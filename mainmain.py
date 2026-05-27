import json
import csv
import os
import re
import time
from pydantic import ValidationError
from json_schema import OCLDocument, OCLConstraint
from Z3_verification import evaluate_constraint, check_z3_translatable
from utils import call_llm_structured
from config import MAX_RETRIES
from semantic_firewall import MetamodelRegistry, TypeEnvironment, OCLSemanticChecker, SemanticError

SYSTEM_INSTRUCTION = """
You are a formal methods expert and a strict OCL AST compiler. Your task is to translate natural language specifications into a strictly structured OCL Abstract Syntax Tree (AST) based on the provided UML metamodel.

CRITICAL RULES:

1. SCHEMA STRICTNESS: You MUST output a valid JSON matching the exact Pydantic schema provided.

2. UML MULTIPLICITY, NAVIGATION SYNTAX & VERIFICATION SEMANTICS: You MUST strictly interpret multiplicity annotations to determine navigation syntax, typing, and null-safety:
- Single Object Navigation (Dot syntax `.`):
  * Applies to Mandatory `[1..1]` and Optional `[0..1]` associations.
  * MUST use dot syntax (`.`) for access (e.g., `self.plane.capacity`).
  * Null Safety:
    - `[1..1]`: Existence is mathematically guaranteed. NEVER use `.isDefined()`.
    - `[0..1]`: MUST guard against nulls. For boolean constraints, use `self.assoc.isDefined() implies ...`. For arithmetic defaults, use IfExpressions (e.g., `if self.assoc.isDefined() then ... else 0 endif`). Direct property access without a guard is strictly forbidden.
  * WRONG: self.plane->size() (plane is not a collection)
  * WRONG: self.manager->isDefined() (optional single object uses dot)

- Collection Navigation (Arrow syntax `->`):
  * Applies ONLY to supported Collection types (`Set` and `Bag` — e.g., `Set(Employee)`). 
  * VERIFICATION SEMANTICS: All collections are verified under unordered multiset semantics. `Sequence` and `OrderedSet` are NOT part of the verification subset and MUST NOT be generated.
  * MUST use arrow syntax (`->`) for all operations (e.g., `->size()`, `->isEmpty()`).
  * Implicit Collect: `self.staff.salary` returns a collection. Subsequent operations MUST use arrow syntax (e.g., `self.staff.salary->sum()`).
  * Null Safety: NEVER use `.isDefined()` on a collection. Use `->notEmpty()` instead.
  * Type Matching: NEVER compare a Collection directly with a Scalar. Always aggregate first (e.g., `->size() > 0`).
  * Numeric Aggregation: `->sum()` requires a collection of numeric values (Integer or Real). WRONG: `self.staff->collect(s | s.company)->sum()`; CORRECT: `self.staff.salary->sum()`.

3. EXPLICIT ITERATORS ONLY: You MUST NOT use implicit shorthand for iterators. Every supported IteratorExpression (specifically `forAll`, `exists`, `select`, `reject`, `collect`, `isUnique`) MUST explicitly declare its `iterator_variables`.
   WRONG: self.cells->isUnique(value)
   CORRECT: self.cells->isUnique(c | c.value)

4. OPERATION ENCODING: Strictly differentiate between OCL standard operations and collection operations.
- Collection Operations (arrow syntax ->op): ->size(), ->sum(), ->isEmpty(), ->notEmpty(), ->includes(), ->excludes(), ->count(), ->asSet(), ->asBag(), ->flatten(), MUST use the `CollectionOperation` node.
  * DETERMINISM CONSTRAINT: This verification subset strictly enforces deterministic, unordered semantics. Operations relying on non-deterministic selection (such as ->any(), ->first(), ->last()) or sequential ordering (such as ->at(), ->indexOf(), ->subSequence()) are structurally excluded and MUST NOT be generated. To inspect collection elements, always use deterministic explicit iterators (e.g., ->forAll, ->exists).
- Standard Operations (dot syntax .op): MUST use the `OperationCall` node.
  * Class-level: ClassName.allInstances() → "source": {"type": "Variable", "name": "ClassName"}, "operation_name": "allInstances"
  * Null checks: self.x.isDefined() or self.x.oclIsUndefined() → "operation_name": "isDefined" / "oclIsUndefined"
  * Math: abs() → "operation_name": "abs"
"""

# 2. 构造测试 Prompt（包含上下文和需求）
def build_dynamic_prompt(model_name: str, uml_context: dict, constraint_name: str, nl_req: str) -> str:
    """动态拼装当前测试用例的上下文和需求"""

    # 将 UML 字典转化为格式化的字符串
    context_str = json.dumps(uml_context, indent=2)

    return f"""
【Metamodel Context (Model: {model_name})】
{context_str}

【Target Constraint: {constraint_name}】
Natural Language Specification:
{nl_req}

Please generate the corresponding OCL AST in valid JSON format.
"""

def sanitize_filename(name: str) -> str:
    """清理字符串，使其成为合法且安全的文件名"""
    # 将空格替换为下划线，移除所有非字母数字下划线的字符
    clean_name = re.sub(r'[^a-zA-Z0-9_]', '_', name.replace(' ', '_'))
    return re.sub(r'_+', '_', clean_name) # 合并连续的下划线


def generate_ast_with_reflexion(case_key: str, context_class: str, initial_prompt: str, gt_ast_data: dict,
                                uml_context: dict) -> tuple[OCLDocument, dict]:
    current_prompt = initial_prompt
    attempt = 0
    max_transient_retries = 30
    transient_count = 0
    z3_reflexion_round = 0
    max_z3_reflexion_rounds = 3

    while attempt < MAX_RETRIES:
        attempt += 1
        print(f"\n🔄 [第 {attempt}/{MAX_RETRIES} 次尝试] 正在呼叫大模型生成 AST...")

        try:
            raw_json_response = call_llm_structured(
                prompt=current_prompt,
                system_instruction=SYSTEM_INSTRUCTION,
                response_schema=OCLDocument
            )

            try:
                parsed_ast = json.loads(raw_json_response)
            except json.JSONDecodeError as json_err:
                print(f"⚠️ 语法拦截: JSON 解析失败！错误坐标: {json_err}")
                current_prompt += (
                    f"\n\n【SYSTEM FEEDBACK】\n"
                    f"Your previous output was NOT valid JSON. Fix it. Error: {json_err}\n"
                    f"Previous Output:\n{raw_json_response}"
                )
                continue

            validated_doc = OCLDocument(**parsed_ast)
            print("✅ Pydantic 深度校验通过！结构完美。")

            # === 防御性检查：确保至少生成了一个约束 ===
            if not validated_doc.constraints:
                raise ValueError("LLM generated an empty constraints list. At least one constraint is required.")

            # 统一提取主约束（与后续 evaluate_constraint 取 [0] 的逻辑对齐）
            target_constraint = validated_doc.constraints[0]

            print("🛡️ 开始进行 AST 语义图结构校验...")
            env = TypeEnvironment(case_key=case_key, context_class=context_class, registry=registry)
            OCLSemanticChecker.check(target_constraint.expression, env)
            print("✅ 语义校验通过！AST 逻辑无懈可击。")

            # === 第二道防线：Z3 可编译性校验 ===
            print("🛡️ 开始进行 Z3 可编译性校验...", flush=True)
            is_z3_ok, z3_error = check_z3_translatable(
                target_constraint.expression, env.uml_context, context_class
            )
            if not is_z3_ok:
                raise ValueError(f"Z3 Compilation Error: {z3_error}")

            print("✅ Z3 编译校验通过！AST 结构完全可形式化。")

            # === 第三道防线：Z3 等价性校验与反例驱动自愈 (CEGAR) ===
            print("⚖️ 开始进行 Z3 语义等价性评估...", flush=True)
            gt_constraint = OCLConstraint(**gt_ast_data)
            gt_expr = gt_constraint.expression
            llm_expr = validated_doc.constraints[0].expression

            try:
                eq_result = evaluate_constraint(
                    gt_ast=gt_expr,
                    llm_ast=llm_expr,
                    uml_context=uml_context,
                    context_class=context_class
                )
            except Exception as eval_err:
                # 如果等价性评估期间发生Z3内部异常，当作编译错误处理
                raise ValueError(f"Z3 Evaluation Exception: {str(eval_err)}")

            if eq_result["result"] == "EQUIVALENT":
                print("✅ Z3 判定：语义完全等价！")
                return validated_doc, eq_result

            # 不等价处理：构造反例反馈
            z3_reflexion_round += 1
            if z3_reflexion_round > max_z3_reflexion_rounds:
                print(f"⚠️ Z3 反例自愈已达最大轮次 ({max_z3_reflexion_rounds})，终止自愈并返回当前最佳结果。")
                return validated_doc, eq_result

            print(f"❌ Z3 判定: {eq_result['result']}，准备第 {z3_reflexion_round} 次反例反馈...")

            feedback_parts = [
                f"\n\n【Z3 FORMAL VERIFICATION REJECTION】",
                f"Your OCL constraint is {eq_result['result']} relative to the ground truth.",
            ]

            if eq_result["result"] == "WEAKENED":
                feedback_parts.append(
                    "Your constraint is TOO PERMISSIVE — it allows a state that the specification rejects."
                )
                if eq_result.get("weakened_counterexample"):
                    feedback_parts.append(
                        f"Counter-example state where your constraint is satisfied but the specification is violated:\n"
                        f"{eq_result['weakened_counterexample']}"
                    )

            elif eq_result["result"] == "STRENGTHENED":
                feedback_parts.append(
                    "Your constraint is TOO RESTRICTIVE — it rejects a state that the specification allows."
                )
                if eq_result.get("strengthened_counterexample"):
                    feedback_parts.append(
                        f"Counter-example state where the specification is satisfied but your constraint rejects it:\n"
                        f"{eq_result['strengthened_counterexample']}"
                    )

            elif eq_result["result"] == "INCOMPARABLE":
                feedback_parts.append(
                    "Your constraint and the specification are logically incomparable (cross-implication failure)."
                )
                if eq_result.get("weakened_counterexample"):
                    feedback_parts.append(
                        f"State where your constraint is too permissive:\n{eq_result['weakened_counterexample']}"
                    )
                if eq_result.get("strengthened_counterexample"):
                    feedback_parts.append(
                        f"State where your constraint is too restrictive:\n{eq_result['strengthened_counterexample']}"
                    )

            feedback_parts.append(
                "Please revise your OCL AST to match the exact semantics of the specification."
            )

            current_prompt += "\n".join(feedback_parts)
            continue

        except ValidationError as pydantic_err:
            print(f"❌ Schema 校验失败，触发自愈合机制...")
            error_details = str(pydantic_err)
            current_prompt += (
                f"\n\n【CRITICAL SYSTEM FEEDBACK】\n"
                f"Your previous JSON output failed the Pydantic Schema validation. "
                f"You MUST fix the specific fields mentioned in the error below:\n"
                f"text\n{error_details}\n```\n"
                f"Do NOT change the correct parts, only fix the structural errors."
                )
        except SemanticError as semantic_err:
            print(f"❌ 语义防火墙拦截: {semantic_err}")
            current_prompt += (
                f"\n\n【SEMANTIC FIREWALL REJECTION】\n"
                f"Your OCL AST has a strict typing/semantic error based on the UML metamodel:\n"
                f"🚨 ERROR: {semantic_err}\n"
                f"Please fix the logic and output the revised JSON. "
                f"Pay close attention to scalar vs. collection operations, "
                f"and ensure all attributes/associations exist in the UML context."
            )

            # === 捕获 Z3 编译错误 ===
        except ValueError as z3_err:
            err_str = str(z3_err)
            # 统一拦截：无论是主动抛出的 ValueError 还是 check 函数抛出的异常
            if "Scalar/Collection mismatch" in err_str or "Z3 Compilation Error" in err_str or "Z3 Internal Exception" in err_str or "Z3 Evaluation Exception" in err_str:
                print(f"❌ Z3 编译防火墙拦截: {err_str}")

                current_prompt += (
                    f"\n\n【Z3 COMPILATION FIREWALL REJECTION】\n"
                    f"Your OCL AST could not be compiled for formal verification:\n"
                    f"🚨 ERROR: {err_str}\n"
                    f"Please review the UML metamodel multiplicities and your AST structure, "
                    f"ensuring dot (.) is used for single objects and arrow (->) for collections."
                )

            else:
                raise z3_err

        except Exception as api_err:
            err_str = str(api_err).lower()
            is_transient = any(
                str(code) in err_str for code in {429, 500, 502, 503, 504}
            ) or any(
                kw in err_str for kw in [
                    "high demand", "overloaded", "rate limit",
                    "temporarily", "try again"
                ]
            )

            if is_transient and transient_count < max_transient_retries:
                transient_count += 1
                wait = min(5 * transient_count, 30)
                print(f"⏳ [API 瞬时错误 x{transient_count}] "
                      f"不消耗重试次数，{wait}s 后重试... ({api_err})")
                time.sleep(wait)
                attempt -= 1
            else:
                print(f"📡 API 永久性异常 (或瞬时错误超限): {api_err}")
                raise api_err

    raise RuntimeError(
            f"🚨 自愈合失败：在 {MAX_RETRIES} 次尝试后，"
            f"大模型依然无法生成合法的 AST。"
        )



registry = MetamodelRegistry("benchmark_v5.json")


def main():
    print("🚀 启动 OCL AST 批量生成与验证流水线...")
    output_dir = "results"
    error_log_file = os.path.join(output_dir, "failed_cases.txt")
    summary_path = os.path.join(output_dir, "evaluation_summary.csv")
    os.makedirs(output_dir, exist_ok=True)

    summary_records = []

    for case_key, case_data in registry.data.items():
        model_name = case_data.get("Model_Name", "UnknownModel")
        uml_context = case_data.get("UML_Context", {})
        constraints = case_data.get("Constraints", {})

        print(f"\n========== 开始处理模型: {model_name} ({case_key}) ==========")

        for constraint_name, constraint_info in constraints.items():
            nl_req = constraint_info.get("Input_NL_Requirement", "")
            if not nl_req.strip():
                print(f"⚠️ 跳过 {constraint_name}: 暂无 NL 需求")
                continue

            gt_ast_data = constraint_info.get("Ground_Truth_AST")
            if not gt_ast_data:
                print(f"⚠️ 跳过 {constraint_name}: 缺少 Ground_Truth_AST")
                continue

            safe_model = sanitize_filename(model_name)
            safe_constraint = sanitize_filename(constraint_name)
            ast_path = os.path.join(output_dir, f"{safe_model}_{safe_constraint}.json")

            llm_ast_doc = None
            cached_eq_result = None

            # ================= 步骤 1: 加载缓存或生成 AST =================
            if os.path.exists(ast_path):
                print(f"⏭️ 发现已有结果文件 [{constraint_name}]，直接加载。")
                try:
                    with open(ast_path, "r", encoding="utf-8") as f:
                        cached_data = json.load(f)
                        llm_ast_doc = OCLDocument(**cached_data.get("ast", cached_data))
                        cached_eq_result = cached_data.get("verification_result")
                except Exception as load_err:
                    print(f"⚠️ 文件损坏，将重新生成: {load_err}")
                    llm_ast_doc = None
                    cached_eq_result = None

            if not llm_ast_doc:
                initial_prompt = build_dynamic_prompt(model_name, uml_context, constraint_name, nl_req)
                context_class = gt_ast_data.get("context_class", constraint_name.split('_')[0])

                print(f"\n▶️ 正在生成并校验约束: [{constraint_name}]")
                try:
                    llm_ast_doc, eq_result_cached = generate_ast_with_reflexion(
                        case_key=case_key,
                        context_class=context_class,
                        initial_prompt=initial_prompt,
                        gt_ast_data=gt_ast_data,
                        uml_context=uml_context
                    )

                    # 合并落盘
                    output_data = {
                        "verification_result": eq_result_cached,
                        "ast": json.loads(llm_ast_doc.model_dump_json())
                    }
                    with open(ast_path, "w", encoding="utf-8") as f:
                        json.dump(output_data, f, indent=2, ensure_ascii=False)# type: ignore[arg-type]

                    cached_eq_result = eq_result_cached
                    print(f"✅ [{constraint_name}] 结果成功入库。")

                except Exception as e:
                    print(f"🚨 放弃生成 [{constraint_name}]: {e}")
                    with open(error_log_file, "a", encoding="utf-8") as f:
                        f.write(f"[{model_name}] {constraint_name} - 生成失败: {str(e)}\n")

                    summary_records.append({
                        "case_key": case_key,
                        "constraint_name": constraint_name,
                        "result": "GENERATION_FAILED",
                        "score": 0.0
                    })
                    continue

            # ================= 步骤 2: 汇总数据 =================
            if cached_eq_result:
                summary_records.append({
                    "case_key": case_key,
                    "constraint_name": constraint_name,
                    "result": cached_eq_result.get("result", "UNKNOWN"),
                    "score": cached_eq_result.get("score", 0.0)
                })

    # ================= 步骤 3: 写入汇总 CSV 并计算平均分 =================
    if summary_records:
        with open(summary_path, "w", encoding="utf-8", newline="") as f:
            writer = csv.DictWriter(f, fieldnames=["case_key", "constraint_name", "result", "score"])# type: ignore[arg-type]
            writer.writeheader()
            writer.writerows(summary_records)

        valid_scores = [r["score"] for r in summary_records if isinstance(r["score"], (int, float))]
        avg_score = sum(valid_scores) / len(valid_scores) if valid_scores else 0.0

        with open(summary_path, "a", encoding="utf-8", newline="") as f:
            f.write(f"\nAVERAGE_SCORE,,,{avg_score:.2f}\n")

        print(f"\n📊 评估完成！汇总表已写入: {summary_path}")
        print(f"📈 全局平均得分: {avg_score:.2f}")
    else:
        print("\n⚠️ 未收集到任何评估数据。")

if __name__ == "__main__":
    main()
