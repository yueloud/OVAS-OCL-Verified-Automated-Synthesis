import json
import os
import re
import time
from pydantic import ValidationError
from json_schema import OCLDocument, OCLConstraint
from Z3_verification import evaluate_constraint, check_z3_translatable


from utils import call_llm_structured
from config import MAX_RETRIES
from semantic_firewall import MetamodelRegistry, TypeEnvironment, OCLSemanticChecker, SemanticError

# 1. 极其严谨的系统指令（定调）
SYSTEM_INSTRUCTION = """
You are a formal methods expert and a strict OCL AST compiler. Your task is to translate natural language specifications into a strictly structured OCL Abstract Syntax Tree (AST) based on the provided UML metamodel.

CRITICAL RULES:
1. SCHEMA STRICTNESS: You MUST output a valid JSON matching the exact Pydantic schema provided.

2. UML FIDELITY, MULTIPLICITY & TYPE MATCHING: ONLY use properties defined in the Metamodel. You MUST strictly interpret multiplicity annotations to determine navigation and typing:
- Set/Sequence/Bag (e.g., `Set(Employee)`): Represents a collection. 
  * MUST use arrow syntax (`->`) for operations (e.g., `->size()`, `->isEmpty()`).
  * Implicit collect is allowed (`self.employees.salary` returns a Bag), but subsequent operations MUST use arrow syntax (`->sum()`).
  * NEVER use `.isDefined()` on a collection. Use `->notEmpty()` instead.
  * TYPE MATCHING: NEVER compare a Collection directly with a Scalar. Always aggregate first (e.g., `->size() > 0`).
- Mandatory Single Value (e.g., `Dept[1..1]`): 
  * MUST use dot syntax (`.`).
  * NEVER use `.isDefined()` — existence is mathematically guaranteed.
- Optional Single Value (e.g., `Employee[0..1]`): 
  * MUST use dot syntax (`.`).
  * MUST guard against nulls. For boolean constraints, use `self.assoc.isDefined() implies ...`. For arithmetic defaults, use IfExpressions (e.g., `if self.assoc.isDefined() then ... else 0 endif`).
  * Direct property access without a guard is strictly forbidden.

3. EXPLICIT ITERATORS ONLY: You MUST NOT use implicit shorthand for iterators. Every IteratorExpression (like forAll, exists, select, isUnique, collect, any, one) MUST explicitly declare its `iterator_variables`.
WRONG: self.cells->isUnique(value)
CORRECT: self.cells->isUnique(c | c.value)

4. OPERATION ENCODING: Strictly differentiate between OCL standard operations and collection operations.
- Collection Operations (arrow syntax ->op): ->size(), ->sum(), ->isEmpty(), ->includes(), ->at(), etc., MUST use the `CollectionOperation` node.
- Standard Operations (dot syntax .op): MUST use the `OperationCall` node.
  * Class-level: ClassName.allInstances() → "source": {"type": "Variable", "name": "ClassName"}, "operation_name": "allInstances"
  * Null checks: self.x.isDefined() or self.x.oclIsUndefined() → "operation_name": "isDefined" / "oclIsUndefined" (DO NOT use PropertyCall for these)
  * Math: abs() → "operation_name": "abs"
  * Type checks: self.x.oclIsKindOf(Type) → "operation_name": "oclIsKindOf"
- Type Casts: obj.oclAsType(TargetClass) MUST use the `TypeCast` node with "target_type": "TargetClass". Do NOT encode the target class as an argument.

5. OCL NAVIGATION SYNTAX RULES (Dot vs Arrow):
You MUST correctly match navigation syntax to the multiplicity of the property:
- Dot syntax (.) is for SINGLE OBJECTS (Mandatory `[1..1]` or Optional `[0..1]`).
  * CORRECT: self.plane.capacity (where plane is Plane[1..1])
  * WRONG: self.plane->size() (plane is not a collection)
- Arrow syntax (->) is for COLLECTIONS (Set, Bag, Sequence, OrderedSet).
  * CORRECT: self.staff->size() (where staff is Set(Employee))
  * WRONG: self.staff.size() (staff is a collection, not a single object)
- Implicit Collect (self.staff.salary) returns a COLLECTION. Use -> for subsequent operations.
  * CORRECT: self.staff.salary->sum()
- ->sum() requires a collection of numeric values (Integer or Real).
  * WRONG: self.staff->collect(s | s.company)->sum() (Company is not a number)
  * CORRECT: self.staff->collect(s | s.salary)->sum() (Real is a number)
  * ALSO CORRECT: self.staff.salary->sum() (implicit collect, preferred when simpler)
- Optional values ([0..1]) MUST use dot syntax, and SHOULD guard against nulls.
  * WRONG: self.manager->isDefined()
  * CORRECT: self.manager.isDefined()
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

def generate_ast_with_reflexion(case_key: str, context_class: str, initial_prompt: str) -> OCLDocument:
    current_prompt = initial_prompt
    attempt = 0
    max_transient_retries = 30
    transient_count = 0

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

            print("🛡️ 开始进行 AST 语义图结构校验...")
            env = TypeEnvironment(case_key=case_key, context_class=context_class, registry=registry)
            for constraint in validated_doc.constraints:
                OCLSemanticChecker.check(constraint.expression, env)
            print("✅ 语义校验通过！AST 逻辑无懈可击。")

            # === 新增：第三道防线 - Z3 可编译性校验 ===
            print("🛡️ 开始进行 Z3 可编译性校验...")
            is_z3_ok, z3_error = check_z3_translatable(
                constraint.expression, env.uml_context, context_class
            )
            if not is_z3_ok:
                raise ValueError(f"Z3 Compilation Error: {z3_error}")

            print("✅ Z3 编译校验通过！AST 结构完全可形式化。")

            return validated_doc

        except ValidationError as pydantic_err:
            print(f"❌ Schema 校验失败，触发自愈合机制...")
            error_details = str(pydantic_err)
            current_prompt += (
                f"\n\n【CRITICAL SYSTEM FEEDBACK】\n"
                f"Your previous JSON output failed the Pydantic Schema validation. "
                f"You MUST fix the specific fields mentioned in the error below:\n"
                f"```text\n{error_details}\n```\n"
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
            if "Scalar/Collection mismatch" in err_str or "Z3 Compilation Error" in err_str or "Z3 Internal Exception" in err_str:
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
    error_log_file = "failed_cases.txt"
    os.makedirs(output_dir, exist_ok=True)

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

            # 获取 Ground Truth
            gt_ast_data = constraint_info.get("Ground_Truth_AST")
            if not gt_ast_data:
                print(f"⚠️ 跳过 {constraint_name}: 缺少 Ground_Truth_AST")
                continue

            # 安全的文件路径构造
            safe_model = sanitize_filename(model_name)
            safe_constraint = sanitize_filename(constraint_name)
            ast_path = os.path.join(output_dir, f"{safe_model}_{safe_constraint}.json")
            score_path = os.path.join(output_dir, f"{safe_model}_{safe_constraint}_score.json")

            # ================= 步骤 1: 获取 LLM 生成的 AST =================
            llm_ast_doc = None
            if os.path.exists(ast_path):
                print(f"⏭️ 发现已有 AST 文件 [{constraint_name}]，直接加载。")
                try:
                    with open(ast_path, "r", encoding="utf-8") as f:
                        llm_ast_doc = OCLDocument(**json.load(f))
                except Exception as load_err:
                    print(f"⚠️ AST 文件损坏，将重新生成: {load_err}")
                    llm_ast_doc = None

            if not llm_ast_doc:
                initial_prompt = build_dynamic_prompt(model_name, uml_context, constraint_name, nl_req)
                # 健壮提取：直接从 GT 中获取 context_class，而非硬编码解析约束名
                context_class = gt_ast_data.get("context_class", constraint_name.split('_')[0])

                print(f"\n▶️ 正在生成并校验约束: [{constraint_name}]")
                try:
                    llm_ast_doc = generate_ast_with_reflexion(
                        case_key=case_key,
                        context_class=context_class,
                        initial_prompt=initial_prompt
                    )
                    # 稳健的落盘保存
                    with open(ast_path, "w", encoding="utf-8") as f:
                        f.write(llm_ast_doc.model_dump_json(indent=2))
                    print(f"✅ [{constraint_name}] AST 成功入库。")
                except Exception as e:
                    print(f"🚨 放弃生成 [{constraint_name}]: {e}")
                    with open(error_log_file, "a", encoding="utf-8") as f:
                        f.write(f"[{model_name}] {constraint_name} - 生成失败: {str(e)}\n")
                    continue  # 生成失败，直接跳过后续评估

            # ================= 步骤 2: Z3 语义等价性评估 =================
            if os.path.exists(score_path):
                print(f"⏭️ 发现已有分数文件 [{constraint_name}]，跳过评估。")
                continue

            print(f"⚖️ [{constraint_name}] 开始 Z3 语义等价性评估...")
            try:
                gt_constraint = OCLConstraint(**gt_ast_data)
                gt_expr = gt_constraint.expression
                llm_expr = llm_ast_doc.constraints[0].expression

                score = evaluate_constraint(
                    gt_ast=gt_expr,
                    llm_ast=llm_expr,
                    uml_context=uml_context,
                    context_class=gt_constraint.context_class
                )
                print(f"🎯 [{constraint_name}] Z3 语义相似度得分: {score}")

                # 保存分数详情
                score_data = {
                    "case_key": case_key,
                    "model_name": model_name,
                    "constraint_name": constraint_name,
                    "score": score
                }
                with open(score_path, "w", encoding="utf-8") as f:
                    json.dump(score_data, f, indent=2)
            except Exception as z3_err:
                print(f"🚨 [{constraint_name}] Z3 评估失败: {z3_err}")
                with open(error_log_file, "a", encoding="utf-8") as f:
                    f.write(f"[{model_name}] {constraint_name} - Z3评估失败: {str(z3_err)}\n")


if __name__ == "__main__":
    main()
