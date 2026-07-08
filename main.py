import json
import csv
import os
import re
import time
from pydantic import ValidationError
from json_schema import OCLDocument, OCLConstraint, build_schema_variant
from Z3_verification import evaluate_constraint, check_z3_translatable
from utils import call_llm_structured
from config import MAX_RETRIES, AblationSwitch, Dict2Obj
from semantic_checker import DomainModelRegistry, TypeEnvironment, OCLSemanticChecker, SemanticError

SYSTEM_INSTRUCTION_FULL = """
You are a formal methods expert and a strict OCL AST compiler. Your task is to translate natural language requirements into a strictly structured OCL Abstract Syntax Tree (AST) based on the provided UML structural context.

CRITICAL RULES:

1. SCHEMA STRICTNESS: You MUST output a valid JSON matching the exact Pydantic schema provided.

2. UML MULTIPLICITY, NAVIGATION SYNTAX & VERIFICATION SEMANTICS: You MUST strictly interpret multiplicity annotations to determine navigation syntax, typing, and null-safety:
- Single Object Navigation (Dot syntax `.`):
  * Applies to Mandatory `[1..1]` and Optional `[0..1]` associations.
  * MUST use dot syntax (`.`) for access (e.g., `self.plane.capacity`).
  * Null Safety:
    - `[1..1]`: Existence is mathematically guaranteed. NEVER use `.oclIsUndefined()`.
    - `[0..1]`: MUST guard against nulls. For boolean constraints, use `not self.assoc.oclIsUndefined() implies ...`. For arithmetic defaults, use IfExpressions (e.g., `if not self.assoc.oclIsUndefined() then ... else 0 endif`). Direct property access without a guard is strictly forbidden.
  * WRONG: self.plane->size() (plane is not a collection)
  * WRONG: self.manager->oclIsUndefined() (optional single object uses dot)

- Collection Navigation (Arrow syntax `->`):
  * Applies ONLY to supported Collection types (`Set` and `Bag` — e.g., `Set(Employee)`).
  * VERIFICATION SEMANTICS: All collections are verified under unordered multiset semantics. `Sequence` and `OrderedSet` are NOT part of the verification subset and MUST NOT be generated.
  * MUST use arrow syntax (`->`) for all operations (e.g., `->size()`, `->isEmpty()`).
  * Implicit Collect: `self.staff.salary` returns a collection. Subsequent operations MUST use arrow syntax (e.g., `self.staff.salary->sum()`).
  * Null Safety: NEVER use `.oclIsUndefined()` on a collection. Use `->notEmpty()` instead.
  * Type Matching: NEVER compare a Collection directly with a Scalar. Always aggregate first (e.g., `->size() > 0`).
  * Numeric Aggregation: `->sum()` requires a collection of numeric values (Integer or Real). WRONG: `self.staff->collect(s | s.company)->sum()`; CORRECT: `self.staff.salary->sum()`.

3. EXPLICIT ITERATORS ONLY: You MUST NOT use implicit shorthand for iterators. Every supported IteratorExpression (specifically `forAll`, `exists`, `select`, `reject`, `collect`, `isUnique`) MUST explicitly declare its `iterator_variables`.
   WRONG: self.cells->isUnique(value)
   CORRECT: self.cells->isUnique(c | c.value)

4. OPERATION ENCODING: Strictly differentiate between OCL standard operations and collection operations.
- Collection Operations (arrow syntax ->op): ->size(), ->sum(), ->isEmpty(), ->notEmpty(), ->includes(), ->excludes(), ->count(), ->asSet(), ->asBag(), MUST use the `CollectionOperation` node.
  * DETERMINISM CONSTRAINT: This verification subset strictly enforces deterministic, unordered semantics. Operations relying on non-deterministic selection (such as ->any(), ->first(), ->last()) or sequential ordering (such as ->at(), ->indexOf(), ->subSequence()) are structurally excluded and MUST NOT be generated. To inspect collection elements, always use deterministic explicit iterators (e.g., ->forAll, ->exists).
- Standard Operations (dot syntax .op): MUST use the `OperationCall` node.
  * Null checks: self.x.oclIsUndefined() → "operation_name": "oclIsUndefined"
  * Math: abs() → "operation_name": "abs"

5. Decidable OCL Subset
This verification pipeline operates on a decidable OCL subset. You MUST NOT generate constructs outside this subset, as they will trigger compilation errors. The supported constructs are strictly defined as follows:

- **Types & Literals**: Integer, Real, Boolean, String, and Null.
- **Logical Operators**: and, or, xor, not, implies.
- **Relational & Arithmetic Operators**: =, <>, <, >, <=, >=, +, -, *, /, abs().
- **Collection Types**: Set and Bag are the ONLY supported collection types. `Sequence` and `OrderedSet` are NOT supported.
- **Iterators**: `forAll`, `exists`, `select`, `reject`, `collect`, `isUnique`.
  * Note: `forAll`, `exists`, and `isUnique` support multi-variable iterator forms (e.g., `forAll(x, y | ...)`).
  * Note: `select`, `reject`, and `collect` are restricted to single-variable forms only to preserve algebraic soundness.
- **Collection Operations**: `size`, `isEmpty`, `notEmpty`, `includes`, `excludes`, `includesAll`, `excludesAll`, `sum`, `count`, `asSet`, `asBag`, `union`, `intersection`.
- **Control Flow**: `if-then-else` expressions and `let-in` expressions.
- **Null Safety**: `oclIsUndefined()` is the ONLY supported null-check operation. Null literal comparisons (e.g., `self.x = null`) are NOT supported.
"""

SYSTEM_INSTRUCTION_MINIMAL = """
You are a formal methods expert and a strict OCL AST compiler. Your task is to translate natural language requirements into a strictly structured OCL Abstract Syntax Tree (AST) based on the provided UML structural context.

You MUST output the result as a single valid raw JSON object. Do not wrap it in markdown code blocks. The JSON should represent a document containing a list of constraints, each with a context class and an expression tree.

CRITICAL RULE:
This verification pipeline operates on a decidable OCL subset. You MUST NOT generate constructs outside this subset, as they will trigger compilation errors. The supported constructs are strictly defined as follows:

- **Types & Literals**: Integer, Real, Boolean, String, and Null.
- **Logical Operators**: and, or, xor, not, implies.
- **Relational & Arithmetic Operators**: =, <>, <, >, <=, >=, +, -, *, /, abs().
- **Collection Types**: Set and Bag are the ONLY supported collection types. `Sequence` and `OrderedSet` are NOT supported.
- **Iterators**: `forAll`, `exists`, `select`, `reject`, `collect`, `isUnique`.
  * Note: `forAll`, `exists`, and `isUnique` support multi-variable iterator forms (e.g., `forAll(x, y | ...)`).
  * Note: `select`, `reject`, and `collect` are restricted to single-variable forms only to preserve algebraic soundness.
- **Collection Operations**: `size`, `isEmpty`, `notEmpty`, `includes`, `excludes`, `includesAll`, `excludesAll`, `sum`, `count`, `asSet`, `asBag`, `union`, `intersection`.
- **Control Flow**: `if-then-else` expressions and `let-in` expressions.
- **Null Safety**: `oclIsUndefined()` is the ONLY supported null-check operation. Null literal comparisons (e.g., `self.x = null`) are NOT supported.
"""


def build_dynamic_prompt(model_name: str, uml_context: dict, constraint_name: str, nl_req: str) -> str:
    context_str = json.dumps(uml_context, indent=2)

    return f"""
[UML structural context (Model: {model_name})]
{context_str}

[Target Constraint: {constraint_name}]
Natural Language Specification:
{nl_req}

Please generate the corresponding OCL AST in valid JSON format.
"""


def sanitize_filename(name: str) -> str:
    clean_name = re.sub(r'[^a-zA-Z0-9_]', '_', name.replace(' ', '_'))
    return re.sub(r'_+', '_', clean_name)


def get_ast_max_depth(node):
    if not isinstance(node, dict):
        return 0

    max_child_depth = 0
    for key, value in node.items():
        if isinstance(value, dict):
            depth = get_ast_max_depth(value)
            if depth > max_child_depth:
                max_child_depth = depth
        elif isinstance(value, list):
            for item in value:
                if isinstance(item, dict):
                    depth = get_ast_max_depth(item)
                    if depth > max_child_depth:
                        max_child_depth = depth

    return 1 + max_child_depth


def generate_ast_with_reflexion(
        case_key: str, context_class: str, constraint_name: str,
        initial_prompt: str, gt_ast_data: dict, uml_context: dict,
        interception_stats: dict = None,
        ablation_config: AblationSwitch = None
) -> tuple[OCLDocument, dict]:
    def _abl_enabled(flag_name: str) -> bool:
        if ablation_config is None:
            return True
        return ablation_config.is_enabled(flag_name)

    current_prompt = initial_prompt
    attempt = 0
    max_transient_retries = 30
    transient_count = 0
    z3_reflexion_round = 0
    max_z3_reflexion_rounds = 3

    schema_variant = "full"
    if ablation_config is not None:
        schema_variant = getattr(ablation_config, 'schema_variant', 'full')
    response_schema = build_schema_variant(schema_variant)

    while attempt < MAX_RETRIES:
        attempt += 1
        print(f"\n Round {attempt}/{MAX_RETRIES} ")

        try:

            system_instruction = SYSTEM_INSTRUCTION_FULL if _abl_enabled(
                "enable_system_instruction") else SYSTEM_INSTRUCTION_MINIMAL

            raw_json_response = call_llm_structured(
                prompt=current_prompt,
                system_instruction=system_instruction,
                response_schema=response_schema,
                ablation_config=ablation_config
            )

            try:
                parsed_ast = json.loads(raw_json_response)

            except json.JSONDecodeError as json_err:

                def repair_json_truncation(json_str: str) -> str:
                    json_str = re.sub(r',\s*$', '', json_str.strip())
                    stack = []
                    pairs = {')': '(', ']': '[', '}': '{'}
                    open_brackets = set('([{')
                    close_brackets = set(')]}')

                    in_string = False
                    escape_char = False
                    for char in json_str:
                        if escape_char:
                            escape_char = False
                            continue
                        if char == '\\':
                            escape_char = True
                            continue
                        if char == '"':
                            in_string = not in_string
                            continue
                        if in_string:
                            continue
                        if char in open_brackets:
                            stack.append(char)
                        elif char in close_brackets:
                            if stack and stack[-1] == pairs[char]:
                                stack.pop()

                    missing = []
                    for char in reversed(stack):
                        if char == '(':
                            missing.append(')')
                        elif char == '[':
                            missing.append(']')
                        elif char == '{':
                            missing.append('}')

                    return json_str + "".join(missing)

                try:
                    fixed_json = repair_json_truncation(raw_json_response)
                    parsed_ast = json.loads(fixed_json)

                except json.JSONDecodeError:

                    if _abl_enabled("enable_layer1_json_schema"):
                        if interception_stats is not None:
                            interception_stats["layer1_json_schema"] += 1
                            interception_stats["layer1_error_types"].add("JSON_PARSE")

                        current_prompt += (
                            f"\n\n[SYSTEM FEEDBACK]\n"
                            f"Your previous output was NOT valid JSON. Fix it. Error: {json_err}\n"
                            f"Previous Output:\n{raw_json_response}"
                        )
                        continue

                    try:

                        import re as _re
                        fixed = _re.sub(r',\s*}', '}', raw_json_response)
                        fixed = _re.sub(r',\s*]', ']', fixed)
                        parsed_ast = json.loads(fixed)
                    except json.JSONDecodeError:
                        raise

            if _abl_enabled("enable_layer1_json_schema"):
                validated_doc = OCLDocument(**parsed_ast)
                print("Structural Check Success")

            else:
                validated_doc = Dict2Obj(parsed_ast)

            if not getattr(validated_doc, "constraints", None):
                raise ValueError("LLM generated an empty constraints list or missing 'constraints' key.")

            target_constraint = validated_doc.constraints[0]

            if _abl_enabled("enable_layer2_semantic"):
                try:
                    env = TypeEnvironment(case_key=case_key, context_class=context_class, registry=registry)
                    OCLSemanticChecker.check(target_constraint.expression, env, ablation_config=ablation_config)
                    print("Type Checking Success")
                except AttributeError as attr_err:
                    raise ValueError(f"Malformed AST structure (missing attribute): {attr_err}")

            else:
                env = TypeEnvironment(case_key=case_key, context_class=context_class, registry=registry)

            if _abl_enabled("enable_layer3_z3_compile"):
                is_z3_ok, z3_error = check_z3_translatable(
                    target_constraint.expression, env.uml_context, context_class,
                    ablation_config=ablation_config
                )
                if not is_z3_ok:
                    raise ValueError(f"Z3 Compilation Error: {z3_error}")

            if _abl_enabled("enable_layer3_z3_equivalence"):
                gt_constraint = OCLConstraint(**gt_ast_data)
                gt_expr = gt_constraint.expression
                llm_expr = validated_doc.constraints[0].expression

                try:
                    eq_result = evaluate_constraint(
                        gt_ast=gt_expr,
                        llm_ast=llm_expr,
                        uml_context=uml_context,
                        context_class=context_class,
                        case_key=case_key,
                        constraint_name=constraint_name,
                        cegar_round=z3_reflexion_round,
                        ablation_config=ablation_config
                    )
                except Exception as eval_err:
                    raise ValueError(f"Z3 Evaluation Exception: {str(eval_err)}")

                if eq_result["result"] == "EQUIVALENT":
                    print("Formal Check: Equivalent")
                    eq_result["z3_correction_round"] = z3_reflexion_round
                    return validated_doc, eq_result

                if eq_result["result"] == "TIMEOUT":
                    print(f"Formal Check: Timeout")
                    return validated_doc, eq_result

                if eq_result["result"] not in ["EQUIVALENT", "TIMEOUT", "ABLATION_SKIPPED"]:
                    if interception_stats is not None:
                        interception_stats["layer3_z3_equivalence"] += 1
                        interception_stats["layer3_eq_results"].add(eq_result["result"])

                if not _abl_enabled("enable_CGSC"):
                    return validated_doc, eq_result

                z3_reflexion_round += 1
                if z3_reflexion_round > max_z3_reflexion_rounds:
                    return validated_doc, eq_result

                print(f"Formal Check: {eq_result['result']}, going to round {z3_reflexion_round} ")

                feedback_parts = [
                    f"\n\n[Z3 FORMAL VERIFICATION REJECTION]",
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
                    feedback_parts.append(
                        "DIAGNOSTIC: Your constraint is strictly weaker than the specification. "
                        "This typically means your guard condition is too permissive or you are missing a constraint entirely."
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
                    feedback_parts.append(
                        "DIAGNOSTIC: Your constraint is strictly stronger than the specification. "
                        "This could be due to: "
                        "1) Missing a conditional guard (implies/if-then) for cases like zero or null. "
                        "2) Using a stricter relational operator (e.g., using > or >= when the spec allows equality). "
                        "Carefully inspect the counter-example state to determine if a boundary value triggered the rejection."
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
                        "DIAGNOSTIC: Your constraint and the specification are incomparable — there exist states where yours is "
                        "too permissive AND states where yours is too restrictive. You likely need to both add missing conditions "
                        "and remove overly restrictive ones."
                    )

                current_prompt += "\n".join(feedback_parts)

                continue
            else:

                eq_result = {
                    "result": "ABLATION_SKIPPED",
                    "weakened_counterexample": None,
                    "strengthened_counterexample": None,
                    "compilation_error": None,
                    "encoding_time_sec": 0.0,
                    "solving_time_sec": 0.0,
                    "total_pipeline_time_sec": 0.0,
                    "timeout_hit": False
                }
                return validated_doc, eq_result

        except ValidationError as pydantic_err:

            if _abl_enabled("enable_layer1_json_schema"):
                if interception_stats is not None:
                    interception_stats["layer1_json_schema"] += 1
                    interception_stats["layer1_error_types"].add("PYDANTIC_SCHEMA")
                print(f"Structural Check failed")
                error_details = str(pydantic_err)
                current_prompt += (
                    f"\n\n[CRITICAL SYSTEM FEEDBACK]\n"
                    f"Your previous JSON output failed the Pydantic Schema validation. "
                    f"You MUST fix the specific fields mentioned in the error below:\n"
                    f"text\n{error_details}\n```\n"
                    f"Do NOT change the correct parts, only fix the structural errors."
                )
            else:
                raise

        except SemanticError as semantic_err:

            if _abl_enabled("enable_layer2_semantic"):
                if interception_stats is not None:
                    interception_stats["layer2_semantic"] += 1
                    interception_stats["layer2_error_types"].add(
                        str(semantic_err)[:50]
                    )
                print(f"Type Checking failed: {semantic_err}")
                current_prompt += (
                    f"\n\n[SEMANTIC FIREWALL REJECTION]\n"
                    f"Your OCL AST has a strict typing/semantic error based on the UML structural context:\n"
                    f" ERROR: {semantic_err}\n"
                    f"Please fix the logic and output the revised JSON. "
                    f"Pay close attention to scalar vs. collection operations, "
                    f"and ensure all attributes/associations exist in the UML context."
                )
            else:
                raise


        except ValueError as z3_err:
            err_str = str(z3_err)
            z3_compile_keywords = [
                "Z3 Compilation Error",
                "Scalar/Collection mismatch",
                "Z3 Internal Exception",
                "Z3 Evaluation Exception"
            ]
            if any(kw in err_str for kw in z3_compile_keywords):

                if _abl_enabled("enable_layer3_z3_compile"):
                    if interception_stats is not None:
                        interception_stats["layer3_z3_compile"] += 1
                        interception_stats["layer3_compile_error_types"].add(err_str[:50])
                    print(f"SMT compile failed: {err_str}")
                    try:

                        if 'parsed_ast' in locals():
                            print(json.dumps(parsed_ast, indent=2, ensure_ascii=False))
                    except Exception as e:
                        raise

                    if "Operation not implemented" in err_str:
                        import re as _re
                        match = _re.search(r"Operation not implemented: (\w+)", err_str)
                        unsupported_op = match.group(1) if match else "unknown"

                        feedback_text = (
                            f"\n\n[UNSUPPORTED OPERATION ERROR]\n"
                            f"Your AST uses operation '{unsupported_op}', which is NOT part of the supported verification subset.\n"
                            f" MANDATORY FIX: Remove '{unsupported_op}' and use supported alternatives.\n"
                            f"For null checks, use 'oclIsUndefined()' instead of 'isDefined'.\n"
                            f"Review the VERIFICATION SUBSET definition in the System Instruction.\n"
                            f"error: {err_str}"
                        )
                    else:
                        feedback_text = (
                            f"\n\n[Z3 COMPILATION REJECTION]\n"
                            f"Your OCL AST could not be compiled for formal verification:\n"
                            f" ERROR: {err_str}\n"
                            f"Please review the UML structural context multiplicities and your AST structure, "
                            f"ensuring dot (.) is used for single objects and arrow (->) for collections."
                        )

                    current_prompt += feedback_text
                    continue

                else:
                    raise
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
                time.sleep(wait)
                attempt -= 1
            else:
                print(f"{api_err}")
                raise api_err

    raise RuntimeError(
        f"Generation failed"
    )


registry = DomainModelRegistry("benchmark.json")


def main(ablation_config: AblationSwitch = None):
    if ablation_config is None:
        ablation_config = AblationSwitch()

    preset_name = ablation_config._meta.get("preset", "custom")
    output_dir = f"results_{preset_name}"
    error_log_file = os.path.join(output_dir, "failed_cases.txt")
    summary_path = os.path.join(output_dir, "evaluation_summary.csv")
    os.makedirs(output_dir, exist_ok=True)

    ablation_config.to_json(os.path.join(output_dir, "ablation_config.json"))

    summary_records = []

    interception_stats = {
        "layer1_json_schema": 0,
        "layer1_error_types": set(),
        "layer2_semantic": 0,
        "layer2_error_types": set(),
        "layer3_z3_compile": 0,
        "layer3_compile_error_types": set(),
        "layer3_z3_equivalence": 0,
        "layer3_eq_results": set(),
    }

    for case_key, case_data in registry.data.items():
        model_name = case_data.get("Model_Name", "UnknownModel")
        uml_context = case_data.get("UML_Context", {})
        constraints = case_data.get("Constraints", {})

        print(f"\n========== Model: {model_name} ({case_key}) ==========")

        for constraint_name, constraint_info in constraints.items():
            complexity_cat = constraint_info.get("Complexity_Category", "Unknown")
            nl_req = constraint_info.get("Input_NL_Requirement", "")
            if not nl_req.strip():
                print(f" Skip {constraint_name}: Can't find this constraint.")
                continue

            gt_ast_data = constraint_info.get("Ground_Truth_AST")
            if not gt_ast_data:
                continue

            ast_depth = get_ast_max_depth(gt_ast_data.get("expression", {}))
            safe_model = sanitize_filename(model_name)
            safe_constraint = sanitize_filename(constraint_name)
            ast_path = os.path.join(output_dir, f"{safe_model}_{safe_constraint}.json")

            llm_ast_doc = None
            cached_eq_result = None

            if os.path.exists(ast_path):
                print(f"Find exist file {constraint_name}, skip the generation")
                try:
                    with open(ast_path, "r", encoding="utf-8") as f:
                        cached_data = json.load(f)
                        llm_ast_doc = OCLDocument(**cached_data.get("ast", cached_data))
                        cached_eq_result = cached_data.get("verification_result")
                except Exception as load_err:
                    llm_ast_doc = None
                    cached_eq_result = None

            if not llm_ast_doc:
                initial_prompt = build_dynamic_prompt(model_name, uml_context, constraint_name, nl_req)
                context_class = gt_ast_data.get("context_class", constraint_name.split('_')[0])

                print(f"\nGenerating: {constraint_name}")
                try:
                    llm_ast_doc, eq_result_cached = generate_ast_with_reflexion(
                        case_key=case_key,
                        context_class=context_class,
                        constraint_name=constraint_name,
                        initial_prompt=initial_prompt,
                        gt_ast_data=gt_ast_data,
                        uml_context=uml_context,
                        interception_stats=interception_stats,
                        ablation_config=ablation_config
                    )

                    if isinstance(llm_ast_doc, Dict2Obj):
                        ast_dict = llm_ast_doc.to_dict()
                    else:
                        ast_dict = json.loads(llm_ast_doc.model_dump_json())

                    output_data = {
                        "verification_result": eq_result_cached,
                        "ast": ast_dict
                    }
                    with open(ast_path, "w", encoding="utf-8") as f:
                        json.dump(output_data, f, indent=2, ensure_ascii=False)

                    cached_eq_result = eq_result_cached
                    print(f"{constraint_name} Saved")

                except Exception as e:
                    print(f"Generation failed {constraint_name}: {e}")
                    with open(error_log_file, "a", encoding="utf-8") as f:
                        f.write(f"[{model_name}] {constraint_name} - Generation failed: {str(e)}\n")

                    summary_records.append({
                        "case_key": case_key,
                        "constraint_name": constraint_name,
                        "complexity": complexity_cat,
                        "ast_depth": ast_depth,
                        "z3_correction_round": 0,
                        "result": "GENERATION_FAILED",
                        "encoding_time_sec": 0.0,
                        "solving_time_sec": 0.0,
                        "total_pipeline_time_sec": 0.0,
                        "timeout_hit": False
                    })
                    continue

            if cached_eq_result:
                summary_records.append({
                    "case_key": case_key,
                    "constraint_name": constraint_name,
                    "complexity": complexity_cat,
                    "ast_depth": ast_depth,
                    "z3_correction_round": cached_eq_result.get("z3_correction_round", 0),
                    "result": cached_eq_result.get("result", "UNKNOWN"),
                    "encoding_time_sec": cached_eq_result.get("encoding_time_sec", 0.0),
                    "solving_time_sec": cached_eq_result.get("solving_time_sec", 0.0),
                    "total_pipeline_time_sec": cached_eq_result.get("total_pipeline_time_sec", 0.0),
                    "timeout_hit": cached_eq_result.get("timeout_hit", False)
                })

    if summary_records:
        with open(summary_path, "w", encoding="utf-8", newline="") as f:
            writer = csv.DictWriter(f, fieldnames=[
                "case_key", "constraint_name", "complexity", "ast_depth", "z3_correction_round", "result",
                "encoding_time_sec", "solving_time_sec", "total_pipeline_time_sec", "timeout_hit"
            ])
            writer.writeheader()
            writer.writerows(summary_records)

        total_cases = len(summary_records)
        equivalent_cases = sum(1 for r in summary_records if r.get("result") == "EQUIVALENT")
        equivalence_rate = (equivalent_cases / total_cases * 100) if total_cases > 0 else 0.0

        valid_encoding = [r["encoding_time_sec"] for r in summary_records
                          if isinstance(r.get("encoding_time_sec"), (int, float))
                          and r["encoding_time_sec"] > 0]
        valid_solving = [r["solving_time_sec"] for r in summary_records
                         if isinstance(r.get("solving_time_sec"), (int, float))
                         and r["solving_time_sec"] > 0]
        valid_total = [r["total_pipeline_time_sec"] for r in summary_records
                       if isinstance(r.get("total_pipeline_time_sec"), (int, float))
                       and r["total_pipeline_time_sec"] > 0]

        avg_encoding = (sum(valid_encoding) / len(valid_encoding)
                        if valid_encoding else 0.0)
        avg_solving = (sum(valid_solving) / len(valid_solving)
                       if valid_solving else 0.0)
        avg_total = (sum(valid_total) / len(valid_total)
                     if valid_total else 0.0)

        timeout_count = sum(1 for r in summary_records
                            if r.get("timeout_hit", False))

        with open(summary_path, "a", encoding="utf-8", newline="") as f:
            f.write(f"\nEQUIVALENCE_RATE,,,{equivalence_rate:.2f}%\n")
            f.write(f"EQUIVALENT_COUNT,,,{equivalent_cases}/{total_cases}\n")
            f.write(f"AVERAGE_ENCODING_TIME,,,{avg_encoding:.4f}\n")
            f.write(f"AVERAGE_SOLVING_TIME,,,{avg_solving:.4f}\n")
            f.write(f"AVERAGE_TOTAL_TIME,,,{avg_total:.4f}\n")
            f.write(f"TIMEOUT_COUNT,,,{timeout_count}\n")

        print(f"\nFinished. Results are in: {summary_path}")

        serializable_stats = {
            "layer1_json_schema": interception_stats["layer1_json_schema"],
            "layer1_error_types": list(interception_stats["layer1_error_types"]),
            "layer2_semantic": interception_stats["layer2_semantic"],
            "layer2_error_types": list(interception_stats["layer2_error_types"]),
            "layer3_z3_compile": interception_stats["layer3_z3_compile"],
            "layer3_compile_error_types": list(interception_stats["layer3_compile_error_types"]),
            "layer3_z3_equivalence": interception_stats["layer3_z3_equivalence"],
            "layer3_eq_results": list(interception_stats["layer3_eq_results"])
        }
        stats_path = os.path.join(output_dir, "interception_stats.json")
        with open(stats_path, "w", encoding="utf-8") as f:
            json.dump(serializable_stats, f, indent=4, ensure_ascii=False)


if __name__ == "__main__":
    main()

