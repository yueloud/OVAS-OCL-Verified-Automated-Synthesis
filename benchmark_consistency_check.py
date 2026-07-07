import json
import time
import sys
from z3 import *
from Z3_verification import BoundedUMLModelEncoder, OCLZ3Translator
from json_schema import OCLConstraint

Z3_TIMEOUT_MS = 60000

def extract_full_state(model, encoder):
    state = {}
    for class_name, sort in encoder.sorts.items():
        state[class_name] = []
        for i in range(encoder.scope):
            inst = getattr(sort, f'{class_name.lower()}_{i}')
            inst_data = {"id": str(inst), "attributes": {}, "associations": {}}

            cls_info = encoder.uml_context.get(class_name, {})

            for attr_name in cls_info.get("attributes", {}).keys():
                func_key = f"{class_name}.{attr_name}"
                if func_key in encoder.attr_funcs:
                    val = model.eval(encoder.attr_funcs[func_key](inst), model_completion=True)
                    inst_data["attributes"][attr_name] = str(val)

            for assoc_name in cls_info.get("associations", {}).keys():
                func_key = f"{class_name}.{assoc_name}"
                if func_key in encoder.assoc_funcs:
                    meta = encoder.assoc_meta[func_key]
                    func = encoder.assoc_funcs[func_key]
                    tgt_class = meta["tgt_class"]
                    tgt_null = encoder.null_consts.get(tgt_class)

                    if meta["is_count"]:
                        links = []
                        for j in range(encoder.scope):
                            tgt_inst = getattr(encoder.sorts[tgt_class], f'{tgt_class.lower()}_{j}')
                            cnt = model.eval(func(inst, tgt_inst), model_completion=True)
                            cnt_val = cnt.as_long() if is_int_value(cnt) else 0
                            if cnt_val > 0:
                                links.append({"target": str(tgt_inst), "count": cnt_val})
                        inst_data["associations"][assoc_name] = links
                    else:
                        tgt_inst = model.eval(func(inst), model_completion=True)
                        if tgt_null is not None and tgt_inst.eq(tgt_null):
                            inst_data["associations"][assoc_name] = None
                        else:
                            inst_data["associations"][assoc_name] = str(tgt_inst)

            state[class_name].append(inst_data)
    return state


def check_case_consistency(case_key, case_data, scope=3):
    model_name = case_data.get("Model_Name", "Unknown")
    uml_context = case_data.get("UML_Context", {})
    constraints = case_data.get("Constraints", {})

    if not constraints:
        return {
            "case_key": case_key,
            "model": model_name,
            "status": "SKIPPED",
            "reason": "No constraints",
            "num_constraints": 0,
            "scope": scope,
            "witness_state": None
        }

    encoder = BoundedUMLModelEncoder(uml_context, scope=scope)
    translator = OCLZ3Translator(encoder)

    solver = Solver()
    solver.set("timeout", Z3_TIMEOUT_MS)
    solver.add(encoder.axioms)

    constraint_details = []

    for cname, cinfo in constraints.items():
        gt_ast_data = cinfo.get("Ground_Truth_AST")
        if not gt_ast_data:
            continue

        gt_constraint = OCLConstraint(**gt_ast_data)
        ctx_class = gt_constraint.context_class
        expr_ast = gt_constraint.expression

        if ctx_class not in encoder.sorts:
            return {
                "case_key": case_key,
                "model": model_name,
                "status": "ERROR",
                "error": f"Context class '{ctx_class}' not in UML model",
                "constraint": cname,
                "scope": scope,
                "witness_state": None
            }

        self_var = Const(f"self_{cname}", encoder.sorts[ctx_class])
        null_const = encoder.null_consts[ctx_class]
        var_bindings = {"context_class": ctx_class, "self": self_var}

        gt_expr, gt_safety = translator.translate(expr_ast, var_bindings)

        if gt_safety:
            safety_conj = And(*gt_safety) if len(gt_safety) > 1 else gt_safety[0]
            gt_expr = And(safety_conj, gt_expr)

        forall_formula = ForAll(
            [self_var],
            Implies(self_var != null_const, gt_expr)
        )
        solver.add(forall_formula)
        constraint_details.append({
            "name": cname,
            "context_class": ctx_class,
        })

    solve_start = time.perf_counter()
    result = solver.check()
    solving_time = time.perf_counter() - solve_start

    witness_state = None
    if result == sat:
        status = "CONSISTENT"
        original_model = solver.model()

        solver.push()
        try:
            for class_name, sort in encoder.sorts.items():
                for i in range(encoder.scope):
                    inst = getattr(sort, f'{class_name.lower()}_{i}')
                    cls_info = encoder.uml_context.get(class_name, {})
                    for attr_name, attr_type in cls_info.get("attributes", {}).items():
                        if attr_type in ("Integer", "Real"):
                            func_key = f"{class_name}.{attr_name}"
                            if func_key in encoder.attr_funcs:
                                solver.add(encoder.attr_funcs[func_key](inst) > 0)

            for class_name, sort in encoder.sorts.items():
                for i in range(encoder.scope):
                    inst = getattr(sort, f'{class_name.lower()}_{i}')
                    cls_info = encoder.uml_context.get(class_name, {})
                    for assoc_name, assoc_type in cls_info.get("associations", {}).items():
                        if "[0..1]" in assoc_type:
                            func_key = f"{class_name}.{assoc_name}"
                            if func_key in encoder.assoc_funcs:
                                meta = encoder.assoc_meta[func_key]
                                tgt_null = encoder.null_consts.get(meta["tgt_class"])
                                if tgt_null is not None:
                                    solver.add(encoder.assoc_funcs[func_key](inst) != tgt_null)

            heuristic_result = solver.check()
            if heuristic_result == sat:
                final_model = solver.model()
            else:
                final_model = original_model

        except Exception:
            final_model = original_model
        finally:
            solver.pop()

        witness_state = extract_full_state(final_model, encoder)

    elif result == unsat:
        status = "INCONSISTENT"
    else:
        status = "TIMEOUT"

    return {
        "case_key": case_key,
        "model": model_name,
        "status": status,
        "num_constraints": len(constraint_details),
        "constraints": constraint_details,
        "solving_time_sec": round(solving_time, 4),
        "scope": scope,
        "witness_state": witness_state
    }


def main():
    benchmark_path = sys.argv[1] if len(sys.argv) > 1 else "benchmark.json"
    scope = int(sys.argv[2]) if len(sys.argv) > 2 else 3

    print("=" * 70)
    print("Benchmark Ground Truth Consistency Check")
    print(f"Scope k = {scope}, Timeout = {Z3_TIMEOUT_MS}ms")
    print("=" * 70)

    with open(benchmark_path, "r", encoding="utf-8") as f:
        benchmark = json.load(f)

    all_results = {}

    for case_key, case_data in benchmark.items():
        model_name = case_data.get("Model_Name", "Unknown")
        print(f"\n[{case_key}] {model_name}")

        result = check_case_consistency(case_key, case_data, scope)
        all_results[case_key] = result

        print(f"  Status: {result['status']}")
        print(f"  Constraints: {result.get('num_constraints', 0)}")
        if "solving_time_sec" in result:
            print(f"  Solving time: {result['solving_time_sec']}s")
        if result["status"] == "INCONSISTENT":
            print("  WARNING: Constraints conflict!")
        elif result["status"] == "ERROR":
            print(f"  Error: {result.get('error', 'Unknown')}")

    consistent = [k for k, r in all_results.items() if r["status"] == "CONSISTENT"]
    inconsistent = [k for k, r in all_results.items() if r["status"] == "INCONSISTENT"]
    timeouts = [k for k, r in all_results.items() if r["status"] == "TIMEOUT"]
    errors = [k for k, r in all_results.items() if r["status"] == "ERROR"]
    skipped = [k for k, r in all_results.items() if r["status"] == "SKIPPED"]

    total = len(all_results)
    print("\n" + "=" * 70)
    print("SUMMARY")
    print("=" * 70)
    print(f"Total cases: {total}")
    print(f"Consistent:  {len(consistent)}/{total}")
    print(f"Inconsistent:{len(inconsistent)}/{total}")
    print(f"Timeout:     {len(timeouts)}/{total}")
    print(f"Error:       {len(errors)}/{total}")
    print(f"Skipped:     {len(skipped)}/{total}")

    if inconsistent:
        print("\nInconsistent cases:")
        for k in inconsistent:
            print(f"  - {k} ({all_results[k]['model']})")

    if timeouts:
        print("\nTimeout cases:")
        for k in timeouts:
            print(f"  - {k} ({all_results[k]['model']})")

    if errors:
        print("\nError cases:")
        for k in errors:
            print(f"  - {k} ({all_results[k]['model']}): {all_results[k].get('error', 'Unknown')}")

    report_path = "benchmark_consistency_report.json"
    with open(report_path, "w", encoding="utf-8") as f:
        json.dump(all_results, f, indent=2, ensure_ascii=False)
    print(f"\nReport saved to: {report_path}")


if __name__ == "__main__":
    main()
