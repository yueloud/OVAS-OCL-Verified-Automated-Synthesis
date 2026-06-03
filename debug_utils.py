import logging
import json
import z3

# ==========================================
# 调试开关：提交前改为 False 即可禁用所有日志
# ==========================================
ENABLE_DUMP = True

# 初始化 Logger，输出到 formulas_debug.log
logger = logging.getLogger("FormulaDumper")
if ENABLE_DUMP:
    logger.setLevel(logging.INFO)
    # 防止重复添加 handler，且不清除已有日志
    if not logger.handlers:
        handler = logging.FileHandler("formulas_debug.log", mode='w', encoding='utf-8')
        formatter = logging.Formatter('%(message)s')
        handler.setFormatter(formatter)
        logger.addHandler(handler)


def dump_formula(case_key: str, constraint_name: str, stage: str, z3_expr: z3.ExprRef, extra_info: str = ""):
    """
    将 Z3 公式保存为 SMT-LIB 格式的 JSON 日志。

    Args:
        case_key: Benchmark 中的 case_key
        constraint_name: 约束名称
        stage: 标记当前是哪个阶段 (e.g., "GT_Logic", "Cand_Logic", "Check_Equiv")
        z3_expr: 要保存的 Z3 表达式
        extra_info: 额外的备注信息
    """
    if not ENABLE_DUMP:
        return

    try:
        # 1. 提取 SMT-LIB 标准格式字符串，这是最直观的公式表现
        smt_str = z3_expr.sexpr() if hasattr(z3_expr, 'sexpr') else str(z3_expr)

        # 2. 提取公式类型
        expr_type = str(z3_expr.sort()) if hasattr(z3_expr, 'sort') else "Unknown"

        log_entry = {
            "case": case_key,
            "constraint": constraint_name,
            "stage": stage,
            "type": expr_type,
            "smt_lib": smt_str,
            "note": extra_info
        }

        logger.info(json.dumps(log_entry, ensure_ascii=False))

    except Exception as e:
        # 防止打印公式本身出错导致主流程崩溃
        logger.error(f"Failed to dump formula for {case_key}/{constraint_name}: {e}")
