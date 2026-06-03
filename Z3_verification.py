import re
import itertools
from typing import Dict, List, Tuple
from z3 import *
from debug_utils import dump_formula, ENABLE_DUMP
from json_schema import (OCLExpression, PropertyCall, OperationCall, BinaryExpression,
                         IteratorExpression, CollectionOperation, LiteralExpression,
                         IfExpression, UnaryExpression, LetExpression, CollectionLiteral)


# ==========================================
# 集合引用标记类
# ==========================================
class CollectionRef:
    """标记类：代表 Z3 编码管线中的集合引用。"""

    def __init__(self, root_inst, cnt_func, element_class, valid_instances,
                 attr_func=None, nav_chain=None, is_set_semantic=False):
        self.root_inst = root_inst
        self.cnt_func = cnt_func
        self.element_class = element_class
        self.valid_instances = valid_instances
        self.attr_func = attr_func
        self.nav_chain = nav_chain or []
        self.is_set_semantic = is_set_semantic


# ==========================================
# 组件 1：有界元模型编码器
# ==========================================
class BoundedMetamodelEncoder:
    def __init__(self, uml_context: dict, scope: int = 3):
        self.uml_context = uml_context
        self.scope = scope
        self.sorts: Dict[str, DatatypeSortRef] = {}
        self.null_consts: Dict[str, Any] = {}
        self.attr_funcs: Dict[str, FuncDeclRef] = {}
        self.assoc_funcs: Dict[str, FuncDeclRef] = {}
        self.assoc_meta: Dict[str, Dict] = {}
        self.axioms: List[Any] = []
        self.sort_to_null: Dict[SortRef, Any] = {}
        self._encode_metamodel()
        self._generate_axioms()

    def _z3_sort(self, type_str: str):
        if type_str == "Integer": return IntSort()
        if type_str == "Real": return RealSort()
        if type_str == "Boolean": return BoolSort()
        if type_str == "String": return StringSort()
        return None

    def _encode_metamodel(self):
        for class_name in self.uml_context.keys():
            Datatype(class_name)

        for class_name in self.uml_context.keys():
            dt = Datatype(class_name)
            for i in range(self.scope):
                dt.declare(f'{class_name.lower()}_{i}')
            dt.declare(f'{class_name.lower()}_null')
            self.sorts[class_name] = dt.create()
            self.null_consts[class_name] = getattr(self.sorts[class_name], f'{class_name.lower()}_null')
            self.sort_to_null[self.sorts[class_name]] = self.null_consts[class_name]

        for class_name, cls_info in self.uml_context.items():
            sort = self.sorts[class_name]
            for attr_name, attr_type in cls_info.get("attributes", {}).items():
                ret_sort = self._z3_sort(attr_type)
                if ret_sort is not None:
                    self.attr_funcs[f"{class_name}.{attr_name}"] = Function(
                        f'{class_name}_{attr_name}', sort, ret_sort)

        for class_name, cls_info in self.uml_context.items():
            src_sort = self.sorts[class_name]
            for assoc_name, assoc_type in cls_info.get("associations", {}).items():
                match_coll = re.match(r'(Set|Bag)\((\w+)\)', assoc_type)
                match_opt = re.match(r'(\w+)\[0\.\.1]', assoc_type)
                match_req = re.match(r'(\w+)\[1\.\.1]', assoc_type)
                func_key = f"{class_name}.{assoc_name}"

                if match_coll:
                    coll_kind = match_coll.group(1)
                    tgt_name = match_coll.group(2)
                    tgt_sort = self.sorts[tgt_name]
                    self.assoc_funcs[func_key] = Function(
                        f'{class_name}_{assoc_name}_cnt', src_sort, tgt_sort, IntSort())
                    self.assoc_meta[func_key] = {
                        "src_class": class_name, "tgt_class": tgt_name,
                        "is_count": True, "is_mandatory": False,
                        "is_set_semantic": (coll_kind == "Set")}

                elif match_opt or match_req:
                    tgt_name = (match_opt or match_req).group(1)
                    tgt_sort = self.sorts[tgt_name]
                    is_mandatory = match_req is not None
                    self.assoc_funcs[func_key] = Function(
                        f'{class_name}_{assoc_name}_nav', src_sort, tgt_sort)
                    self.assoc_meta[func_key] = {
                        "src_class": class_name, "tgt_class": tgt_name,
                        "is_count": False, "is_mandatory": is_mandatory}

    def _generate_axioms(self):
        self.axioms = []

        # Null 哨兵全局公理
        for key, func in self.attr_funcs.items():
            class_name = key.split('.')[0]
            null = self.null_consts[class_name]
            ret_sort = func.range()
            if ret_sort == IntSort():
                self.axioms.append(func(null) == 0)
            elif ret_sort == RealSort():
                self.axioms.append(func(null) == RealVal(0))
            elif ret_sort == BoolSort():
                self.axioms.append(func(null) == False)
            elif ret_sort == StringSort():
                self.axioms.append(func(null) == StringVal(""))

        for key, func in self.assoc_funcs.items():
            meta = self.assoc_meta[key]
            src_null = self.null_consts[meta["src_class"]]
            tgt_null = self.null_consts[meta["tgt_class"]]

            if meta["is_count"]:
                for src_inst in self.get_valid_instances(meta["src_class"]):
                    self.axioms.append(func(src_inst, tgt_null) == 0)
                for tgt_inst in self.get_valid_instances(meta["tgt_class"]):
                    self.axioms.append(func(src_null, tgt_inst) == 0)
                self.axioms.append(func(src_null, tgt_null) == 0)
                for src_inst in self.get_valid_instances(meta["src_class"]):
                    for tgt_inst in self.get_valid_instances(meta["tgt_class"]):
                        self.axioms.append(func(src_inst, tgt_inst) >= 0)
                        if meta.get("is_set_semantic", False):
                            self.axioms.append(func(src_inst, tgt_inst) <= 1)

            else:
                self.axioms.append(func(src_null) == tgt_null)
                # [1..1] 关联非空全局约束
                if meta["is_mandatory"]:
                    for src_inst in self.get_valid_instances(meta["src_class"]):
                        self.axioms.append(
                            Implies(src_inst != src_null, func(src_inst) != tgt_null))

    def get_valid_instances(self, class_name: str) -> List[Any]:
        sort = self.sorts[class_name]
        instances = [getattr(sort, f'{class_name.lower()}_{i}') for i in range(self.scope)]
        instances.append(self.null_consts[class_name])  # 核心修复：将 null 哨兵纳入追踪域
        return instances

    def _default_value_for_sort(self, sort_ref):
        """根据 Z3 Sort 返回类型安全的哑值（用于 Sort Mismatch 回退）"""
        if sort_ref == IntSort(): return IntVal(0)
        if sort_ref == RealSort(): return RealVal(0)
        if sort_ref == BoolSort(): return BoolVal(False)
        if sort_ref == StringSort(): return StringVal("")
        return IntVal(0)


# ==========================================
# 组件 2：AST 驱动的 Z3 忠实翻译器
# ==========================================
class OCLZ3Translator:
    def __init__(self, meta_encoder: BoundedMetamodelEncoder):
        self.me = meta_encoder

    def translate(self, ast: OCLExpression, var_bindings: Dict[str, Any]) -> Tuple[Any, List]:
        node_type = ast.type

        if node_type == "Variable":
            if ast.name in var_bindings:
                return var_bindings[ast.name], []
            raise ValueError(f"Unbound variable: {ast.name}")

        elif node_type == "LiteralExpression":
            return self._handle_literal(ast)

        elif node_type == "UnaryExpression":
            return self._handle_unary_expr(ast, var_bindings)

        elif node_type == "BinaryExpression":
            return self._handle_binary_expr(ast, var_bindings)

        elif node_type == "IfExpression":
            return self._handle_if_expr(ast, var_bindings)

        elif node_type == "LetExpression":
            return self._handle_let_expr(ast, var_bindings)

        elif node_type == "PropertyCall":
            return self._handle_property_call(ast, var_bindings)

        elif node_type == "OperationCall":
            return self._handle_operation_call(ast, var_bindings)

        elif node_type == "CollectionLiteral":
            return self._handle_collection_literal(ast, var_bindings)

        elif node_type == "IteratorExpression":
            return self._handle_iterator(ast, var_bindings)

        elif node_type == "CollectionOperation":
            return self._handle_collection_op(ast, var_bindings)

        raise NotImplementedError(f"AST node type not implemented: {node_type}")

    #Basic Expressions
    def _handle_literal(self, ast: LiteralExpression) -> Tuple[Any, List]:
        val = ast.value
        lt = ast.literal_type
        if lt == "Integer": return IntVal(val), []
        if lt == "Real": return RealVal(val), []
        if lt == "Boolean": return BoolVal(val), []
        if lt == "String": return StringVal(str(val)), []
        if lt == "Null": return None, []
        return IntVal(0), []

    def _handle_unary_expr(self, ast: UnaryExpression, var_bindings: Dict) -> Tuple[Any, List]:
        expr, safety = self.translate(ast.expression, var_bindings)
        if ast.operator == "not":
            # 终极修复：直接透传 safety，防止 not(invalid) 被错误反转为 True
            return Not(expr), safety
        elif ast.operator == "-":
            return -expr, safety
        raise NotImplementedError(f"Unary operator: {ast.operator}")

    def _handle_binary_expr(self, ast: BinaryExpression, var_bindings: Dict) -> Tuple[Any, List]:
        left, left_safety = self.translate(ast.left, var_bindings)
        right, right_safety = self.translate(ast.right, var_bindings)
        op = ast.operator

        if op == '/':
            if is_int(left): left = ToReal(left)
            if is_int(right): right = ToReal(right)
            return left / right, left_safety + right_safety + [right != 0]

        if op in ['+', '-', '*']:
            return self._apply_arithmetic(op, left, right), left_safety + right_safety

        if op in ['=', '<>', '<', '<=', '>', '>=']:
            # Int/Real 自动提升必须在 Sort mismatch 检查之前
            if is_real(left) and is_int(right):
                right = ToReal(right)
            elif is_int(left) and is_real(right):
                left = ToReal(left)
            # 提升后再做 Sort mismatch 检查
            if op in ['=', '<>'] and left.sort() != right.sort():
                if op == '=':
                    return BoolVal(False), left_safety + right_safety
                else:
                    return BoolVal(True), left_safety + right_safety
            constraint = self._apply_relational(op, left, right)
            return constraint, left_safety + right_safety

        def combine_s(s_list):
            return And(*s_list) if s_list else BoolVal(True)

        s_l = combine_s(left_safety)
        s_r = combine_s(right_safety)

        if op == 'and':
            # 对称化修复：如果一侧为 False，则无视另一侧的 Invalid；仅当两侧均不为 False 且有一侧 Invalid 时，整体 Invalid
            is_safe = Or(And(s_l, Not(left)), And(s_r, Not(right)), And(s_l, s_r))
            return And(left, right), [is_safe]
        if op == 'or':
            # 对称化修复：如果一侧为 True，则无视另一侧的 Invalid
            is_safe = Or(And(s_l, left), And(s_r, right), And(s_l, s_r))
            return Or(left, right), [is_safe]
        if op == 'implies':
            # implies 保持非对称，符合 OCL 语义 (false implies invalid = true)
            return Implies(left, right), [And(s_l, Implies(left, s_r))]
        if op == 'xor':
            return Xor(left, right), left_safety + right_safety
        raise NotImplementedError(f"Binary operator not implemented: {op}")

    def _handle_if_expr(self, ast: IfExpression, var_bindings: Dict) -> Tuple[Any, List]:
        cond, cond_safety = self.translate(ast.condition, var_bindings)
        then_expr, then_safety = self.translate(ast.then_expr, var_bindings)
        else_expr, else_safety = self.translate(ast.else_expr, var_bindings)

        # 终极修复：条件分支下的安全条件动态选择
        def combine_s(s_list): return And(*s_list) if s_list else BoolVal(True)

        s_cond = combine_s(cond_safety)
        s_then = combine_s(then_safety)
        s_else = combine_s(else_safety)

        combined_safety = And(s_cond, If(cond, s_then, s_else))
        return If(cond, then_expr, else_expr), [combined_safety]

    def _handle_let_expr(self, ast: LetExpression, var_bindings: Dict) -> Tuple[Any, List]:
        val_expr, val_safety = self.translate(ast.value, var_bindings)
        new_bindings = var_bindings.copy()
        new_bindings[ast.variable.name] = val_expr
        body_expr, body_safety = self.translate(ast.body, new_bindings)
        return body_expr, val_safety + body_safety

    #Property & Operation Calls
    def _handle_property_call(self, ast: PropertyCall, var_bindings: Dict) -> Tuple[Any, List]:
        src_result, src_safety = self.translate(ast.source, var_bindings)

        if isinstance(src_result, CollectionRef):
            return self._handle_implicit_collect(src_result, ast.property_name, src_safety)

        src_expr = src_result
        src_type_name = self._infer_class_name(ast.source, var_bindings)
        func_key = f"{src_type_name}.{ast.property_name}"

        # === 核心修复：获取源类型的 null 哨兵 ===
        # 任何对单对象的点号访问（.attr 或 .nav），前提都是源对象不能是 null
        src_null = self.me.null_consts.get(src_type_name)
        base_safety = src_safety + ([src_expr != src_null] if src_null is not None else [])

        # 关联导航
        if func_key in self.me.assoc_funcs:
            func = self.me.assoc_funcs[func_key]
            meta = self.me.assoc_meta[func_key]

            if src_expr.sort() != func.domain(0):
                raise ValueError(...)

            if meta["is_count"]:
                valid_instances = self.me.get_valid_instances(meta["tgt_class"])
                # 修复：集合导航源不能为 null (null.staff 是 invalid)
                return CollectionRef(
                    root_inst=src_expr, cnt_func=func, element_class=meta["tgt_class"],
                    valid_instances=valid_instances,
                    is_set_semantic=meta.get("is_set_semantic", False)
                ), base_safety
            else:
                result = func(src_expr)
                return result, base_safety

        # 属性访问
        if func_key in self.me.attr_funcs:
            func = self.me.attr_funcs[func_key]
            if src_expr.sort() != func.domain(0):
                raise ValueError(...)
            return func(src_expr), base_safety

        raise ValueError(f"Unknown property: {func_key}")

    def _handle_implicit_collect(self, coll_ref: CollectionRef, prop_name: str,
                                 src_safety: List) -> Tuple[Any, List]:
        if not isinstance(coll_ref, CollectionRef):
            # 理论上进入此函数的必定是 CollectionRef，如果不是，说明 LLM 在非集合上调用了 ->
            raise ValueError(
                f"Semantic Error: Cannot navigate property '{prop_name}' on a non-collection value. Did you mean to use '.' instead of '->'?")
        """处理隐式 collect：从集合导航属性 (如 self.staff.salary)"""
        element_class = coll_ref.element_class
        func_key = f"{element_class}.{prop_name}"

        if func_key in self.me.attr_funcs:
            return CollectionRef(
                root_inst=coll_ref.root_inst, cnt_func=coll_ref.cnt_func,
                element_class=element_class, valid_instances=coll_ref.valid_instances,
                attr_func=self.me.attr_funcs[func_key],
                nav_chain=coll_ref.nav_chain,
                is_set_semantic=False), src_safety

        if func_key in self.me.assoc_funcs:
            func = self.me.assoc_funcs[func_key]
            meta = self.me.assoc_meta[func_key]

            if not meta["is_count"]:
                # 立刻进行目标类型投影，废弃失效的 nav_chain
                tgt_class = meta["tgt_class"]
                tgt_instances = self.me.get_valid_instances(tgt_class)
                src_root_inst = coll_ref.root_inst
                null_c = self.me.null_consts.get(coll_ref.element_class)

                def mapped_cnt(root, tgt_elem):
                    total = IntVal(0)
                    for src_elem in coll_ref.valid_instances:
                        if null_c is not None and src_elem.eq(null_c): continue
                        nav_val = src_elem
                        for nav_func in coll_ref.nav_chain:
                            nav_val = nav_func(nav_val)
                        nav_val = func(nav_val)
                        src_cnt = coll_ref.cnt_func(src_root_inst, src_elem)
                        total = total + If(nav_val == tgt_elem, src_cnt, IntVal(0))
                    return total

                return CollectionRef(
                    root_inst=coll_ref.root_inst, cnt_func=mapped_cnt,
                    element_class=tgt_class, valid_instances=tgt_instances,
                    nav_chain=[], is_set_semantic=False
                ), src_safety
            else:
                return self._handle_nested_collection(coll_ref, func_key, meta, src_safety)

        raise ValueError(f"Unknown property in implicit collect: {func_key}")

    def _handle_nested_collection(self, parent_ref: CollectionRef, func_key: str, meta: Dict, src_safety: List) -> \
    Tuple[Any, List]:
        sub_cnt_func = self.me.assoc_funcs[func_key]
        sub_element_class = meta["tgt_class"]
        sub_valid_instances = self.me.get_valid_instances(sub_element_class)
        prop_root_inst = parent_ref.root_inst
        null_c = self.me.null_consts.get(parent_ref.element_class)  # 获取 null 哨兵

        def combined_cnt(root, sub_elem):
            total = IntVal(0)
            for parent_elem in parent_ref.valid_instances:
                # 核心修复：剔除对 null 的属性导航贡献
                if null_c is not None and parent_elem.eq(null_c):
                    continue
                parent_cnt = parent_ref.cnt_func(prop_root_inst, parent_elem)
                sub_cnt = sub_cnt_func(parent_elem, sub_elem)
                max_cnt = 1 if parent_ref.is_set_semantic else self.me.scope
                total = total + self._linear_multiply(parent_cnt, sub_cnt, max_cnt)
            return total

        return CollectionRef(
            root_inst=prop_root_inst, cnt_func=combined_cnt, element_class=sub_element_class,
            valid_instances=sub_valid_instances, is_set_semantic=False), src_safety  # 恢复使用 src_safety

    def _handle_operation_call(self, ast: OperationCall, var_bindings: Dict) -> Tuple[Any, List]:
        op = ast.operation_name

        # === 第一类：不需要翻译 source 的操作 ===
        if op == "allInstances":
            if ast.source.type == "Variable" and ast.source.name in self.me.uml_context:
                element_class = ast.source.name
            else:
                element_class = self._infer_class_name(ast.source, var_bindings)
            valid_instances = self.me.get_valid_instances(element_class)

            # === 核心修复：OCL 语义中 allInstances 绝不包含 null ===
            null_c = self.me.null_consts.get(element_class)
            if null_c is not None:
                valid_instances = [inst for inst in valid_instances if not inst.eq(null_c)]

            return CollectionRef(
                root_inst=None, cnt_func=lambda root, inst: IntVal(1), element_class=element_class,
                valid_instances=valid_instances, is_set_semantic=True), []

        # === 第二类：需要翻译 source 的操作 ===
        src_expr, src_safety = self.translate(ast.source, var_bindings)

        if op == "isDefined":
            src_type = self._infer_class_name(ast.source, var_bindings)
            null_const = self.me.null_consts.get(src_type)
            is_safe = And(*src_safety) if src_safety else BoolVal(True)
            if null_const is not None:
                return And(is_safe, src_expr != null_const), []
            return is_safe, []

        if op == "oclIsUndefined":
            src_type = self._infer_class_name(ast.source, var_bindings)
            null_const = self.me.null_consts.get(src_type)
            is_safe = And(*src_safety) if src_safety else BoolVal(True)
            if null_const is not None:
                return Or(Not(is_safe), src_expr == null_const), []
            return Not(is_safe), []

        if op == "abs":
            return If(src_expr < 0, -src_expr, src_expr), src_safety
        if op == "oclIsKindOf":
            return BoolVal(True), src_safety
        if op == "toString":
            return StringVal(""), src_safety

        raise NotImplementedError(f"Operation not implemented: {op}")

    #Collection
    def _handle_collection_literal(self, ast: CollectionLiteral, var_bindings: Dict) -> Tuple[Any, List]:
        elements = []
        literal_safety = []
        for elem in ast.elements:
            elem_expr, elem_safety = self.translate(elem, var_bindings)
            elements.append(elem_expr)
            literal_safety.extend(elem_safety)

        if ast.collection_kind == "Set":
            unique_elements = []
            seen_keys = set()
            for elem_expr in elements:
                # 1. 归一化：消除代数/语法差异
                normalized = simplify(elem_expr)
                # 2. 防碰撞哈希键：融合代数表示与底层 Sort
                key = f"{str(normalized)}:{normalized.sort()}"
                if key not in seen_keys:
                    seen_keys.add(key)
                    # 优化：直接保留化简后的 AST，降低 SMT 求解器负担
                    unique_elements.append(normalized)
            elements = unique_elements

        def literal_cnt(root, inst):
            return IntVal(1)

        return CollectionRef(
            root_inst=None, cnt_func=literal_cnt,
            element_class="Unknown", valid_instances=elements,
            is_set_semantic=(ast.collection_kind == "Set")), literal_safety

    def _handle_iterator(self, ast: IteratorExpression, var_bindings: Dict) -> Tuple[Any, List]:
        coll_ref, coll_safety = self._resolve_collection_source(ast.source, var_bindings)
        element_class = coll_ref.element_class
        iter_vars = [v.name for v in ast.iterator_variables]

        # 缺陷 1 修复：多重迭代变量的笛卡尔积展开
        if len(iter_vars) == 1:
            return self._handle_single_var_iterator(
                ast, coll_ref, iter_vars[0], element_class, var_bindings, coll_safety)
        else:
            return self._handle_multi_var_iterator(
                ast, coll_ref, iter_vars, element_class, var_bindings, coll_safety)

    def _handle_single_var_iterator(self, ast, coll_ref, iter_var_name, element_class, var_bindings, coll_safety):
        """单变量迭代器的处理（含安全条件冒泡修复）"""

        accumulated_body_safety = []

        # ========== forAll / exists：布尔逻辑 ==========
        if ast.iterator_type in ["forAll", "exists"]:
            results = []
            for inst in coll_ref.valid_instances:
                body_val, body_safety_ref = self._eval_body_with_var(
                    ast.body, iter_var_name, inst, element_class, var_bindings)
                in_set = coll_ref.cnt_func(coll_ref.root_inst, inst) > 0
                accumulated_body_safety.append(Implies(in_set, body_safety_ref))

                if ast.iterator_type == "forAll":
                    results.append(Implies(in_set, body_val))
                elif ast.iterator_type == "exists":
                    results.append(And(in_set, body_val))

            final_safety = coll_safety + accumulated_body_safety
            if ast.iterator_type == "forAll":
                return And(*results), final_safety
            elif ast.iterator_type == "exists":
                return Or(*results), final_safety

        # ========== isUnique ==========
        elif ast.iterator_type == "isUnique":
            return self._handle_is_unique_single(
                ast, coll_ref, iter_var_name, element_class, var_bindings, coll_safety)

        # ========== select / reject ==========
        elif ast.iterator_type in ["select", "reject"]:
            body_vals = {}
            for inst in coll_ref.valid_instances:
                body_val, body_safety_ref = self._eval_body_with_var(
                    ast.body, iter_var_name, inst, element_class, var_bindings)
                in_set = coll_ref.cnt_func(coll_ref.root_inst, inst) > 0
                accumulated_body_safety.append(Implies(in_set, body_safety_ref))
                body_vals[inst] = body_val

            filter_root_inst = coll_ref.root_inst

            def filtered_cnt(root, inst):
                base_cnt = coll_ref.cnt_func(filter_root_inst, inst)
                b_val = body_vals.get(inst, BoolVal(False))
                if ast.iterator_type == "select":
                    return If(And(base_cnt > 0, b_val), base_cnt, IntVal(0))
                else:
                    return If(And(base_cnt > 0, Not(b_val)), base_cnt, IntVal(0))

            final_safety = coll_safety + accumulated_body_safety
            return CollectionRef(
                root_inst=filter_root_inst,
                cnt_func=filtered_cnt,
                element_class=element_class,
                valid_instances=coll_ref.valid_instances,
                attr_func=coll_ref.attr_func,
                nav_chain=coll_ref.nav_chain,
                is_set_semantic=coll_ref.is_set_semantic), final_safety

        # ========== collect ==========
        elif ast.iterator_type == "collect":
            for inst in coll_ref.valid_instances:
                pass

            final_safety = coll_safety
            return CollectionRef(
                root_inst=coll_ref.root_inst,
                cnt_func=coll_ref.cnt_func,
                element_class=element_class,
                valid_instances=coll_ref.valid_instances,
                attr_func=("collect_body", ast.body, iter_var_name, element_class, var_bindings),
                nav_chain=coll_ref.nav_chain,
                is_set_semantic=False), final_safety

        raise NotImplementedError(f"Iterator not implemented: {ast.iterator_type}")

    def _handle_multi_var_iterator(self, ast, coll_ref, iter_vars, element_class, var_bindings, coll_safety):
        """多重迭代变量的笛卡尔积展开（含安全条件冒泡修复）"""
        iter_type = ast.iterator_type
        n_vars = len(iter_vars)

        # 核心修复：统一收集闭包体在各个实例组合上求值时的安全条件
        accumulated_body_safety = []

        # ========== forAll / exists：布尔逻辑 ==========
        if iter_type in ["forAll", "exists"]:
            results = []
            for inst_tuple in itertools.product(coll_ref.valid_instances, repeat=n_vars):
                in_set_conditions = []
                for var_name, inst in zip(iter_vars, inst_tuple):
                    in_set_conditions.append(coll_ref.cnt_func(coll_ref.root_inst, inst) > 0)
                in_set = And(*in_set_conditions) if len(in_set_conditions) > 1 else in_set_conditions[0]

                body_val, body_safety_ref = self._eval_body_with_vars(
                    ast.body, iter_vars, inst_tuple, element_class, var_bindings)
                accumulated_body_safety.append(Implies(in_set, body_safety_ref))

                if iter_type == "forAll":
                    results.append(Implies(in_set, body_val))
                elif iter_type == "exists":
                    results.append(And(in_set, body_val))

            final_safety = coll_safety + accumulated_body_safety

            if iter_type == "forAll":
                return And(*results), final_safety
            elif iter_type == "exists":
                return Or(*results), final_safety

        # ========== isUnique ==========
        elif iter_type == "isUnique":
            # isUnique 需要预计算所有元组的 body_val 和 safety
            tuples = list(itertools.product(coll_ref.valid_instances, repeat=n_vars))
            body_vals = {}
            for t in tuples:
                in_set_conditions = []
                for var_name, inst in zip(iter_vars, t):
                    in_set_conditions.append(coll_ref.cnt_func(coll_ref.root_inst, inst) > 0)
                in_set = And(*in_set_conditions) if len(in_set_conditions) > 1 else in_set_conditions[0]

                body_val, body_safety_ref = self._eval_body_with_vars(
                    ast.body, iter_vars, t, element_class, var_bindings)
                accumulated_body_safety.append(Implies(in_set, body_safety_ref))
                body_vals[t] = body_val

            pair_constraints = []
            for i, t1 in enumerate(tuples):
                for j, t2 in enumerate(tuples):
                    if i < j:
                        not_same = Or(*[a != b for a, b in zip(t1, t2)])
                        in1_conditions = [coll_ref.cnt_func(coll_ref.root_inst, inst) > 0 for inst in t1]
                        in2_conditions = [coll_ref.cnt_func(coll_ref.root_inst, inst) > 0 for inst in t2]
                        in1 = And(*in1_conditions) if len(in1_conditions) > 1 else in1_conditions[0]
                        in2 = And(*in2_conditions) if len(in2_conditions) > 1 else in2_conditions[0]

                        b1 = body_vals[t1]
                        b2 = body_vals[t2]
                        pair_constraints.append(Implies(And(in1, in2, not_same), b1 != b2))

            final_safety = coll_safety + accumulated_body_safety
            return And(*pair_constraints), final_safety

        raise NotImplementedError(f"Multi-var iterator not implemented: {iter_type}")

    def _handle_is_unique_single(self, ast, coll_ref, iter_var_name, element_class, var_bindings, coll_safety):
        """单变量 isUnique 处理（含安全条件冒泡修复）"""
        pair_constraints = []
        accumulated_body_safety = []
        instances = coll_ref.valid_instances

        # 预求值缓存
        body_vals = {}
        for inst in instances:
            body_val, body_safety_ref = self._eval_body_with_var(
                ast.body, iter_var_name, inst, element_class, var_bindings)
            in_set = coll_ref.cnt_func(coll_ref.root_inst, inst) > 0
            accumulated_body_safety.append(Implies(in_set, body_safety_ref))
            body_vals[inst] = body_val

        for i, inst1 in enumerate(instances):
            for j, inst2 in enumerate(instances):
                if i < j:
                    in1 = coll_ref.cnt_func(coll_ref.root_inst, inst1) > 0
                    in2 = coll_ref.cnt_func(coll_ref.root_inst, inst2) > 0
                    b1 = body_vals[inst1]
                    b2 = body_vals[inst2]
                    pair_constraints.append(
                        Implies(And(in1, in2, inst1 != inst2), b1 != b2))

        final_safety = coll_safety + accumulated_body_safety
        return And(*pair_constraints), final_safety

    def _handle_collection_op(self, ast: CollectionOperation, var_bindings: Dict) -> Tuple[Any, List]:

        op = ast.operation_type
        coll_ref, coll_safety = self._resolve_collection_source(ast.source, var_bindings)

        def _get_actual_val_for_coll(target_coll: CollectionRef, inst, accumulated_safety, cnt_val):
            """返回 (值, 是否有效的Z3布尔表达式)"""
            if target_coll.attr_func is None:
                return inst, BoolVal(True)
            if isinstance(target_coll.attr_func, tuple) and target_coll.attr_func[0] == "collect_body":
                _, body_ast, var_name, elem_class, saved_bindings = target_coll.attr_func
                body_val, body_safety = self._eval_body_with_var(body_ast, var_name, inst, elem_class, saved_bindings)
                # 核心修复：返回 body_safety 作为有效性标记
                return body_val, body_safety
            elif callable(target_coll.attr_func):
                nav_val = inst
                is_valid = BoolVal(True)
                for nav_func in target_coll.nav_chain:
                    null_c = self.me.sort_to_null.get(nav_val.sort())
                    if null_c is not None:
                        is_valid = And(is_valid, nav_val != null_c)
                    nav_val = nav_func(nav_val)
                null_c = self.me.sort_to_null.get(nav_val.sort())
                if null_c is not None:
                    is_valid = And(is_valid, nav_val != null_c)
                # 核心修复：任何一环为 null 则整体 invalid
                return target_coll.attr_func(nav_val), is_valid
            return inst, BoolVal(True)

        def _safe_eq(left, right):
            """安全的 Z3 等价性比较，防止 Int/Real Sort Mismatch"""
            if is_real(left) and is_int(right):
                right = ToReal(right)
            elif is_int(left) and is_real(right):
                left = ToReal(left)
            if left.sort() != right.sort():
                raise ValueError(
                    f"Z3 Sort Mismatch in collection element comparison: "
                    f"{left.sort()} vs {right.sort()}. "
                    f"This indicates a type inference bug bypassed the semantic firewall."
                )
            return left == right

        if op == "size":
            return self._compute_size(coll_ref), coll_safety
        if op == "isEmpty":
            return self._compute_size(coll_ref) == 0, coll_safety
        if op == "notEmpty":
            return self._compute_size(coll_ref) > 0, coll_safety
        if op == "sum":
            sum_expr, sum_safety = self._compute_sum(coll_ref)
            return sum_expr, coll_safety + sum_safety

        if op == "includes":
            if ast.arguments:
                arg_expr, arg_safety = self.translate(ast.arguments[0], var_bindings)
                conds = []
                for inst in coll_ref.valid_instances:
                    base_cnt = coll_ref.cnt_func(coll_ref.root_inst, inst)
                    actual_val, is_valid = _get_actual_val_for_coll(coll_ref, inst, arg_safety, base_cnt)
                    effective_cnt = If(is_valid, base_cnt, IntVal(0))  # 剔除 invalid
                    conds.append(And(effective_cnt > 0, _safe_eq(actual_val, arg_expr)))

                return Or(*conds) if conds else BoolVal(False), coll_safety + arg_safety

        if op == "excludes":
            if ast.arguments:
                arg_expr, arg_safety = self.translate(ast.arguments[0], var_bindings)
                conds = []
                for inst in coll_ref.valid_instances:
                    base_cnt = coll_ref.cnt_func(coll_ref.root_inst, inst)
                    actual_val, is_valid = _get_actual_val_for_coll(coll_ref, inst, arg_safety, base_cnt)
                    effective_cnt = If(is_valid, base_cnt, IntVal(0))  # 剔除 invalid
                    conds.append(Implies(effective_cnt > 0, Not(_safe_eq(actual_val, arg_expr))))

                return And(*conds) if conds else BoolVal(True), coll_safety + arg_safety

        if op == "asSet":
            return CollectionRef(
                root_inst=coll_ref.root_inst, cnt_func=coll_ref.cnt_func, element_class=coll_ref.element_class,
                valid_instances=coll_ref.valid_instances, attr_func=coll_ref.attr_func, nav_chain=coll_ref.nav_chain,
                is_set_semantic=True  # 强制转为 Set 语义
            ), coll_safety

        if op == "asBag":
            return CollectionRef(
                root_inst=coll_ref.root_inst, cnt_func=coll_ref.cnt_func, element_class=coll_ref.element_class,
                valid_instances=coll_ref.valid_instances, attr_func=coll_ref.attr_func, nav_chain=coll_ref.nav_chain,
                is_set_semantic=False  # 强制转为 Bag 语义
            ), coll_safety

        if op == "flatten":
            return CollectionRef(
                root_inst=coll_ref.root_inst, cnt_func=coll_ref.cnt_func, element_class=coll_ref.element_class,
                valid_instances=coll_ref.valid_instances, attr_func=coll_ref.attr_func, nav_chain=coll_ref.nav_chain,
                is_set_semantic=False  # flatten 强制转为 Bag 语义
            ), coll_safety

        if op == "count":
            if ast.arguments:
                arg_expr, arg_safety = self.translate(ast.arguments[0], var_bindings)
                cnt_terms = []
                for inst in coll_ref.valid_instances:
                    base_cnt = coll_ref.cnt_func(coll_ref.root_inst, inst)
                    actual_val, is_valid = _get_actual_val_for_coll(coll_ref, inst, arg_safety, base_cnt)
                    effective_cnt = If(is_valid, base_cnt, IntVal(0))  # 剔除 invalid
                    cnt_terms.append(If(_safe_eq(actual_val, arg_expr), effective_cnt, IntVal(0)))

                total = Sum(*cnt_terms) if cnt_terms else IntVal(0)
                return total, coll_safety + arg_safety


        if op in ["includesAll", "excludesAll"]:
            if not ast.arguments:
                raise ValueError(f"{op} operation requires an argument")
            arg_expr, arg_safety = self.translate(ast.arguments[0], var_bindings)
            if not isinstance(arg_expr, CollectionRef):
                raise ValueError(f"Semantic Error: {op} requires a collection as argument.")

            # === 核心修复：预求值与缓存 (Pre-computation & Caching) ===
            # 1. 以 O(N + M) 复杂度独立完成两侧集合真实值的提取
            # 2. 正确且仅一次地将所有深层闭包的 safety 条件冒泡至对应的 coll_safety / arg_safety

            coll_actuals = {}
            coll_is_valid = {}
            for coll_inst in coll_ref.valid_instances:
                coll_cnt = coll_ref.cnt_func(coll_ref.root_inst, coll_inst)
                actual_val, is_valid = _get_actual_val_for_coll(coll_ref, coll_inst, coll_safety, coll_cnt)
                coll_actuals[coll_inst] = actual_val
                coll_is_valid[coll_inst] = is_valid

            arg_actuals = {}
            arg_is_valid = {}
            for arg_inst in arg_expr.valid_instances:
                arg_cnt = arg_expr.cnt_func(arg_expr.root_inst, arg_inst)
                actual_val, is_valid = _get_actual_val_for_coll(arg_expr, arg_inst, arg_safety, arg_cnt)
                arg_actuals[arg_inst] = actual_val
                arg_is_valid[arg_inst] = is_valid
            conds = []

            # ==========================================
            if op == "includesAll":
                for arg_inst in arg_expr.valid_instances:
                    arg_actual = arg_actuals[arg_inst]

                    # 1. 计算该真实值在参数集合中的总频数
                    arg_match_terms = []
                    for inner_arg in arg_expr.valid_instances:
                        inner_actual = arg_actuals[inner_arg]
                        inner_cnt = arg_expr.cnt_func(arg_expr.root_inst, inner_arg)
                        effective_inner_cnt = If(arg_is_valid[inner_arg], inner_cnt, IntVal(0))
                        arg_match_terms.append(If(_safe_eq(inner_actual, arg_actual), effective_inner_cnt, IntVal(0)))
                    total_arg_cnt = Sum(*arg_match_terms) if arg_match_terms else IntVal(0)

                    # 2. 计算该真实值在主集合中的总频数
                    coll_match_terms = []
                    for coll_inst in coll_ref.valid_instances:
                        coll_actual = coll_actuals[coll_inst]
                        coll_cnt = coll_ref.cnt_func(coll_ref.root_inst, coll_inst)
                        effective_coll_cnt = If(coll_is_valid[coll_inst], coll_cnt, IntVal(0))
                        coll_match_terms.append(If(_safe_eq(coll_actual, arg_actual), effective_coll_cnt, IntVal(0)))
                    total_coll_cnt = Sum(*coll_match_terms) if coll_match_terms else IntVal(0)

                    # 3. 包含断言：主频数 >= 参数频数
                    conds.append(total_coll_cnt >= total_arg_cnt)

                return And(*conds) if conds else BoolVal(True), coll_safety + arg_safety

            # ==========================================
            elif op == "excludesAll":
                for arg_inst in arg_expr.valid_instances:
                    arg_actual = arg_actuals[arg_inst]
                    arg_cnt = arg_expr.cnt_func(arg_expr.root_inst, arg_inst)

                    coll_match_terms = []
                    for coll_inst in coll_ref.valid_instances:
                        coll_actual = coll_actuals[coll_inst]
                        coll_cnt = coll_ref.cnt_func(coll_ref.root_inst, coll_inst)
                        coll_match_terms.append(If(_safe_eq(coll_actual, arg_actual), coll_cnt, IntVal(0)))
                    total_coll_cnt = Sum(*coll_match_terms) if coll_match_terms else IntVal(0)

                    # 排斥断言：参数中存在的实例，在主集合的映射频数必须为 0
                    conds.append(Implies(arg_cnt > 0, total_coll_cnt == 0))

                return And(*conds) if conds else BoolVal(True), coll_safety + arg_safety

        if op in ["union", "intersection"]:
            if not ast.arguments:
                raise ValueError(f"{op} operation requires an argument")
            arg_expr, arg_safety = self.translate(ast.arguments[0], var_bindings)
            if not isinstance(arg_expr, CollectionRef):
                raise ValueError(f"{op} requires a collection as argument")

            # === 1. Set/Bag 语义判定 ===
            if op == "union":
                result_is_set = coll_ref.is_set_semantic and arg_expr.is_set_semantic
            else:  # intersection
                result_is_set = coll_ref.is_set_semantic or arg_expr.is_set_semantic

            # === 2. 基于 Z3 Sort 的实例域兼容性检查 ===
            left_insts = coll_ref.valid_instances
            right_insts = arg_expr.valid_instances

            # 边界情况：空集合
            if not left_insts:
                return CollectionRef(
                    root_inst=arg_expr.root_inst, cnt_func=arg_expr.cnt_func,
                    element_class=arg_expr.element_class, valid_instances=right_insts,
                    is_set_semantic=result_is_set
                ), coll_safety + arg_safety
            if not right_insts:
                return CollectionRef(
                    root_inst=coll_ref.root_inst, cnt_func=coll_ref.cnt_func,
                    element_class=coll_ref.element_class, valid_instances=left_insts,
                    is_set_semantic=result_is_set
                ), coll_safety + arg_safety

            left_sort = left_insts[0].sort()
            right_sort = right_insts[0].sort()

            # ---------- 场景 A：同构域（最常见，如同一 UML 类的实例） ----------
            if left_sort == right_sort:
                # 合并实例域并去重
                seen = set()
                final_instances = []
                for inst in (left_insts + right_insts):
                    inst_id = inst.get_id() if hasattr(inst, 'get_id') else id(inst)
                    if inst_id not in seen:
                        seen.add(inst_id)
                        final_instances.append(inst)

                # 确定最终的 element_class（处理 Integer/Real OCL提升）
                final_class = coll_ref.element_class
                if {coll_ref.element_class, arg_expr.element_class} == {"Integer", "Real"}:
                    final_class = "Real"

                # 同构域下，两个 cnt_func 接受相同的 Sort，绝对安全
                def merged_cnt(root, inst):
                    # 关键：每个 cnt_func 必须使用自己的 root_inst
                    root1 = coll_ref.root_inst if root is None else root
                    root2 = arg_expr.root_inst if root is None else root
                    cnt1 = coll_ref.cnt_func(root1, inst)
                    cnt2 = arg_expr.cnt_func(root2, inst)
                    if op == "union":
                        return If(cnt1 > cnt2, cnt1, cnt2) if result_is_set else (cnt1 + cnt2)
                    else:
                        return If(cnt1 < cnt2, cnt1, cnt2)

                return CollectionRef(
                    root_inst=None, cnt_func=merged_cnt,
                    element_class=final_class, valid_instances=final_instances,
                    is_set_semantic=result_is_set
                ), coll_safety + arg_safety

            # ---------- 场景 B：Int/Real 提升域（仅限 CollectionLiteral 数值合并） ----------
            elif {str(left_sort), str(right_sort)} == {"Int", "Real"}:
                final_class = "Real"
                # 安全转换：仅对 IntSort 实例做 ToReal，RealSort 保持原样
                final_instances = []
                for inst in left_insts:
                    final_instances.append(ToReal(inst) if is_int(inst) else inst)
                for inst in right_insts:
                    final_instances.append(ToReal(inst) if is_int(inst) else inst)
                # 去重
                seen = set()
                unique_instances = []
                for inst in final_instances:
                    key = str(inst)
                    if key not in seen:
                        seen.add(key)
                        unique_instances.append(inst)

                # CollectionLiteral 的 cnt_func 通常是 literal_cnt（忽略 inst 参数）
                # 但为防御性编程，对原来是 IntSort 的 cnt_func，需包装桥接
                def safe_numeric_cnt(orig_cnt_func, orig_root, orig_sort, root, inst):
                    if orig_sort == IntSort() and is_real(inst):
                        return If(IsInt(inst), orig_cnt_func(orig_root, ToInt(inst)), IntVal(0))
                    return orig_cnt_func(orig_root, inst)

                left_root = coll_ref.root_inst
                right_root = arg_expr.root_inst

                def merged_cnt_literal(root, inst):
                    cnt1 = safe_numeric_cnt(coll_ref.cnt_func, left_root, left_sort, root, inst)
                    cnt2 = safe_numeric_cnt(arg_expr.cnt_func, right_root, right_sort, root, inst)
                    if op == "union":
                        return If(cnt1 > cnt2, cnt1, cnt2) if result_is_set else (cnt1 + cnt2)
                    else:
                        return If(cnt1 < cnt2, cnt1, cnt2)

                return CollectionRef(
                    root_inst=None, cnt_func=merged_cnt_literal,
                    element_class=final_class, valid_instances=unique_instances,
                    is_set_semantic=result_is_set
                ), coll_safety + arg_safety

            # ---------- 场景 C：异构域（如 Set(Dog) union Set(Cat)） ----------
            else:
                raise ValueError(
                    f"Z3 Compilation Error: Cannot perform {op} on collections with "
                    f"incompatible Z3 sorts ({left_sort} vs {right_sort}). "
                    f"Cross-type collection algebra is not supported in the verification subset."
                )

        raise NotImplementedError(f"Collection operation not implemented: {op}")

    #Tools
    def _eval_body_with_var(self, body_ast, var_name, inst, element_class, var_bindings):
        new_bindings = var_bindings.copy()
        new_bindings[var_name] = inst
        new_bindings[var_name + "_type"] = element_class
        body_expr, body_safety = self.translate(body_ast, new_bindings)

        # 关键修复：不再将 safety 乘入 body_expr！
        # 闭包求值若触发 invalid，让 combined_safety 冒泡即可，body_expr 保留原值（作为无意义的垃圾值被外层忽略）
        combined_safety = And(*body_safety) if body_safety else BoolVal(True)

        return body_expr, combined_safety

    def _eval_body_with_vars(self, body_ast, var_names, inst_tuple, element_class, var_bindings):
        new_bindings = var_bindings.copy()
        for var_name, inst in zip(var_names, inst_tuple):
            new_bindings[var_name] = inst
            new_bindings[var_name + "_type"] = element_class
        body_expr, body_safety = self.translate(body_ast, new_bindings)

        # 关键修复：彻底分离 value 和 safety
        combined_safety = And(*body_safety) if body_safety else BoolVal(True)

        return body_expr, combined_safety

    def _resolve_collection_source(self, source_ast, var_bindings) -> Tuple[CollectionRef, List]:
        src_result, coll_safety = self.translate(source_ast, var_bindings)
        if isinstance(src_result, CollectionRef):
            return src_result, coll_safety
        src_type_name = "Unknown"
        if hasattr(src_result, 'sort'):
            src_type_name = str(src_result.sort())
        raise ValueError(
            f"Semantic Error: Arrow operator (->) used on a non-collection value ({src_type_name}). "
            f"Use dot syntax (.) for single objects. "
            f"AST Source Type: {source_ast.type}"
        )

    def _compute_size(self, coll_ref: CollectionRef) -> Any:
        terms = []
        for inst in coll_ref.valid_instances:
            cnt = coll_ref.cnt_func(coll_ref.root_inst, inst)
            terms.append(cnt)
        return Sum(*terms) if terms else IntVal(0)

    def _compute_sum(self, coll_ref: CollectionRef) -> Tuple[Any, List]:
        if coll_ref.attr_func is None:
            raise ValueError("Cannot sum collection without attribute function or collect body")

        attr_func = coll_ref.attr_func

        if isinstance(attr_func, tuple) and attr_func[0] == "collect_body":
            _, body_ast, var_name, elem_class, saved_bindings = attr_func
            terms = []
            sum_safety_acc = []
            for inst in coll_ref.valid_instances:
                cnt = coll_ref.cnt_func(coll_ref.root_inst, inst)
                body_val, body_safety_ref = self._eval_body_with_var(body_ast, var_name, inst, elem_class,
                                                                     saved_bindings)

                if not (is_int(body_val) or is_real(body_val)):
                    raise ValueError("Z3 Compilation Error: ->sum() requires numeric values...")

                max_cnt = 1 if coll_ref.is_set_semantic else self.me.scope
                # 核心修复：若闭包体 invalid，有效计数降为 0（即剔除），而非爆炸
                valid_multiplier = If(body_safety_ref, IntVal(1), IntVal(0))
                safe_cnt = cnt * valid_multiplier
                term = self._linear_multiply(safe_cnt, body_val, max_cnt)
                terms.append(term)

                # 修复：不再追加 Implies(cnt > 0, body_safety_ref)，invalid 被静默剔除
            return Sum(*terms) if terms else IntVal(0), sum_safety_acc

        # 然后再检查 callable（FuncDeclRef）
        if not callable(attr_func):
            raise RuntimeError(
                f"Z3 Translator Internal Error: attr_func has unexpected type {type(attr_func).__name__}. "
                f"This is a translator bug, not an AST error."
            )

        # 正常的 FuncDeclRef 路径
        terms = []
        sum_safety_acc = []
        for inst in coll_ref.valid_instances:
            cnt = coll_ref.cnt_func(coll_ref.root_inst, inst)
            nav_val = inst
            for nav_func in coll_ref.nav_chain:
                if not callable(nav_func): raise RuntimeError(...)
                nav_val = nav_func(nav_val)

            attr_val = attr_func(nav_val)
            max_cnt = 1 if coll_ref.is_set_semantic else self.me.scope

            # 核心修复：剔除 invalid 而非爆炸
            null_c = self.me.sort_to_null.get(nav_val.sort())
            if null_c is not None:
                term = If(nav_val != null_c, self._linear_multiply(cnt, attr_val, max_cnt), IntVal(0))
            else:
                term = self._linear_multiply(cnt, attr_val, max_cnt)
            terms.append(term)
        return Sum(*terms) if terms else IntVal(0), sum_safety_acc

    def _infer_class_name(self, ast: OCLExpression, bindings: Dict[str, Any]) -> str:
        if ast.type == "Variable":
            if ast.name == "self":
                return bindings.get("context_class", "Unknown")
            if ast.name + "_type" in bindings:
                return bindings[ast.name + "_type"]
            # 缺陷 2 修复：检查是否为全局类名调用
            if ast.name in self.me.uml_context:
                return ast.name
            return "Unknown"

        elif ast.type == "PropertyCall":
            owner_class = self._infer_class_name(ast.source, bindings)
            return self._get_element_class_name(owner_class, ast.property_name)

        elif ast.type == "OperationCall":
            if ast.operation_name == "allInstances":
                return self._infer_class_name(ast.source, bindings)
            if ast.operation_name in ["isDefined", "oclIsUndefined"]:
                return "Boolean"
            if ast.operation_name == "abs":
                return self._infer_class_name(ast.source, bindings)
            return self._infer_class_name(ast.source, bindings)

        elif ast.type == "IteratorExpression":
            if ast.iterator_type in ["forAll", "exists", "isUnique"]:
                return "Boolean"
            if ast.iterator_type in ["select", "reject"]:
                return self._infer_class_name(ast.source, bindings)
            if ast.iterator_type == "collect":
                return self._infer_class_name(ast.body, bindings)
            return self._infer_class_name(ast.source, bindings)

        elif ast.type == "CollectionOperation":
            if ast.operation_type in ["size", "count"]:
                return "Integer"
            if ast.operation_type in ["isEmpty", "notEmpty", "includes", "excludes"]:
                return "Boolean"
            if ast.operation_type == "sum":
                return "Real"
            return self._infer_class_name(ast.source, bindings)

        elif ast.type == "BinaryExpression":
            if ast.operator in ['and', 'or', 'implies', 'xor']:
                return "Boolean"
            if ast.operator in ['=', '<>', '<', '<=', '>', '>=']:
                return "Boolean"
            if ast.operator in ['+', '-', '*', '/']:
                return self._infer_class_name(ast.left, bindings)
            return "Unknown"

        elif ast.type == "UnaryExpression":
            if ast.operator == "not":
                return "Boolean"
            return self._infer_class_name(ast.expression, bindings)

        elif ast.type == "LiteralExpression":
            return ast.literal_type

        elif ast.type == "IfExpression":
            return self._infer_class_name(ast.then_expr, bindings)

        elif ast.type == "LetExpression":
            return self._infer_class_name(ast.body, bindings)

        return "Unknown"

    def _get_element_class_name(self, owner_class: str, prop_name: str) -> str:
        uml_ctx = self.me.uml_context.get(owner_class, {})

        assoc_type = uml_ctx.get("associations", {}).get(prop_name, "")
        if assoc_type:
            match = re.search(r'\((\w+)\)', assoc_type)
            if match:
                return match.group(1)
            match_opt = re.match(r'(\w+)\[', assoc_type)
            if match_opt:
                return match_opt.group(1)
            # 缺陷 4 修复：兜底提取
            return re.sub(r'[^a-zA-Z0-9_]', '', assoc_type)

        attr_type = uml_ctx.get("attributes", {}).get(prop_name, "")
        if attr_type:
            return attr_type
        return "Unknown"

    def _apply_arithmetic(self, op, left, right):
        if is_real(left) and is_int(right):
            right = ToReal(right)
        elif is_int(left) and is_real(right):
            left = ToReal(left)
        if op == '+': return left + right
        if op == '-': return left - right
        if op == '*': return left * right
        raise NotImplementedError(f"Arithmetic op: {op}")

    def _apply_relational(self, op, left, right):
        if is_real(left) and is_int(right):
            right = ToReal(right)
        elif is_int(left) and is_real(right):
            left = ToReal(left)
        if op == '=': return left == right
        if op == '<>': return left != right
        if op == '<': return left < right
        if op == '<=': return left <= right
        if op == '>': return left > right
        if op == '>=': return left >= right
        raise NotImplementedError(f"Relational op: {op}")

    def _linear_multiply(self, cnt: Any, val: Any, max_cnt: int) -> Any:
        """
        将符号整数 cnt 与 Z3 值 val 相乘，展开为条件加法，避免非线性算术。
        假设 cnt 的范围是 [0, max_cnt]。
        """
        # 1. 严格的 Sort 匹配，拒接非法类型
        if is_real(val):
            zero = RealVal(0)
        elif is_int(val):
            zero = IntVal(0)
        else:
            raise ValueError(
                f"Z3 Compilation Error: Cannot perform linear multiplication on non-numeric sort {val.sort()}."
            )

        # 2. 边界裁剪
        if max_cnt <= 0:
            return zero

        # 3. 针对 Set 语义 (max_cnt == 1) 的极速优化
        # 使用 cnt > 0 比 cnt == 1 更具防御性
        if max_cnt == 1:
            return If(cnt > 0, val, zero)

        # 4. 一般 Bag 语义的线性展开 (例如 max_cnt = 3)
        terms = []
        for i in range(1, max_cnt + 1):
            terms.append(If(cnt >= i, val, zero))

        return Sum(*terms)

# ==========================================
# 组件 3 & 4：基于蕴含关系的定性分级判定
# ==========================================

def check_equivalence(gt_expr, llm_expr, meta_encoder, context_class, self_var, case_key: str, constraint_name: str) -> dict:
    """基于 Z3 蕴含关系判定，返回结构化结果（含反例）"""
    null_const = meta_encoder.null_consts[context_class]
    gt_forall = ForAll([self_var], Implies(self_var != null_const, gt_expr))
    llm_forall = ForAll([self_var], Implies(self_var != null_const, llm_expr))

    dump_formula(case_key, constraint_name, "GT_Quantified_Axiom", gt_forall)
    dump_formula(case_key, constraint_name, "LLM_Quantified_Axiom", llm_forall)

    s = Solver()
    s.add(meta_encoder.axioms)

    # 判定 1: 寻找 LLM 是否排除了 GT 的合法状态 (即 LLM 更严格/强化)
    # 逻辑条件：GT 成立 且 LLM 不成立
    s.push()
    s.add(gt_forall)
    s.add(Not(llm_forall))
    is_llm_stricter = (s.check() == sat)
    # 修正配套：更严格对应强化反例
    strengthened_ce = extract_counterexample(s, meta_encoder, context_class, self_var) if is_llm_stricter else None
    s.pop()

    # 判定 2: 寻找 LLM 是否放行了 GT 的非法状态 (即 LLM 更宽松/弱化)
    # 逻辑条件：LLM 成立 且 GT 不成立
    s.push()
    s.add(llm_forall)
    s.add(Not(gt_forall))
    is_llm_looser = (s.check() == sat)
    # 修正配套：更宽松对应弱化反例
    weakened_ce = extract_counterexample(s, meta_encoder, context_class, self_var) if is_llm_looser else None
    s.pop()

    # 定性分级
    if not is_llm_stricter and not is_llm_looser:
        result = "EQUIVALENT"
    elif is_llm_stricter and not is_llm_looser:
        result = "STRENGTHENED"  # LLM 约束更强，排除了合法状态
    elif not is_llm_stricter and is_llm_looser:
        result = "WEAKENED"  # LLM 约束更弱，放行了非法状态
    else:
        result = "INCOMPARABLE"

    return {
        "result": result,
        "score": {"EQUIVALENT": 100, "STRENGTHENED": 60, "WEAKENED": 40, "INCOMPARABLE": 0}[result],
        "weakened_counterexample": weakened_ce,
        "strengthened_counterexample": strengthened_ce
    }

# ==========================================
# 主控流水线
# ==========================================
def evaluate_constraint(gt_ast: OCLExpression, llm_ast: OCLExpression, uml_context: dict, context_class: str, case_key: str, constraint_name: str) -> dict:
    """
    评估 GT 与 LLM 约束的等价性，返回包含判定结果、分数和反例的结构化字典。
    """
    # 1. 预检：防御性隔离，确保 LLM 的 AST 可翻译
    is_translatable, err_msg = check_z3_translatable(llm_ast, uml_context, context_class)
    if not is_translatable:
        # 编译失败，逻辑必然不等价，直接返回 0 分及空反例
        return {
            "result": "INCOMPARABLE",
            "score": 0.0,
            "weakened_counterexample": None,
            "strengthened_counterexample": None,
            "compilation_error": err_msg  # 附带编译错误信息供主程序参考
        }

    meta_encoder = BoundedMetamodelEncoder(uml_context, scope=3)

    self_var = Const("self", meta_encoder.sorts[context_class])
    var_bindings = {"context_class": context_class, "self": self_var}

    translator = OCLZ3Translator(meta_encoder)
    gt_expr, gt_safety = translator.translate(gt_ast, var_bindings)
    llm_expr, llm_safety = translator.translate(llm_ast, var_bindings)
    null_const = meta_encoder.null_consts[context_class]

    if gt_safety:
        s_safety = Solver()
        s_safety.add(meta_encoder.axioms)
        s_safety.add(self_var != null_const)  # 仅在 self 有效时讨论约束语义
        s_safety.add(Not(And(*gt_safety)))  # 尝试寻找违反安全条件的模型 (即触发 Invalid 的路径)

        # 如果 Z3 找到了使 GT 不安全的模型，说明 GT 自身存在 Null/Invalid 解引用
        if s_safety.check() == sat:
            return {
                "result": "INCOMPARABLE",
                "score": 0.0,
                "weakened_counterexample": None,
                "strengthened_counterexample": None,
                "compilation_error": "Unsafe GT: Ground Truth contains potential null/invalid dereference. Equivalence is semantically undefined."
            }

    # 终极收口：将顶层残留安全条件合取注入
    if gt_safety:
        gt_expr = And(And(*gt_safety), gt_expr)
    if llm_safety:
        llm_expr = And(And(*llm_safety), llm_expr)

    dump_formula(case_key, constraint_name, "GT_Translated_Expr", gt_expr)
    dump_formula(case_key, constraint_name, "LLM_Translated_Expr", llm_expr)

    null_const = meta_encoder.null_consts[context_class]
    s_pre = Solver()
    s_pre.add(meta_encoder.axioms)
    s_pre.add(ForAll([self_var], Implies(self_var != null_const, gt_expr)))
    if s_pre.check() == unsat:
        return {
            "result": "INCOMPARABLE",
            "score": 0.0,
            "weakened_counterexample": None,
            "strengthened_counterexample": None,
            "compilation_error": "Vacuous Truth: GT is UNSAT within bounded scope. Increase scope or skip."
        }

    # 5. 基于蕴含关系的定性分级判定（直接返回字典）
    return check_equivalence(gt_expr, llm_expr, meta_encoder, context_class, self_var,case_key, constraint_name)

def check_z3_translatable(llm_ast: OCLExpression, uml_context: dict, context_class: str) -> tuple:
    try:
        meta_encoder = BoundedMetamodelEncoder(uml_context, scope=1)
        self_var = Const("self", meta_encoder.sorts[context_class])
        var_bindings = {"context_class": context_class, "self": self_var}
        translator = OCLZ3Translator(meta_encoder)
        translator.translate(llm_ast, var_bindings)
        return True, None
    except RuntimeError:
        raise  # 翻译器 Bug，必须崩溃，绝不能反馈给 LLM
    except Exception as e:
        import traceback
        traceback.print_exc()
        return False, f"Z3 Compilation Error: {type(e).__name__}: {e}"


def extract_counterexample(solver: Solver, meta_encoder: BoundedMetamodelEncoder,
                           context_class: str, self_var) -> str:
    """从 Z3 sat 的 solver 中提取人类可读的反例状态描述"""
    model = solver.model()

    # 1. 确定 self 的具体值
    self_val = model.eval(self_var, model_completion=True)
    lines = [f"Counter-example state: self = {self_val}"]

    # 2. 遍历当前 self 的所有属性值
    sort = meta_encoder.sorts[context_class]
    cls_info = meta_encoder.uml_context.get(context_class, {})

    for attr_name, attr_type in cls_info.get("attributes", {}).items():
        func_key = f"{context_class}.{attr_name}"
        if func_key in meta_encoder.attr_funcs:
            val = model.eval(meta_encoder.attr_funcs[func_key](self_val), model_completion=True)
            lines.append(f"  self.{attr_name} = {val}")

    # 3. 遍历当前 self 的所有关联
    for assoc_name, assoc_type in cls_info.get("associations", {}).items():
        func_key = f"{context_class}.{assoc_name}"
        if func_key in meta_encoder.assoc_funcs:
            meta = meta_encoder.assoc_meta[func_key]
            if meta["is_count"]:
                # 集合关联：报告每个目标实例的计数
                parts = []
                for tgt_inst in meta_encoder.get_valid_instances(meta["tgt_class"]):
                    cnt = model.eval(
                        meta_encoder.assoc_funcs[func_key](self_val, tgt_inst),
                        model_completion=True
                    )
                    if is_int_value(cnt):
                        cnt_int = cnt.as_long()
                    else:
                        cnt_int = str(cnt)
                    if cnt_int != 0:
                        parts.append(f"{tgt_inst}(count={cnt_int})")
                if parts:
                    lines.append(f"  self.{assoc_name}: {', '.join(parts)}")
            else:
                # 单值关联：报告导航目标
                tgt_val = model.eval(
                    meta_encoder.assoc_funcs[func_key](self_val),
                    model_completion=True
                )
                lines.append(f"  self.{assoc_name} = {tgt_val}")

    return "\n".join(lines)
