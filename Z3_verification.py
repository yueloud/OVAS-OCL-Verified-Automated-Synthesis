import re
import itertools
from typing import Dict, List, Tuple, Any
from z3 import *
from json_schema import (OCLExpression, PropertyCall, OperationCall, BinaryExpression,
                         IteratorExpression, CollectionOperation, LiteralExpression,
                         IfExpression, UnaryExpression, LetExpression, CollectionLiteral)


# ==========================================
# 集合引用标记类
# ==========================================
class CollectionRef:
    """标记类：代表 Z3 编码管线中的集合引用。"""

    def __init__(self, root_inst, cnt_func, element_class, valid_instances,
                 attr_func=None, nav_chain=None):
        self.root_inst = root_inst
        self.cnt_func = cnt_func
        self.element_class = element_class
        self.valid_instances = valid_instances
        self.attr_func = attr_func
        self.nav_chain = nav_chain or []


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
                match_coll = re.match(r'(Set|Bag|Sequence|OrderedSet)\((\w+)\)', assoc_type)
                match_opt = re.match(r'(\w+)\[0\.\.1]', assoc_type)
                match_req = re.match(r'(\w+)\[1\.\.1]', assoc_type)
                func_key = f"{class_name}.{assoc_name}"

                if match_coll:
                    tgt_name = match_coll.group(2)
                    tgt_sort = self.sorts[tgt_name]
                    self.assoc_funcs[func_key] = Function(
                        f'{class_name}_{assoc_name}_cnt', src_sort, tgt_sort, IntSort())
                    self.assoc_meta[func_key] = {
                        "src_class": class_name, "tgt_class": tgt_name,
                        "is_count": True, "is_mandatory": False}
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

        # 铁律 1: Null 哨兵全局公理
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
            else:
                self.axioms.append(func(src_null) == tgt_null)
                # 铁律 4: [1..1] 关联非空全局约束
                if meta["is_mandatory"]:
                    for src_inst in self.get_valid_instances(meta["src_class"]):
                        self.axioms.append(
                            Implies(src_inst != src_null, func(src_inst) != tgt_null))

    def get_valid_instances(self, class_name: str) -> List[Any]:
        sort = self.sorts[class_name]
        # 零参数构造器：getattr 返回的已是 DatatypeRef 实例，不需要再调用 ()
        return [getattr(sort, f'{class_name.lower()}_{i}') for i in range(self.scope)]

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

        elif node_type == "PropertyCall":
            return self._handle_property_call(ast, var_bindings)

        elif node_type == "BinaryExpression":
            return self._handle_binary_expr(ast, var_bindings)

        elif node_type == "UnaryExpression":
            return self._handle_unary_expr(ast, var_bindings)

        elif node_type == "OperationCall":
            return self._handle_operation_call(ast, var_bindings)

        elif node_type == "IteratorExpression":
            return self._handle_iterator(ast, var_bindings)

        elif node_type == "CollectionOperation":
            return self._handle_collection_op(ast, var_bindings)

        elif node_type == "IfExpression":
            return self._handle_if_expr(ast, var_bindings)

        elif node_type == "LetExpression":
            return self._handle_let_expr(ast, var_bindings)

        elif node_type == "TypeCast":
            return self.translate(ast.expression, var_bindings)

        elif node_type == "CollectionLiteral":
            return self._handle_collection_literal(ast, var_bindings)

        raise NotImplementedError(f"AST node type not implemented: {node_type}")

    # ---------- LiteralExpression ----------
    def _handle_literal(self, ast: LiteralExpression) -> Tuple[Any, List]:
        val = ast.value
        lt = ast.literal_type
        if lt == "Integer": return IntVal(val), []
        if lt == "Real": return RealVal(val), []
        if lt == "Boolean": return BoolVal(val), []
        if lt == "String": return StringVal(str(val)), []
        if lt == "Null": return None, []
        return IntVal(0), []

    # ---------- PropertyCall ----------
    def _handle_property_call(self, ast: PropertyCall, var_bindings: Dict) -> Tuple[Any, List]:
        src_result, src_safety = self.translate(ast.source, var_bindings)

        # 隐式 collect: source 是集合，在其上导航属性
        if isinstance(src_result, CollectionRef):
            return self._handle_implicit_collect(src_result, ast.property_name, src_safety)

        src_expr = src_result
        src_type_name = self._infer_class_name(ast.source, var_bindings)
        func_key = f"{src_type_name}.{ast.property_name}"

        # 关联导航
        if func_key in self.me.assoc_funcs:
            func = self.me.assoc_funcs[func_key]
            meta = self.me.assoc_meta[func_key]

            # 缺陷 3 修复：Sort Mismatch 检查
            if src_expr.sort() != func.domain(0):
                raise ValueError(
                    f"Z3 Sort Mismatch: Cannot apply {func_key} (domain: {func.domain(0)}) "
                    f"to source expression of sort {src_expr.sort()}. "
                    f"This indicates a critical type inference bug in the translator or semantic firewall."
                )
            if meta["is_count"]:
                valid_instances = self.me.get_valid_instances(meta["tgt_class"])
                return CollectionRef(
                    root_inst=src_expr, cnt_func=func,
                    element_class=meta["tgt_class"],
                    valid_instances=valid_instances), src_safety
            else:
                result = func(src_expr)
                tgt_null = self.me.null_consts[meta["tgt_class"]]
                if not meta["is_mandatory"]:
                    return result, src_safety + [result != tgt_null]
                else:
                    return result, src_safety

        # 属性访问
        if func_key in self.me.attr_funcs:
            func = self.me.attr_funcs[func_key]

            # 缺陷 3 修复：Sort Mismatch 检查
            if src_expr.sort() != func.domain(0):
                raise ValueError(
                    f"Z3 Sort Mismatch: Cannot apply {func_key} (domain: {func.domain(0)}) "
                    f"to source expression of sort {src_expr.sort()}. "
                    f"This indicates a critical type inference bug in the translator or semantic firewall."
                )

            return func(src_expr), src_safety

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
                nav_chain=coll_ref.nav_chain), src_safety

        if func_key in self.me.assoc_funcs:
            func = self.me.assoc_funcs[func_key]
            meta = self.me.assoc_meta[func_key]

            if not meta["is_count"]:
                # 立刻进行目标类型投影，废弃失效的 nav_chain
                tgt_class = meta["tgt_class"]
                tgt_instances = self.me.get_valid_instances(tgt_class)

                def mapped_cnt(root, tgt_elem):
                    total = IntVal(0)
                    for src_elem in coll_ref.valid_instances:
                        # 解析历史上可能残留的 nav_chain
                        nav_val = src_elem
                        for nav_func in coll_ref.nav_chain:
                            nav_val = nav_func(nav_val)

                        nav_val = func(nav_val)  # 执行本次导航
                        src_cnt = coll_ref.cnt_func(coll_ref.root_inst if root is None else root, src_elem)
                        # 如果导航结果命中目标元素，则累加源计数
                        total = total + If(nav_val == tgt_elem, src_cnt, IntVal(0))
                    return total

                return CollectionRef(
                    root_inst=coll_ref.root_inst, cnt_func=mapped_cnt,
                    element_class=tgt_class, valid_instances=tgt_instances,
                    nav_chain=[]  # 导航链已被消化
                ), src_safety
            else:
                return self._handle_nested_collection(coll_ref, func_key, meta, src_safety)

        raise ValueError(f"Unknown property in implicit collect: {func_key}")

    def _handle_nested_collection(self, parent_ref: CollectionRef,
                                  func_key: str, meta: Dict, src_safety: List) -> Tuple[Any, List]:
        """处理嵌套集合 (如 self.rooms.beds)"""
        sub_cnt_func = self.me.assoc_funcs[func_key]
        sub_element_class = meta["tgt_class"]
        sub_valid_instances = self.me.get_valid_instances(sub_element_class)

        def combined_cnt(root, sub_elem):
            total = IntVal(0)
            for parent_elem in parent_ref.valid_instances:
                parent_cnt = parent_ref.cnt_func(
                    parent_ref.root_inst if root is None else root, parent_elem)
                sub_cnt = sub_cnt_func(parent_elem, sub_elem)
                total = total + parent_cnt * sub_cnt
            return total

        return CollectionRef(
            root_inst=None, cnt_func=combined_cnt,
            element_class=sub_element_class,
            valid_instances=sub_valid_instances), src_safety

    # ---------- BinaryExpression ----------
    def _handle_binary_expr(self, ast: BinaryExpression, var_bindings: Dict) -> Tuple[Any, List]:
        left, left_safety = self.translate(ast.left, var_bindings)
        right, right_safety = self.translate(ast.right, var_bindings)
        op = ast.operator

        # 铁律 7: 除法的严格评估范式与 OCL Real 提升强制约
        if op == '/':
            if is_int(left): left = ToReal(left)
            if is_int(right): right = ToReal(right)
            return left / right, left_safety + right_safety + [right != 0]

        if op in ['+', '-', '*']:
            return self._apply_arithmetic(op, left, right), left_safety + right_safety

        # 关系算子：两边都必须有效（直接相加冒泡）
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

    # ---------- UnaryExpression ----------
    def _handle_unary_expr(self, ast: UnaryExpression, var_bindings: Dict) -> Tuple[Any, List]:
        expr, safety = self.translate(ast.expression, var_bindings)
        if ast.operator == "not":
            # 终极修复：直接透传 safety，防止 not(invalid) 被错误反转为 True
            return Not(expr), safety
        elif ast.operator == "-":
            return -expr, safety
        raise NotImplementedError(f"Unary operator: {ast.operator}")

    # ---------- OperationCall ----------
    def _handle_operation_call(self, ast: OperationCall, var_bindings: Dict) -> Tuple[Any, List]:
        op = ast.operation_name

        # === 第一类：不需要翻译 source 的操作 ===
        if op == "allInstances":
            if ast.source.type == "Variable" and ast.source.name in self.me.uml_context:
                element_class = ast.source.name
            else:
                element_class = self._infer_class_name(ast.source, var_bindings)
            valid_instances = self.me.get_valid_instances(element_class)
            return CollectionRef(
                root_inst=None,
                cnt_func=lambda root, inst: IntVal(1),
                element_class=element_class,
                valid_instances=valid_instances), []

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
        if op == "oclAsType":
            return src_expr, src_safety
        if op == "oclIsKindOf":
            return BoolVal(True), src_safety
        if op == "toString":
            return StringVal(""), src_safety

        raise NotImplementedError(f"Operation not implemented: {op}")

    # ---------- IteratorExpression ----------
    # ---------- IteratorExpression ----------
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
                accumulated_body_safety.append(body_safety_ref)

                in_set = coll_ref.cnt_func(coll_ref.root_inst, inst) > 0
                if ast.iterator_type == "forAll":
                    results.append(Implies(in_set, body_val))
                elif ast.iterator_type == "exists":
                    results.append(And(in_set, body_val))

            final_safety = coll_safety + accumulated_body_safety
            if ast.iterator_type == "forAll":
                return And(*results), final_safety
            elif ast.iterator_type == "exists":
                return Or(*results), final_safety

        # ========== one：代数求和逻辑（Bag 语义修正） ==========
        elif ast.iterator_type == "one":
            cnt_terms = []
            for inst in coll_ref.valid_instances:
                cnt = coll_ref.cnt_func(coll_ref.root_inst, inst)
                body_val, body_safety_ref = self._eval_body_with_var(
                    ast.body, iter_var_name, inst, element_class, var_bindings)
                accumulated_body_safety.append(body_safety_ref)
                # 满足条件的实例，累加其实际数量；否则累加 0
                cnt_terms.append(If(And(cnt > 0, body_val), cnt, IntVal(0)))

            total_matches = Sum(*cnt_terms) if cnt_terms else IntVal(0)
            final_safety = coll_safety + accumulated_body_safety
            return total_matches == 1, final_safety

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
                accumulated_body_safety.append(body_safety_ref)
                body_vals[inst] = body_val

            def filtered_cnt(root, inst):
                base_cnt = coll_ref.cnt_func(coll_ref.root_inst if root is None else root, inst)
                b_val = body_vals.get(inst, BoolVal(False))
                if ast.iterator_type == "select":
                    return If(And(base_cnt > 0, b_val), base_cnt, IntVal(0))
                else:
                    return If(And(base_cnt > 0, Not(b_val)), base_cnt, IntVal(0))

            final_safety = coll_safety + accumulated_body_safety
            return CollectionRef(
                root_inst=coll_ref.root_inst,
                cnt_func=filtered_cnt,
                element_class=element_class,
                valid_instances=coll_ref.valid_instances,
                attr_func=coll_ref.attr_func,
                nav_chain=coll_ref.nav_chain), final_safety

        # ========== collect ==========
        elif ast.iterator_type == "collect":
            for inst in coll_ref.valid_instances:
                _, body_safety_ref = self._eval_body_with_var(
                    ast.body, iter_var_name, inst, element_class, var_bindings)
                accumulated_body_safety.append(body_safety_ref)

            final_safety = coll_safety + accumulated_body_safety
            return CollectionRef(
                root_inst=coll_ref.root_inst,
                cnt_func=coll_ref.cnt_func,
                element_class=element_class,
                valid_instances=coll_ref.valid_instances,
                attr_func=("collect_body", ast.body, iter_var_name, element_class, var_bindings),
                nav_chain=coll_ref.nav_chain), final_safety

        # ========== any ==========
        elif ast.iterator_type == "any":
            null_const = self.me.null_consts.get(element_class)
            res_expr = null_const if null_const is not None else self.me._default_value_for_sort(
                self.me._z3_sort(element_class))

            body_vals = {}
            for inst in coll_ref.valid_instances:
                body_val, body_safety_ref = self._eval_body_with_var(
                    ast.body, iter_var_name, inst, element_class, var_bindings)
                accumulated_body_safety.append(body_safety_ref)
                body_vals[inst] = body_val

            for inst in reversed(coll_ref.valid_instances):
                b_val = body_vals[inst]
                in_set = coll_ref.cnt_func(coll_ref.root_inst, inst) > 0
                res_expr = If(And(in_set, b_val), inst, res_expr)

            final_safety = coll_safety + accumulated_body_safety
            return res_expr, final_safety

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

                accumulated_body_safety.append(body_safety_ref)

                if iter_type == "forAll":
                    results.append(Implies(in_set, body_val))
                elif iter_type == "exists":
                    results.append(And(in_set, body_val))

            final_safety = coll_safety + accumulated_body_safety

            if iter_type == "forAll":
                return And(*results), final_safety
            elif iter_type == "exists":
                return Or(*results), final_safety

        # ========== one：代数求和逻辑（Bag 语义修正） ==========
        elif iter_type == "one":
            cnt_terms = []
            for inst_tuple in itertools.product(coll_ref.valid_instances, repeat=n_vars):
                in_set_conditions = []
                tuple_cnt = IntVal(1)  # 计算当前组合在多重集中出现的总次数
                for inst in inst_tuple:
                    cnt = coll_ref.cnt_func(coll_ref.root_inst, inst)
                    in_set_conditions.append(cnt > 0)
                    tuple_cnt = tuple_cnt * cnt  # 乘积累积

                # 组合存在的布尔条件
                in_set = And(*in_set_conditions) if len(in_set_conditions) > 1 else in_set_conditions[0]

                body_val, body_safety_ref = self._eval_body_with_vars(
                    ast.body, iter_vars, inst_tuple, element_class, var_bindings)

                accumulated_body_safety.append(body_safety_ref)

                # 满足条件的组合，累加其实际出现次数；否则累加 0
                cnt_terms.append(If(And(in_set, body_val), tuple_cnt, IntVal(0)))

            total_matches = Sum(*cnt_terms) if cnt_terms else IntVal(0)
            final_safety = coll_safety + accumulated_body_safety
            return total_matches == 1, final_safety

        # ========== isUnique ==========
        elif iter_type == "isUnique":
            # isUnique 需要预计算所有元组的 body_val 和 safety
            tuples = list(itertools.product(coll_ref.valid_instances, repeat=n_vars))
            body_vals = {}
            for t in tuples:
                body_val, body_safety_ref = self._eval_body_with_vars(
                    ast.body, iter_vars, t, element_class, var_bindings)
                accumulated_body_safety.append(body_safety_ref)
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
            accumulated_body_safety.append(body_safety_ref)
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

    def _eval_body_with_var(self, body_ast, var_name, inst, element_class, var_bindings):
        new_bindings = var_bindings.copy()
        new_bindings[var_name] = inst
        new_bindings[var_name + "_type"] = element_class
        body_expr, body_safety = self.translate(body_ast, new_bindings)

        # 关键修复：不再在此处合并 safety，而是原样返回，交由迭代器统一处理
        combined_safety = And(*body_safety) if body_safety else BoolVal(True)
        if is_bool(body_expr):
            return And(combined_safety, body_expr), combined_safety
        else:
            return body_expr, combined_safety

    def _eval_body_with_vars(self, body_ast, var_names, inst_tuple, element_class, var_bindings):
        new_bindings = var_bindings.copy()
        for var_name, inst in zip(var_names, inst_tuple):
            new_bindings[var_name] = inst
            new_bindings[var_name + "_type"] = element_class

        body_expr, body_safety = self.translate(body_ast, new_bindings)

        # 关键修复：不再在此处合并 safety，而是原样返回，交由迭代器统一处理
        combined_safety = And(*body_safety) if body_safety else BoolVal(True)

        # 只有当 body 是布尔表达式时，才用 safety 条件做 And 守卫
        # 如果 body 是算术/对象表达式（如 collect 体中的 t.amount），
        # And(BoolRef, ArithRef) 会触发 Z3 类型坍塌
        if is_bool(body_expr):
            return And(combined_safety, body_expr), combined_safety
        else:
            return body_expr, combined_safety

    # ---------- CollectionOperation ----------
    def _handle_collection_op(self, ast: CollectionOperation, var_bindings: Dict) -> Tuple[Any, List]:

        op = ast.operation_type
        coll_ref, coll_safety = self._resolve_collection_source(ast.source, var_bindings)

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
                membership = Or(*[And(coll_ref.cnt_func(coll_ref.root_inst, inst) > 0, inst == arg_expr)
                                  for inst in coll_ref.valid_instances])
                return membership, coll_safety + arg_safety
            raise ValueError("includes operation requires an argument")

        if op == "excludes":
            if ast.arguments:
                arg_expr, arg_safety = self.translate(ast.arguments[0], var_bindings)
                non_membership = And(*[
                    Implies(coll_ref.cnt_func(coll_ref.root_inst, inst) > 0, inst != arg_expr)
                    for inst in coll_ref.valid_instances])
                return non_membership, coll_safety + arg_safety
            raise ValueError("excludes operation requires an argument")

        if op in ["asSet", "asBag"]:
            return coll_ref, coll_safety

        if op in ["asSequence", "asOrderedSet", "at"]:
            raise NotImplementedError(
                f"Verification Capability Limit: '{op}' requires ordered collection semantics, "
                f"which are not supported in the current unordered counting model fragment."
            )

        if op == "flatten":
            return coll_ref, coll_safety

        if op in ["first", "last"]:
            null_const = self.me.null_consts.get(coll_ref.element_class)
            res_expr = null_const if null_const is not None else self.me._default_value_for_sort(
                self.me._z3_sort(coll_ref.element_class))

            # 逆向折叠：如果是 first，从后往前覆盖；如果是 last，从前往后覆盖
            instances = coll_ref.valid_instances
            if op == "first":
                instances = reversed(instances)

            for inst in instances:
                in_set = coll_ref.cnt_func(coll_ref.root_inst, inst) > 0
                res_expr = If(in_set, inst, res_expr)
            return res_expr, coll_safety

        if op == "count":
            if ast.arguments:
                arg_expr, arg_safety = self.translate(ast.arguments[0], var_bindings)
                cnt_terms = [
                    If(inst == arg_expr, coll_ref.cnt_func(coll_ref.root_inst, inst), IntVal(0))
                    for inst in coll_ref.valid_instances
                ]
                total = Sum(*cnt_terms) if cnt_terms else IntVal(0)
                return total, coll_safety + arg_safety

        if op == "includesAll":
            if ast.arguments:
                arg_expr, arg_safety = self.translate(ast.arguments[0], var_bindings)
                if not isinstance(arg_expr, CollectionRef):
                    raise ValueError(
                        "Semantic Error: includesAll requires a collection as argument, "
                        f"but got a scalar value of type {arg_expr.sort()}."
                    )
                conds = []
                for inst in arg_expr.valid_instances:
                    arg_cnt = arg_expr.cnt_func(arg_expr.root_inst, inst)
                    coll_cnt = coll_ref.cnt_func(coll_ref.root_inst, inst)
                    conds.append(coll_cnt >= arg_cnt)
                return And(*conds), coll_safety + arg_safety
            raise ValueError("includesAll operation requires an argument")

        if op == "excludesAll":
            if ast.arguments:
                arg_expr, arg_safety = self.translate(ast.arguments[0], var_bindings)
                # 修复：防御性隔离，确保参数是集合而非标量
                if not isinstance(arg_expr, CollectionRef):
                    raise ValueError(
                        "Semantic Error: excludesAll requires a collection as argument, "
                        f"but got a scalar value of type {arg_expr.sort()}."
                    )
                conds = []
                for inst in arg_expr.valid_instances:
                    in_arg = arg_expr.cnt_func(arg_expr.root_inst, inst) > 0
                    in_coll = coll_ref.cnt_func(coll_ref.root_inst, inst) > 0
                    conds.append(Not(And(in_arg, in_coll)))
                return And(*conds), coll_safety + arg_safety
            raise ValueError("excludesAll operation requires an argument")

            # 确保此行与所有 if op == ... 对齐，不在任何分支内部
        raise NotImplementedError(f"Collection operation not implemented: {op}")

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
            sum_safety_acc = []  # 收集 sum 内部的 safety
            for inst in coll_ref.valid_instances:
                cnt = coll_ref.cnt_func(coll_ref.root_inst, inst)
                body_val, body_safety_ref = self._eval_body_with_var(body_ast, var_name, inst, elem_class,
                                                                     saved_bindings)
                sum_safety_acc.append(body_safety_ref)  # 冒泡收集
                if not (is_int(body_val) or is_real(body_val)):
                    raise ValueError(
                        "Z3 Compilation Error: ->sum() requires numeric values, but ->collect() "
                        "returned a non-numeric type. Ensure the collect body evaluates to Integer or Real."
                    )
                if is_real(body_val):
                    terms.append(ToReal(cnt) * body_val)
                else:
                    terms.append(cnt * body_val)
            return Sum(*terms) if terms else IntVal(0), sum_safety_acc  # 返回收集的 safety

        # 然后再检查 callable（FuncDeclRef）
        if not callable(attr_func):
            raise RuntimeError(
                f"Z3 Translator Internal Error: attr_func has unexpected type {type(attr_func).__name__}. "
                f"This is a translator bug, not an AST error."
            )

        # 正常的 FuncDeclRef 路径
        terms = []
        for inst in coll_ref.valid_instances:
            cnt = coll_ref.cnt_func(coll_ref.root_inst, inst)
            nav_val = inst
            for nav_func in coll_ref.nav_chain:
                if not callable(nav_func):
                    raise RuntimeError(
                        f"Z3 Translator Internal Error: non-callable in nav_chain: {type(nav_func).__name__}"
                    )
                nav_val = nav_func(nav_val)
            attr_val = attr_func(nav_val)
            if is_real(attr_val):
                terms.append(ToReal(cnt) * attr_val)
            else:
                terms.append(cnt * attr_val)
        return Sum(*terms) if terms else IntVal(0), []

    # ---------- 集合源解析 ----------
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

    # ---------- IfExpression ----------
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

    # ---------- LetExpression ----------
    def _handle_let_expr(self, ast: LetExpression, var_bindings: Dict) -> Tuple[Any, List]:
        val_expr, val_safety = self.translate(ast.value, var_bindings)
        new_bindings = var_bindings.copy()
        new_bindings[ast.variable.name] = val_expr
        body_expr, body_safety = self.translate(ast.body, new_bindings)
        return body_expr, val_safety + body_safety

    # ---------- CollectionLiteral ----------
    def _handle_collection_literal(self, ast: CollectionLiteral, var_bindings: Dict) -> Tuple[Any, List]:
        elements = []
        literal_safety = []
        for elem in ast.elements:
            elem_expr, elem_safety = self.translate(elem, var_bindings)
            elements.append(elem_expr)
            literal_safety.extend(elem_safety)

        def literal_cnt(root, inst):
            return IntVal(1)

        return CollectionRef(
            root_inst=None, cnt_func=literal_cnt,
            element_class="Unknown", valid_instances=elements), literal_safety

    # ---------- 类型推导 ----------
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
            if ast.iterator_type in ["forAll", "exists", "one", "isUnique"]:
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

        elif ast.type == "TypeCast":
            return ast.target_type

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

        for super_cls in uml_ctx.get("superclasses", []):
            result = self._get_element_class_name(super_cls, prop_name)
            if result != "Unknown":
                return result

        return "Unknown"

    # ---------- 算术/关系运算辅助 ----------
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


# ==========================================
# ==========================================
# 组件 3 & 4：基于蕴含关系的定性分级判定
# ==========================================

def check_equivalence(gt_expr, llm_expr, meta_encoder, context_class, self_var) -> dict:
    """基于 Z3 蕴含关系判定，返回结构化结果（含反例）"""
    null_const = meta_encoder.null_consts[context_class]
    gt_forall = ForAll([self_var], Implies(self_var != null_const, gt_expr))
    llm_forall = ForAll([self_var], Implies(self_var != null_const, llm_expr))

    s = Solver()
    s.add(meta_encoder.axioms)

    # 判定 1: GT 是否蕴含 LLM (弱化检查)
    s.push()
    s.add(gt_forall)
    s.add(Not(llm_forall))
    is_weakened = (s.check() == sat)
    weakened_ce = extract_counterexample(s, meta_encoder, context_class, self_var) if is_weakened else None
    s.pop()

    # 判定 2: LLM 是否蕴含 GT (强化检查)
    s.push()
    s.add(llm_forall)
    s.add(Not(gt_forall))
    is_strengthened = (s.check() == sat)
    strengthened_ce = extract_counterexample(s, meta_encoder, context_class, self_var) if is_strengthened else None
    s.pop()

    # 定性分级
    if not is_weakened and not is_strengthened:
        result = "EQUIVALENT"
    elif not is_weakened and is_strengthened:
        result = "STRENGTHENED"
    elif is_weakened and not is_strengthened:
        result = "WEAKENED"
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
def evaluate_constraint(gt_ast: OCLExpression, llm_ast: OCLExpression, uml_context: dict, context_class: str) -> dict:
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

    # 2. 编码元模型
    meta_encoder = BoundedMetamodelEncoder(uml_context, scope=3)

    # 3. self 的 Z3 Const 显式绑定
    self_var = Const("self", meta_encoder.sorts[context_class])
    var_bindings = {"context_class": context_class, "self": self_var}

    # 4. 翻译 AST (经过预检，此处理论上是安全的)
    translator = OCLZ3Translator(meta_encoder)
    gt_expr, gt_safety = translator.translate(gt_ast, var_bindings)
    llm_expr, llm_safety = translator.translate(llm_ast, var_bindings)

    # 终极收口：将顶层残留安全条件合取注入
    if gt_safety:
        gt_expr = And(And(*gt_safety), gt_expr)
    if llm_safety:
        llm_expr = And(And(*llm_safety), llm_expr)

    # 5. 基于蕴含关系的定性分级判定（直接返回字典）
    return check_equivalence(gt_expr, llm_expr, meta_encoder, context_class, self_var)

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
                    cnt_int = cnt.as_long() if hasattr(cnt, 'as_long') else str(cnt)
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
