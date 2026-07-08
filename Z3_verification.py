import re
import itertools
import time
import gc
from typing import Dict, List, Tuple
from z3 import *
from json_schema import (OCLExpression, PropertyCall, OperationCall, BinaryExpression,
                         IteratorExpression, CollectionOperation, LiteralExpression,
                         IfExpression, UnaryExpression, LetExpression, CollectionLiteral)

Z3_TIMEOUT_MS = 60000


class CollectionRef:
    def __init__(self, root_inst, cnt_func, element_class, valid_instances,
                 attr_func=None, nav_chain=None, is_set_semantic=False):
        self.root_inst = root_inst
        self.cnt_func = cnt_func
        self.element_class = element_class
        self.valid_instances = valid_instances
        self.attr_func = attr_func
        self.nav_chain = nav_chain or []
        self.is_set_semantic = is_set_semantic

class BoundedUMLModelEncoder:
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
                            self.axioms.append(func(src_inst, tgt_inst) <= self.scope)

            else:
                self.axioms.append(func(src_null) == tgt_null)

                if meta["is_mandatory"]:
                    for src_inst in self.get_valid_instances(meta["src_class"]):
                        self.axioms.append(
                            Implies(src_inst != src_null, func(src_inst) != tgt_null))

    def get_valid_instances(self, class_name: str) -> List[Any]:
        sort = self.sorts[class_name]
        instances = [getattr(sort, f'{class_name.lower()}_{i}') for i in range(self.scope)]
        instances.append(self.null_consts[class_name])
        return instances

    def _default_value_for_sort(self, sort_ref):

        if sort_ref == IntSort(): return IntVal(0)
        if sort_ref == RealSort(): return RealVal(0)
        if sort_ref == BoolSort(): return BoolVal(False)
        if sort_ref == StringSort(): return StringVal("")
        return IntVal(0)


class OCLZ3Translator:
    def __init__(self, encoder: BoundedUMLModelEncoder):
        self.encoder = encoder

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

            if is_real(left) and is_int(right):
                right = ToReal(right)
            elif is_int(left) and is_real(right):
                left = ToReal(left)

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

            is_safe = Or(And(s_l, Not(left)), And(s_r, Not(right)), And(s_l, s_r))
            return And(left, right), [is_safe]
        if op == 'or':

            is_safe = Or(And(s_l, left), And(s_r, right), And(s_l, s_r))
            return Or(left, right), [is_safe]
        if op == 'implies':

            return Implies(left, right), [And(s_l, Implies(left, s_r))]
        if op == 'xor':
            return Xor(left, right), left_safety + right_safety
        raise NotImplementedError(f"Binary operator not implemented: {op}")

    def _handle_if_expr(self, ast, var_bindings):
        cond, cond_safety = self.translate(ast.condition, var_bindings)
        then_expr, then_safety = self.translate(ast.then_expression, var_bindings)
        else_expr, else_safety = self.translate(ast.else_expression, var_bindings)

        if is_real(then_expr) and is_int(else_expr):
            else_expr = ToReal(else_expr)
        elif is_int(then_expr) and is_real(else_expr):
            then_expr = ToReal(then_expr)

        def combine_s(s_list):
            return And(*s_list) if s_list else BoolVal(True)

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


    def _handle_property_call(self, ast: PropertyCall, var_bindings: Dict) -> Tuple[Any, List]:
        src_result, src_safety = self.translate(ast.source, var_bindings)

        if isinstance(src_result, CollectionRef):
            return self._handle_implicit_collect(src_result, ast.property_name, src_safety)

        src_expr = src_result
        src_type_name = self._infer_class_name(ast.source, var_bindings)
        func_key = f"{src_type_name}.{ast.property_name}"
        src_null = self.encoder.null_consts.get(src_type_name)

        is_mandatory = False
        if func_key in self.encoder.assoc_funcs:
            is_mandatory = self.encoder.assoc_meta[func_key].get("is_mandatory", False)


        is_source_non_null = self._is_guaranteed_non_null(ast.source, var_bindings)


        null_guard = [] if (is_mandatory or is_source_non_null) else (
            [src_expr != src_null] if src_null is not None else [])
        base_safety = src_safety + null_guard


        if func_key in self.encoder.assoc_funcs:
            func = self.encoder.assoc_funcs[func_key]
            meta = self.encoder.assoc_meta[func_key]

            if src_expr.sort() != func.domain(0):
                raise ValueError(...)

            if meta["is_count"]:
                valid_instances = self.encoder.get_valid_instances(meta["tgt_class"])

                return CollectionRef(
                    root_inst=src_expr, cnt_func=func, element_class=meta["tgt_class"],
                    valid_instances=valid_instances,
                    is_set_semantic=meta.get("is_set_semantic", False)
                ), base_safety
            else:
                result = func(src_expr)
                return result, base_safety

        if func_key in self.encoder.attr_funcs:
            func = self.encoder.attr_funcs[func_key]
            if src_expr.sort() != func.domain(0):
                raise ValueError(...)
            return func(src_expr), base_safety

        raise ValueError(f"Unknown property: {func_key}")

    def _handle_implicit_collect(self, coll_ref: CollectionRef, prop_name: str,
                                 src_safety: List) -> Tuple[Any, List]:
        if not isinstance(coll_ref, CollectionRef):

            raise ValueError(
                f"Semantic Error: Cannot navigate property '{prop_name}' on a non-collection value. Did you mean to use '.' instead of '->'?")

        element_class = coll_ref.element_class
        func_key = f"{element_class}.{prop_name}"

        if func_key in self.encoder.attr_funcs:
            return CollectionRef(
                root_inst=coll_ref.root_inst, cnt_func=coll_ref.cnt_func,
                element_class=element_class, valid_instances=coll_ref.valid_instances,
                attr_func=self.encoder.attr_funcs[func_key],
                nav_chain=coll_ref.nav_chain,
                is_set_semantic=False), src_safety

        if func_key in self.encoder.assoc_funcs:
            func = self.encoder.assoc_funcs[func_key]
            meta = self.encoder.assoc_meta[func_key]

            if not meta["is_count"]:
                tgt_class = meta["tgt_class"]
                tgt_instances_raw = self.encoder.get_valid_instances(tgt_class)
                tgt_null = self.encoder.null_consts.get(tgt_class)


                tgt_instances = [inst for inst in tgt_instances_raw
                                 if tgt_null is None or not inst.eq(tgt_null)]
                src_root_inst = coll_ref.root_inst
                null_c = self.encoder.null_consts.get(coll_ref.element_class)

                def mapped_cnt(root, tgt_elem):
                    total = IntVal(0)
                    for src_elem in coll_ref.valid_instances:
                        if null_c is not None and src_elem.eq(null_c):
                            continue
                        nav_val = src_elem
                        for nav_func in coll_ref.nav_chain:
                            nav_val = nav_func(nav_val)
                        nav_val = func(nav_val)
                        src_cnt = coll_ref.cnt_func(src_root_inst, src_elem)


                        if tgt_null is not None:
                            total = total + If(And(nav_val != tgt_null, nav_val == tgt_elem),
                                               src_cnt, IntVal(0))
                        else:
                            total = total + If(nav_val == tgt_elem, src_cnt, IntVal(0))
                    return total

                return CollectionRef(
                    root_inst=coll_ref.root_inst,
                    cnt_func=mapped_cnt,
                    element_class=tgt_class,
                    valid_instances=tgt_instances,
                    nav_chain=[],
                    is_set_semantic=False
                ), src_safety

            else:
                return self._handle_nested_collection(coll_ref, func_key, meta, src_safety)

        raise ValueError(f"Unknown property in implicit collect: {func_key}")

    def _handle_nested_collection(self, parent_ref: CollectionRef, func_key: str, meta: Dict, src_safety: List) -> \
    Tuple[Any, List]:
        sub_cnt_func = self.encoder.assoc_funcs[func_key]
        sub_element_class = meta["tgt_class"]
        sub_valid_instances = self.encoder.get_valid_instances(sub_element_class)
        prop_root_inst = parent_ref.root_inst
        null_c = self.encoder.null_consts.get(parent_ref.element_class)

        def combined_cnt(root, sub_elem):
            total = IntVal(0)
            for parent_elem in parent_ref.valid_instances:

                if null_c is not None and parent_elem.eq(null_c):
                    continue
                parent_cnt = parent_ref.cnt_func(prop_root_inst, parent_elem)
                sub_cnt = sub_cnt_func(parent_elem, sub_elem)
                max_cnt = 1 if parent_ref.is_set_semantic else self.encoder.scope
                total = total + self._linear_multiply(parent_cnt, sub_cnt, max_cnt)
            return total

        return CollectionRef(
            root_inst=prop_root_inst, cnt_func=combined_cnt, element_class=sub_element_class,
            valid_instances=sub_valid_instances, is_set_semantic=False), src_safety

    def _handle_operation_call(self, ast: OperationCall, var_bindings: Dict) -> Tuple[Any, List]:
        op = ast.operation_name
        src_expr, src_safety = self.translate(ast.source, var_bindings)

        if op == "oclIsUndefined":
            src_type = self._infer_class_name(ast.source, var_bindings)
            null_const = self.encoder.null_consts.get(src_type)
            is_safe = And(*src_safety) if src_safety else BoolVal(True)
            if null_const is not None:
                return Or(Not(is_safe), src_expr == null_const), []
            return Not(is_safe), []

        if op == "abs":
            return If(src_expr < 0, -src_expr, src_expr), src_safety

        raise NotImplementedError(f"Operation not implemented: {op}")


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

                normalized = simplify(elem_expr)

                key = f"{str(normalized)}:{normalized.sort()}"
                if key not in seen_keys:
                    seen_keys.add(key)

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
        iter_vars = [v.name for v in ast.iterators]


        if len(iter_vars) == 1:
            return self._handle_single_var_iterator(
                ast, coll_ref, iter_vars[0], element_class, var_bindings, coll_safety)
        else:
            return self._handle_multi_var_iterator(
                ast, coll_ref, iter_vars, element_class, var_bindings, coll_safety)

    def _handle_single_var_iterator(self, ast, coll_ref, iter_var_name, element_class, var_bindings, coll_safety):
        accumulated_body_safety = []
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

        elif ast.iterator_type == "isUnique":
            return self._handle_is_unique_single(
                ast, coll_ref, iter_var_name, element_class, var_bindings, coll_safety)

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
        iter_type = ast.iterator_type
        n_vars = len(iter_vars)
        accumulated_body_safety = []

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

        elif iter_type == "isUnique":

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

        pair_constraints = []
        accumulated_body_safety = []
        instances = coll_ref.valid_instances
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

        op = ast.operation_name
        coll_ref, coll_safety = self._resolve_collection_source(ast.source, var_bindings)

        def _get_actual_val_for_coll(target_coll: CollectionRef, inst, accumulated_safety, cnt_val):

            if target_coll.attr_func is None:
                return inst, BoolVal(True)
            if isinstance(target_coll.attr_func, tuple) and target_coll.attr_func[0] == "collect_body":
                _, body_ast, var_name, elem_class, saved_bindings = target_coll.attr_func
                body_val, body_safety = self._eval_body_with_var(body_ast, var_name, inst, elem_class, saved_bindings)

                return body_val, body_safety
            elif callable(target_coll.attr_func):
                nav_val = inst
                is_valid = BoolVal(True)
                for nav_func in target_coll.nav_chain:
                    null_c = self.encoder.sort_to_null.get(nav_val.sort())
                    if null_c is not None:
                        is_valid = And(is_valid, nav_val != null_c)
                    nav_val = nav_func(nav_val)
                null_c = self.encoder.sort_to_null.get(nav_val.sort())
                if null_c is not None:
                    is_valid = And(is_valid, nav_val != null_c)

                return target_coll.attr_func(nav_val), is_valid
            return inst, BoolVal(True)

        def _safe_eq(left, right):

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
                    effective_cnt = If(is_valid, base_cnt, IntVal(0))
                    conds.append(And(effective_cnt > 0, _safe_eq(actual_val, arg_expr)))

                return Or(*conds) if conds else BoolVal(False), coll_safety + arg_safety

        if op == "excludes":
            if ast.arguments:
                arg_expr, arg_safety = self.translate(ast.arguments[0], var_bindings)
                conds = []
                for inst in coll_ref.valid_instances:
                    base_cnt = coll_ref.cnt_func(coll_ref.root_inst, inst)
                    actual_val, is_valid = _get_actual_val_for_coll(coll_ref, inst, arg_safety, base_cnt)
                    effective_cnt = If(is_valid, base_cnt, IntVal(0))
                    conds.append(Implies(effective_cnt > 0, Not(_safe_eq(actual_val, arg_expr))))

                return And(*conds) if conds else BoolVal(True), coll_safety + arg_safety

        if op == "asSet":
            _old_cnt = coll_ref.cnt_func
            _old_root = coll_ref.root_inst

            def _set_truncated_cnt(root, inst):
                actual_root = _old_root if root is None else root
                raw_cnt = _old_cnt(actual_root, inst)
                return If(raw_cnt > 0, IntVal(1), IntVal(0))

            return CollectionRef(
                root_inst=coll_ref.root_inst,
                cnt_func=_set_truncated_cnt,
                element_class=coll_ref.element_class,
                valid_instances=coll_ref.valid_instances,
                attr_func=coll_ref.attr_func,
                nav_chain=coll_ref.nav_chain,
                is_set_semantic=True
            ), coll_safety

        if op == "asBag":
            return CollectionRef(
                root_inst=coll_ref.root_inst, cnt_func=coll_ref.cnt_func, element_class=coll_ref.element_class,
                valid_instances=coll_ref.valid_instances, attr_func=coll_ref.attr_func, nav_chain=coll_ref.nav_chain,
                is_set_semantic=False
            ), coll_safety

        if op == "count":
            if ast.arguments:
                arg_expr, arg_safety = self.translate(ast.arguments[0], var_bindings)
                cnt_terms = []
                for inst in coll_ref.valid_instances:
                    base_cnt = coll_ref.cnt_func(coll_ref.root_inst, inst)
                    actual_val, is_valid = _get_actual_val_for_coll(coll_ref, inst, arg_safety, base_cnt)
                    effective_cnt = If(is_valid, base_cnt, IntVal(0))
                    cnt_terms.append(If(_safe_eq(actual_val, arg_expr), effective_cnt, IntVal(0)))

                total = Sum(*cnt_terms) if cnt_terms else IntVal(0)
                return total, coll_safety + arg_safety

        if op in ["includesAll", "excludesAll"]:
            if not ast.arguments:
                raise ValueError(f"{op} operation requires an argument")
            arg_expr, arg_safety = self.translate(ast.arguments[0], var_bindings)
            if not isinstance(arg_expr, CollectionRef):
                raise ValueError(f"Semantic Error: {op} requires a collection as argument.")

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

            if op == "includesAll":
                for arg_inst in arg_expr.valid_instances:
                    arg_actual = arg_actuals[arg_inst]
                    arg_match_terms = []
                    for inner_arg in arg_expr.valid_instances:
                        inner_actual = arg_actuals[inner_arg]
                        inner_cnt = arg_expr.cnt_func(arg_expr.root_inst, inner_arg)
                        effective_inner_cnt = If(arg_is_valid[inner_arg], inner_cnt, IntVal(0))
                        arg_match_terms.append(If(_safe_eq(inner_actual, arg_actual), effective_inner_cnt, IntVal(0)))
                    total_arg_cnt = Sum(*arg_match_terms) if arg_match_terms else IntVal(0)

                    coll_match_terms = []
                    for coll_inst in coll_ref.valid_instances:
                        coll_actual = coll_actuals[coll_inst]
                        coll_cnt = coll_ref.cnt_func(coll_ref.root_inst, coll_inst)
                        effective_coll_cnt = If(coll_is_valid[coll_inst], coll_cnt, IntVal(0))
                        coll_match_terms.append(If(_safe_eq(coll_actual, arg_actual), effective_coll_cnt, IntVal(0)))
                    total_coll_cnt = Sum(*coll_match_terms) if coll_match_terms else IntVal(0)

                    conds.append(total_coll_cnt >= total_arg_cnt)
                return And(*conds) if conds else BoolVal(True), coll_safety + arg_safety

            elif op == "excludesAll":
                for arg_inst in arg_expr.valid_instances:
                    arg_actual = arg_actuals[arg_inst]
                    arg_cnt = arg_expr.cnt_func(arg_expr.root_inst, arg_inst)
                    effective_arg_cnt = If(arg_is_valid[arg_inst], arg_cnt, IntVal(0))

                    coll_match_terms = []
                    for coll_inst in coll_ref.valid_instances:
                        coll_actual = coll_actuals[coll_inst]
                        coll_cnt = coll_ref.cnt_func(coll_ref.root_inst, coll_inst)
                        effective_coll_cnt = If(coll_is_valid[coll_inst], coll_cnt, IntVal(0))
                        coll_match_terms.append(If(_safe_eq(coll_actual, arg_actual), effective_coll_cnt, IntVal(0)))
                    total_coll_cnt = Sum(*coll_match_terms) if coll_match_terms else IntVal(0)
                    conds.append(Implies(effective_arg_cnt > 0, total_coll_cnt == 0))
                return And(*conds) if conds else BoolVal(True), coll_safety + arg_safety

        if op in ["union", "intersection"]:
            if not ast.arguments:
                raise ValueError(f"{op} operation requires an argument")
            arg_expr, arg_safety = self.translate(ast.arguments[0], var_bindings)
            if not isinstance(arg_expr, CollectionRef):
                raise ValueError(f"{op} requires a collection as argument")

            if op == "union":
                result_is_set = coll_ref.is_set_semantic and arg_expr.is_set_semantic
            else:
                result_is_set = coll_ref.is_set_semantic or arg_expr.is_set_semantic

            left_insts = coll_ref.valid_instances
            right_insts = arg_expr.valid_instances

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

            if left_sort == right_sort:
                seen = set()
                final_instances = []
                for inst in (left_insts + right_insts):
                    inst_id = inst.get_id() if hasattr(inst, 'get_id') else id(inst)
                    if inst_id not in seen:
                        seen.add(inst_id)
                        final_instances.append(inst)

                final_class = coll_ref.element_class
                if {coll_ref.element_class, arg_expr.element_class} == {"Integer", "Real"}:
                    final_class = "Real"

                def merged_cnt(root, inst):
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


            elif {str(left_sort), str(right_sort)} == {"Int", "Real"}:
                final_class = "Real"
                final_instances = []
                for inst in left_insts:
                    final_instances.append(ToReal(inst) if is_int(inst) else inst)
                for inst in right_insts:
                    final_instances.append(ToReal(inst) if is_int(inst) else inst)

                seen = set()
                unique_instances = []
                for inst in final_instances:
                    key = str(inst)
                    if key not in seen:
                        seen.add(key)
                        unique_instances.append(inst)


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

            else:
                raise ValueError(
                    f"Z3 Compilation Error: Cannot perform {op} on collections with "
                    f"incompatible Z3 sorts ({left_sort} vs {right_sort}). "
                    f"Cross-type collection algebra is not supported in the verification subset."
                )

        raise NotImplementedError(f"Collection operation not implemented: {op}")

    def _is_guaranteed_non_null(self, ast, var_bindings):

        if ast.type == "Variable":
            return ast.name == "self"
        elif ast.type == "PropertyCall":
            src_type_name = self._infer_class_name(ast.source, var_bindings)
            func_key = f"{src_type_name}.{ast.property_name}"
            if func_key in self.encoder.assoc_funcs:
                meta = self.encoder.assoc_meta[func_key]

                if meta.get("is_mandatory", False) and not meta.get("is_count", False):
                    return self._is_guaranteed_non_null(ast.source, var_bindings)
            return False
        return False

    def _eval_body_with_var(self, body_ast, var_name, inst, element_class, var_bindings):
        new_bindings = var_bindings.copy()
        new_bindings[var_name] = inst
        new_bindings[var_name + "_type"] = element_class
        body_expr, body_safety = self.translate(body_ast, new_bindings)


        combined_safety = And(*body_safety) if body_safety else BoolVal(True)

        return body_expr, combined_safety

    def _eval_body_with_vars(self, body_ast, var_names, inst_tuple, element_class, var_bindings):
        new_bindings = var_bindings.copy()
        for var_name, inst in zip(var_names, inst_tuple):
            new_bindings[var_name] = inst
            new_bindings[var_name + "_type"] = element_class
        body_expr, body_safety = self.translate(body_ast, new_bindings)


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

                max_cnt = 1 if coll_ref.is_set_semantic else self.encoder.scope

                valid_multiplier = If(body_safety_ref, IntVal(1), IntVal(0))
                safe_cnt = cnt * valid_multiplier
                term = self._linear_multiply(safe_cnt, body_val, max_cnt)
                terms.append(term)

            return Sum(*terms) if terms else IntVal(0), sum_safety_acc

        if not callable(attr_func):
            raise RuntimeError(
                f"Z3 Translator Internal Error: attr_func has unexpected type {type(attr_func).__name__}. "
                f"This is a translator bug, not an AST error."
            )

        terms = []
        sum_safety_acc = []
        for inst in coll_ref.valid_instances:
            cnt = coll_ref.cnt_func(coll_ref.root_inst, inst)
            nav_val = inst
            for nav_func in coll_ref.nav_chain:
                if not callable(nav_func): raise RuntimeError(...)
                nav_val = nav_func(nav_val)

            attr_val = attr_func(nav_val)
            max_cnt = 1 if coll_ref.is_set_semantic else self.encoder.scope
            null_c = self.encoder.sort_to_null.get(nav_val.sort())
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

            if ast.name in self.encoder.uml_context:
                return ast.name
            return "Unknown"

        elif ast.type == "PropertyCall":
            owner_class = self._infer_class_name(ast.source, bindings)
            return self._get_element_class_name(owner_class, ast.property_name)

        elif ast.type == "OperationCall":
            if ast.operation_name == "oclIsUndefined":
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
            if ast.operation_name in ["size", "count"]:
                return "Integer"
            if ast.operation_name in ["isEmpty", "notEmpty", "includes", "excludes"]:
                return "Boolean"
            if ast.operation_name == "sum":
                inner_type = self._infer_class_name(ast.source, bindings)
                return "Real" if "Real" in inner_type else "Integer"
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
            return self._infer_class_name(ast.then_expression, bindings)

        elif ast.type == "LetExpression":
            return self._infer_class_name(ast.body, bindings)

        return "Unknown"

    def _get_element_class_name(self, owner_class: str, prop_name: str) -> str:
        uml_ctx = self.encoder.uml_context.get(owner_class, {})

        assoc_type = uml_ctx.get("associations", {}).get(prop_name, "")
        if assoc_type:
            match = re.search(r'\((\w+)\)', assoc_type)
            if match:
                return match.group(1)
            match_opt = re.match(r'(\w+)\[', assoc_type)
            if match_opt:
                return match_opt.group(1)
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
        if is_real(val):
            zero = RealVal(0)
        elif is_int(val):
            zero = IntVal(0)
        else:
            raise ValueError(
                f"Z3 Compilation Error: Cannot perform linear multiplication on non-numeric sort {val.sort()}."
            )

        if max_cnt <= 0:
            return zero

        if max_cnt == 1:
            return If(cnt > 0, val, zero)

        terms = []
        for i in range(1, max_cnt + 1):
            terms.append(If(cnt >= i, val, zero))
        return Sum(*terms)


def check_equivalence(solver, gt_forall, llm_forall, encoder,
                      context_class, self_var, case_key: str,
                      constraint_name: str, ablation_config=None) -> dict:
    solving_time = 0.0
    is_llm_stricter = False
    is_llm_looser = False
    strengthened_ce = None
    weakened_ce = None
    timeout_hit = False

    solver.push()
    solver.add(gt_forall)
    solver.add(Not(llm_forall))

    solve_start = time.perf_counter()
    res1 = solver.check()
    solve_end = time.perf_counter()
    solving_time += (solve_end - solve_start)

    if res1 == sat:
        is_llm_stricter = True
        strengthened_ce = extract_counterexample(
            solver, encoder, context_class, self_var)
    elif res1 == unknown:
        timeout_hit = True
        solving_time = max(solving_time, Z3_TIMEOUT_MS / 1000.0)

    solver.pop()
    solver.push()
    solver.add(llm_forall)
    solver.add(Not(gt_forall))

    solve_start = time.perf_counter()
    res2 = solver.check()
    solve_end = time.perf_counter()
    solving_time += (solve_end - solve_start)

    if res2 == sat:
        is_llm_looser = True
        weakened_ce = extract_counterexample(
            solver, encoder, context_class, self_var)
    elif res2 == unknown:
        timeout_hit = True
        solving_time = max(solving_time, Z3_TIMEOUT_MS / 1000.0)

    solver.pop()
    if timeout_hit:
        result = "TIMEOUT"
    elif not is_llm_stricter and not is_llm_looser:
        result = "EQUIVALENT"
    elif is_llm_stricter and not is_llm_looser:
        result = "STRENGTHENED"
    elif not is_llm_stricter and is_llm_looser:
        result = "WEAKENED"
    else:
        result = "INCOMPARABLE"

    return {
        "result": result,
        "weakened_counterexample": weakened_ce,
        "strengthened_counterexample": strengthened_ce,
        "solving_time_sec": solving_time,
        "timeout_hit": timeout_hit
    }

def evaluate_constraint(gt_ast: OCLExpression, llm_ast: OCLExpression,
                        uml_context: dict, context_class: str,
                        case_key: str, constraint_name: str,
                        cegar_round: int = 0,
                        ablation_config=None) -> dict:


    gc.disable()
    total_start = time.perf_counter()
    safety_solving_time = 0.0
    vacuity_solving_time = 0.0
    safety_timeout = False
    vacuity_timeout = False
    encoding_time = 0.0

    def _abl_enabled(flag_name: str) -> bool:

        if ablation_config is None:
            return True
        return ablation_config.is_enabled(flag_name)

    try:

        if _abl_enabled("enable_layer3_z3_compile"):
            is_translatable, err_msg = check_z3_translatable(
                llm_ast, uml_context, context_class)
            if not is_translatable:
                total_end = time.perf_counter()
                result = {
                    "result": "INCOMPARABLE",
                    "weakened_counterexample": None,
                    "strengthened_counterexample": None,
                    "compilation_error": err_msg,
                    "encoding_time_sec": 0.0,
                    "solving_time_sec": 0.0,
                    "total_pipeline_time_sec": total_end - total_start,
                    "timeout_hit": False
                }
                return result

        encoding_start = time.perf_counter()
        encoder = BoundedUMLModelEncoder(uml_context, scope=3)
        self_var = Const("self", encoder.sorts[context_class])
        var_bindings = {"context_class": context_class, "self": self_var}
        translator = OCLZ3Translator(encoder)
        gt_expr, gt_safety = translator.translate(gt_ast, var_bindings)
        llm_expr, llm_safety = translator.translate(llm_ast, var_bindings)
        null_const = encoder.null_consts[context_class]

        if _abl_enabled("enable_safety_injection"):
            if gt_safety:
                gt_expr = And(And(*gt_safety), gt_expr)
            if llm_safety:
                llm_expr = And(And(*llm_safety), llm_expr)

        gt_forall = ForAll([self_var],
                           Implies(self_var != null_const, gt_expr))
        llm_forall = ForAll([self_var],
                            Implies(self_var != null_const, llm_expr))

        s = Solver()
        s.set("timeout", Z3_TIMEOUT_MS)
        s.add(encoder.axioms)

        encoding_end = time.perf_counter()
        encoding_time = encoding_end - encoding_start

        if gt_safety:
            s.push()
            s.add(self_var != null_const)
            s.add(Not(And(*gt_safety)))

            solve_start = time.perf_counter()
            safety_result = s.check()
            solve_end = time.perf_counter()
            safety_solving_time = solve_end - solve_start

            if safety_result == unknown:
                safety_timeout = True
                safety_solving_time = Z3_TIMEOUT_MS / 1000.0

            s.pop()

            if safety_result == sat:
                total_end = time.perf_counter()
                result = {
                    "result": "INVALID_REF",
                    "weakened_counterexample": None,
                    "strengthened_counterexample": None,
                    "compilation_error": (
                        "Unsafe GT: Ground Truth contains potential "
                        "null/invalid dereference. "
                        "Equivalence is semantically undefined."),
                    "encoding_time_sec": encoding_time,
                    "solving_time_sec": safety_solving_time,
                    "total_pipeline_time_sec": total_end - total_start,
                    "timeout_hit": safety_timeout
                }
                return result

        if _abl_enabled("enable_vacuity_check"):
            s.push()
            s.add(gt_forall)

            solve_start = time.perf_counter()
            vacuity_result = s.check()
            solve_end = time.perf_counter()
            vacuity_solving_time = solve_end - solve_start

            if vacuity_result == unknown:
                vacuity_timeout = True
                vacuity_solving_time = Z3_TIMEOUT_MS / 1000.0

            s.pop()

            if vacuity_result == unsat:
                total_end = time.perf_counter()
                result = {
                    "result": "INVALID_REF",
                    "weakened_counterexample": None,
                    "strengthened_counterexample": None,
                    "compilation_error": (
                        "Vacuous Truth: GT is UNSAT within bounded scope. "
                        "Increase scope or skip."),
                    "encoding_time_sec": encoding_time,
                    "solving_time_sec": safety_solving_time + vacuity_solving_time,
                    "total_pipeline_time_sec": total_end - total_start,
                    "timeout_hit": safety_timeout or vacuity_timeout
                }
                return result

        if _abl_enabled("enable_layer3_z3_equivalence"):
            eq_result = check_equivalence(
                s, gt_forall, llm_forall, encoder,
                context_class, self_var, case_key, constraint_name)
        else:
            eq_result = {
                "result": "ABLATION_SKIPPED",
                "weakened_counterexample": None,
                "strengthened_counterexample": None,
                "compilation_error": None,
                "solving_time_sec": 0.0,
                "timeout_hit": False
            }

        total_end = time.perf_counter()
        total_solving = (safety_solving_time + vacuity_solving_time
                         + eq_result.get("solving_time_sec", 0.0))
        eq_result["encoding_time_sec"] = encoding_time
        eq_result["solving_time_sec"] = total_solving
        eq_result["total_pipeline_time_sec"] = total_end - total_start
        eq_result["timeout_hit"] = (
            eq_result.get("timeout_hit", False)
            or safety_timeout or vacuity_timeout)
        return eq_result

    finally:
        gc.enable()
        gc.collect()

def check_z3_translatable(llm_ast: OCLExpression, uml_context: dict,
                          context_class: str, ablation_config=None) -> tuple:

    try:
        encoder = BoundedUMLModelEncoder(uml_context, scope=1)
        self_var = Const("self", encoder.sorts[context_class])
        var_bindings = {"context_class": context_class, "self": self_var}
        translator = OCLZ3Translator(encoder)
        translator.translate(llm_ast, var_bindings)
        return True, None
    except RuntimeError:
        raise
    except Exception as e:
        import traceback
        traceback.print_exc()
        return False, f"Z3 Compilation Error: {type(e).__name__}: {e}"


def extract_counterexample(solver, encoder, context_class, self_var) -> str:
    model = solver.model()
    sort = encoder.sorts[context_class]
    null_const = encoder.null_consts[context_class]
    scope = encoder.scope
    lines = []

    def _get_inst_attrs_str(inst, class_name, depth=1):

        if depth < 0:
            return ""
        cls_info = encoder.uml_context.get(class_name, {})
        parts = []

        for attr_name, attr_type in cls_info.get("attributes", {}).items():
            func_key = f"{class_name}.{attr_name}"
            if func_key in encoder.attr_funcs:
                val = model.eval(encoder.attr_funcs[func_key](inst), model_completion=True)
                parts.append(f"{attr_name}={val}")

        if depth > 0:
            for assoc_name, assoc_type in cls_info.get("associations", {}).items():
                func_key = f"{class_name}.{assoc_name}"
                if func_key in encoder.assoc_funcs:
                    meta = encoder.assoc_meta[func_key]
                    tgt_class = meta["tgt_class"]
                    tgt_null = encoder.null_consts.get(tgt_class)

                    if meta["is_count"]:
                        coll_parts = []
                        for tgt_inst in encoder.get_valid_instances(tgt_class):
                            cnt = model.eval(encoder.assoc_funcs[func_key](inst, tgt_inst), model_completion=True)
                            cnt_int = cnt.as_long() if is_int_value(cnt) else str(cnt)
                            if cnt_int != 0:
                                tgt_attrs_str = _get_inst_attrs_str(tgt_inst, tgt_class, depth - 1)
                                coll_parts.append(f"{tgt_inst}(count={cnt_int}){tgt_attrs_str}")
                        if coll_parts:
                            parts.append(f"{assoc_name}=[{', '.join(coll_parts)}]")
                    else:
                        tgt_val = model.eval(encoder.assoc_funcs[func_key](inst), model_completion=True)
                        if tgt_null is not None and tgt_val.eq(tgt_null):
                            parts.append(f"{assoc_name}={tgt_val}")
                        else:
                            tgt_attrs_str = _get_inst_attrs_str(tgt_val, tgt_class, depth - 1)
                            parts.append(f"{assoc_name}={tgt_val}{tgt_attrs_str}")

        return f"{{{', '.join(parts)}}}" if parts else ""

    for i in range(scope):
        inst = getattr(sort, f'{context_class.lower()}_{i}')
        lines.append(f"\n--- Candidate: {inst} ---")
        lines.append(f" self = {inst}")


        cls_info = encoder.uml_context.get(context_class, {})
        for attr_name, attr_type in cls_info.get("attributes", {}).items():
            func_key = f"{context_class}.{attr_name}"
            if func_key in encoder.attr_funcs:
                val = model.eval(encoder.attr_funcs[func_key](inst), model_completion=True)
                lines.append(f" self.{attr_name} = {val}")


        for assoc_name, assoc_type in cls_info.get("associations", {}).items():
            func_key = f"{context_class}.{assoc_name}"
            if func_key in encoder.assoc_funcs:
                meta = encoder.assoc_meta[func_key]
                tgt_class = meta["tgt_class"]
                tgt_null = encoder.null_consts.get(tgt_class)

                if meta["is_count"]:
                    parts = []
                    for tgt_inst in encoder.get_valid_instances(tgt_class):
                        cnt = model.eval(encoder.assoc_funcs[func_key](inst, tgt_inst), model_completion=True)
                        cnt_int = cnt.as_long() if is_int_value(cnt) else str(cnt)
                        if cnt_int != 0:

                            tgt_attrs_str = _get_inst_attrs_str(tgt_inst, tgt_class, 1)
                            parts.append(f"{tgt_inst}(count={cnt_int}) {tgt_attrs_str}")
                    if parts:
                        lines.append(f" self.{assoc_name}: {', '.join(parts)}")
                else:
                    tgt_val = model.eval(encoder.assoc_funcs[func_key](inst), model_completion=True)
                    if tgt_null is not None and tgt_val.eq(tgt_null):
                        lines.append(f" self.{assoc_name} = {tgt_val}")
                    else:
                        tgt_attrs_str = _get_inst_attrs_str(tgt_val, tgt_class, 1)
                        lines.append(f" self.{assoc_name} = {tgt_val} {tgt_attrs_str}")

    header = f"Counter-example state (all {scope} bounded instances shown):\n"
    return header + "\n".join(lines)
