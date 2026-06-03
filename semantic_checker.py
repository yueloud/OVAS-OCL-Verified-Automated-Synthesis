import re
import json
from typing import List, Dict, Union
from json_schema import OCLExpression


class SemanticError(Exception):
    """语义校验失败时抛出的专属异常"""
    pass


# ==========================================
# 组件 1：静态元模型库 (Metamodel Registry)
# ==========================================
class MetamodelRegistry:
    def __init__(self, benchmark_path: str):
        with open(benchmark_path, 'r', encoding='utf-8') as f:
            self.data = json.load(f)

    def get_uml_context(self, case_key: str) -> dict:
        if case_key not in self.data:
            raise SemanticError(f"Benchmark 中找不到用例: {case_key}")
        return self.data[case_key].get("UML_Context", {})

    def resolve_property(self, uml_context: dict, class_name: str, prop_name: str) -> str:
        if class_name not in uml_context:
            raise SemanticError(f"未知的类: '{class_name}'。请检查是否拼写错误或使用了不存在的类型。")
        cls_info = uml_context[class_name]

        if prop_name in cls_info.get("attributes", {}):
            return cls_info["attributes"][prop_name]

        if prop_name in cls_info.get("associations", {}):
            return cls_info["associations"][prop_name]

        for super_cls in cls_info.get("superclasses", []):
            try:
                return self.resolve_property(uml_context, super_cls, prop_name)
            except SemanticError:
                continue

        raise SemanticError(
            f"大模型幻觉: 类 '{class_name}' 及其父类中不存在属性/关联 '{prop_name}'"
        )


# ==========================================
# 组件 2：动态符号表 (Type Environment)
# ==========================================
class TypeEnvironment:
    def __init__(self, case_key: str, context_class: str, registry: MetamodelRegistry):
        self.case_key = case_key
        self.uml_context = registry.get_uml_context(case_key)
        self.registry = registry
        self.scopes: List[Dict[str, str]] = [{"self": context_class}]

    def push_scope(self):
        self.scopes.append({})

    def pop_scope(self):
        self.scopes.pop()

    def bind_variable(self, name: str, var_type: str):
        self.scopes[-1][name] = var_type

    def resolve_variable(self, name: str) -> str:
        if name in self.uml_context:
            return f"Class({name})"
        for scope in reversed(self.scopes):
            if name in scope:
                return scope[name]
        raise SemanticError(f"大模型幻觉: 使用了未绑定的变量或作用域越界 '{name}'")


# ==========================================
# 强化版类型辅助函数
# ==========================================
def is_collection_type(type_str: str) -> bool:
    """核心子集仅支持 Set 和 Bag"""
    return type_str.startswith(("Set(", "Bag("))


def extract_inner_type(collection_type: str) -> str:
    """提取集合内部类型，天然支持任意层级的嵌套 (e.g., Set(Bag(X)) -> Bag(X))"""
    match = re.match(r'^[A-Za-z]+\(', collection_type)
    if not match:
        return collection_type
    inner = collection_type[match.end():]
    if inner.endswith(')'):
        inner = inner[:-1]
    return inner


# ==========================================
# 组件 3：终极版核心校验引擎 (Semantic Checker)
# ==========================================
class OCLSemanticChecker:
    @classmethod
    def _infer_type_from_value(cls, value: Union[str, int, float, bool, None]) -> str:

        if value is None:
            return "Null"
        if isinstance(value, bool):  # 注意：bool 必须在 int 之前判断，因为 bool 是 int 的子类
            return "Boolean"
        if isinstance(value, int):
            return "Integer"
        if isinstance(value, float):
            return "Real"
        if isinstance(value, str):
            return "String"
        raise SemanticError(f"无法识别的字面量值: {value}")

    @classmethod
    def _compatible_types(cls, derived_type: str) -> set:
        """给定推导类型，返回所有兼容的声明类型（用于容错）"""
        compatibility_map = {
            "Integer": {"Integer", "Real"},  # OCL 中 Integer 可当 Real 用
            "Real": {"Real"},
            "String": {"String"},
            "Boolean": {"Boolean"},
            # 其他类型严格匹配
        }
        return compatibility_map.get(derived_type, {derived_type})

    @classmethod
    def check(cls, expr: OCLExpression, env: 'TypeEnvironment') -> str:# type: ignore[arg-type]
        """递归入口：严格返回推导类型，遇到任何未知直接 raise 拦截"""
        node_type = expr.type

        if node_type == "LiteralExpression":
            actual_type = cls._infer_type_from_value(expr.value)
            # 使用统一的兼容性判断函数
            if expr.literal_type and expr.literal_type not in cls._compatible_types(actual_type):
                raise SemanticError(
                    f"字面量类型声明冲突: value={repr(expr.value)} 实际是 {actual_type}，"
                    f"但声明为 {expr.literal_type}"
                )
            return actual_type

        elif node_type == "Variable":
            resolved_type = env.resolve_variable(expr.name)  # 推导类型是真理
            if expr.declared_type and expr.declared_type not in cls._compatible_types(resolved_type):
                raise SemanticError(
                    f"变量类型声明冲突: '{expr.name}' 声明为 {expr.declared_type}，"
                    f"但上下文推导为 {resolved_type}"
                )
            return resolved_type  # 永远返回推导类型

        elif node_type == "CollectionLiteral":
            if expr.elements:
                elem_types = [cls.check(elem, env) for elem in expr.elements]
                unique_types = set(elem_types)
                if len(unique_types) == 1:
                    return f"{expr.collection_kind}({elem_types[0]})"
                # Integer 和 Real 兼容：集合中混合时提升为 Real
                elif unique_types == {"Integer", "Real"}:
                    return f"{expr.collection_kind}(Real)"
                else:
                    raise SemanticError(
                        f"集合字面量中元素类型不一致: {unique_types}"
                    )
            # 空集合无法推导元素类型，直接拦截
            raise SemanticError(
                "空集合字面量无法推导元素类型，请避免使用空集合或使用更明确的类型标注"
            )

        elif node_type == "TypeCast":
            _ = cls.check(expr.expression, env)
            return expr.target_type


        elif node_type == "PropertyCall":

            source_type = cls.check(expr.source, env)
            is_col = is_collection_type(source_type)
            base_type = extract_inner_type(source_type) if is_col else source_type
            clean_base = re.sub(r'\[.*?]', '', base_type)

            if clean_base.startswith("Class("):
                raise SemanticError(
                    f"不能直接对类调用属性 '{expr.property_name}'"
                )

            prop_type: str = str(env.registry.resolve_property(
                env.uml_context, clean_base, expr.property_name
            ))

            clean_prop_type = re.sub(r'\[.*?]', '', prop_type)

            if is_col:
                flat_type = (

                    extract_inner_type(clean_prop_type) if is_collection_type(clean_prop_type) else clean_prop_type

                )
                # OCL 隐式 collect 语义：对集合属性导航结果（如 Set(X).prop），降级为 Bag
                return f"Bag({flat_type})"

            return clean_prop_type


        elif node_type == "OperationCall":
            source_type = cls.check(expr.source, env)
            op = expr.operation_name

            if op == "allInstances":
                if not source_type.startswith("Class("):
                    raise SemanticError("allInstances() 只能对类调用")
                return f"Set({extract_inner_type(source_type)})"

            elif op in ["isDefined", "oclIsUndefined", "oclIsInvalid", "oclIsKindOf"]:
                return "Boolean"

            elif op == "oclAsType":
                # 尝试从 arguments 中提取目标类型
                if expr.arguments:
                    arg = expr.arguments[0]
                    # 类型名通常以 LiteralExpression(String) 或 Variable 形式出现
                    if hasattr(arg, 'value') and isinstance(arg.value, str):
                        return arg.value
                    elif hasattr(arg, 'name'):  # Variable 节点
                        return str(arg.name)
                # 无法推断目标类型时，给出精确错误
                raise SemanticError(
                    f"oclAsType() 无法推断目标类型。请在 arguments 中明确指定类型名称。"
                )

            elif op == "abs":
                if source_type not in ["Integer", "Real"]:
                    raise SemanticError(
                        f"abs() 只能用于数字类型，得到 {source_type}"
                    )
                return source_type

            elif op == "toString":
                return "String"

            # 【终极防御】绝不静默放行 Unknown
            raise SemanticError(
                f"未知的 OperationCall: '{op}' 作用于类型 {source_type}。"
                f"请使用 OCL 标准库中已定义的操作。"
            )

        elif node_type == "BinaryExpression":
            left_type = cls.check(expr.left, env)
            right_type = cls.check(expr.right, env)

            is_left_col = is_collection_type(left_type)
            is_right_col = is_collection_type(right_type)

            if expr.operator in ['+', '-', '*', '/', '<', '<=', '>', '>=']:
                # 维度坍塌检查：算术算子两端不能出现集合
                if is_left_col or is_right_col:
                    raise SemanticError(
                        f"维度坍塌: '{expr.operator}' 两端必须是标量，"
                        f"得到 {left_type} 和 {right_type}。"
                        f"提示：是否忘记了 ->size() 或 ->sum()?"
                    )
                # String 拼接支持：'+' 两端均为 String 时合法
                if expr.operator == '+' and left_type == "String" and right_type == "String":
                    return "String"
                # 数值类型兼容性：Integer + Real → Real
                if expr.operator in ['<', '<=', '>', '>=']:
                    # 比较算子要求两侧均为数值类型
                    numeric = {"Integer", "Real"}
                    if left_type not in numeric or right_type not in numeric:
                        raise SemanticError(
                            f"比较算子 '{expr.operator}' 要求两侧为数值类型，"
                            f"得到 {left_type} 和 {right_type}"
                        )
                    return "Boolean"
                return "Real" if "Real" in [left_type, right_type] else "Integer"

            elif expr.operator in ['and', 'or', 'implies', 'xor']:
                if left_type != "Boolean" or right_type != "Boolean":
                    raise SemanticError(
                        f"逻辑运算违例: '{expr.operator}' 两边必须为 Boolean，"
                        f"得到 {left_type} 和 {right_type}"
                    )
                return "Boolean"

            elif expr.operator in ['=', '<>']:
                # 等价性检查：拒绝集合与标量的比较
                if is_left_col != is_right_col:
                    raise SemanticError(
                        f"类型违例: '{expr.operator}' 不能比较集合与标量，"
                        f"得到 {left_type} 和 {right_type}"
                    )
                return "Boolean"

        elif node_type == "UnaryExpression":
            inner_type = cls.check(expr.expression, env)
            if expr.operator == "not":
                if inner_type != "Boolean":
                    raise SemanticError(
                        f"'not' 算子必须作用于 Boolean，得到 {inner_type}"
                    )
                return "Boolean"
            elif expr.operator == "-":
                if inner_type not in ["Integer", "Real"]:
                    raise SemanticError(
                        f"负号算子必须作用于数字，得到 {inner_type}"
                    )
                return inner_type
            raise SemanticError(f"未知的一元算子: '{expr.operator}'")

        elif node_type == "IfExpression":
            cond_type = cls.check(expr.condition, env)
            if cond_type != "Boolean":
                raise SemanticError(f"If 条件必须是 Boolean，得到 {cond_type}")
            then_type = cls.check(expr.then_expr, env)
            else_type = cls.check(expr.else_expr, env)

            # 兼容性检查：Integer 与 Real 兼容
            compatible = (
                then_type == else_type
                or {then_type, else_type} == {"Integer", "Real"}
            )
            if not compatible:
                raise SemanticError(
                    f"If 分支类型不兼容: {then_type} vs {else_type}"
                )
            return "Real" if "Real" in [then_type, else_type] else then_type


        elif node_type == "CollectionOperation":
            source_type = cls.check(expr.source, env)

            if not is_collection_type(source_type):
                raise SemanticError(
                    f"算子违例: '{expr.operation_type}' 只能作用于集合类型，"
                    f"得到 {source_type}"
                )

            if expr.operation_type == "size":
                return "Integer"

            elif expr.operation_type == "count":
                return "Integer"

            elif expr.operation_type == "sum":
                inner = extract_inner_type(source_type)

                if inner not in ["Integer", "Real"]:
                    raise SemanticError(
                        f"集合求和违例: sum() 只能用于数字集合，"
                        f"得到元素类型为 {inner}"
                    )
                return "Real" if inner == "Real" else "Integer"

            elif expr.operation_type in [
                "isEmpty", "notEmpty", "includes", "excludes", "includesAll", "excludesAll"
            ]:
                return "Boolean"

            elif expr.operation_type == "asSet":
                return f"Set({extract_inner_type(source_type)})"

            elif expr.operation_type == "asBag":
                return f"Bag({extract_inner_type(source_type)})"

            elif expr.operation_type == "flatten":
                inner = extract_inner_type(source_type)
                if is_collection_type(inner):
                    return f"Bag({extract_inner_type(inner)})"

                return f"Bag({inner})"

            elif expr.operation_type in ["union", "intersection"]:
                if not expr.arguments:
                    raise SemanticError(f"'{expr.operation_type}' requires a collection argument.")

                # 推导参数的类型
                arg_type = cls.check(expr.arguments[0], env)

                # 双方都必须是集合
                if not is_collection_type(arg_type):
                    raise SemanticError(f"'{expr.operation_type}' argument must be a collection, got {arg_type}")

                src_inner = extract_inner_type(source_type)
                arg_inner = extract_inner_type(arg_type)

                # 元素类型必须兼容 (Integer 和 Real 视为兼容，此处简化为必须一致)
                if src_inner != arg_inner and not ({src_inner, arg_inner} == {"Integer", "Real"}):
                    raise SemanticError(
                        f"Collection element type mismatch in {expr.operation_type}: "
                        f"{source_type} vs {arg_type}"
                    )

                # OCL 类型提升规则
                src_is_set = source_type.startswith("Set(")
                arg_is_set = arg_type.startswith("Set(")
                inner_type = src_inner if src_inner != "Integer" else "Real"  # 处理 Int+Real 提升

                if expr.operation_type == "union":
                    result_is_set = src_is_set and arg_is_set
                else:  # intersection
                    result_is_set = src_is_set or arg_is_set  # 只要有一方是 Set，交集必然是 Set

                return f"Set({inner_type})" if result_is_set else f"Bag({inner_type})"

            raise SemanticError(
                f"未知的 CollectionOperation: '{expr.operation_type}'"
            )

        elif node_type == "IteratorExpression":
            source_type = cls.check(expr.source, env)
            if not is_collection_type(source_type):
                raise SemanticError(
                    f"迭代器违例: '{expr.iterator_type}' 只能用于集合，"
                    f"得到 {source_type}"
                )

            inner_type = extract_inner_type(source_type)

            # 显式变量声明检查
            if not expr.iterator_variables:
                raise SemanticError(
                    f"迭代器 {expr.iterator_type} 缺少显式的变量声明 "
                    f"(iterator_variables 为空)。必须使用显式迭代变量，"
                    f"例如: self.xs->forAll(x | x.prop > 0)"
                )

            # try/finally 保护作用域栈，防止异常导致栈污染
            env.push_scope()
            try:
                for var in expr.iterator_variables:
                    if var.declared_type and var.declared_type not in cls._compatible_types(inner_type):
                        raise SemanticError(
                            f"迭代变量类型声明冲突: '{var.name}' 声明为 {var.declared_type}，"
                            f"但集合元素推导为 {inner_type}"
                        )
                    env.bind_variable(var.name, inner_type)  # 仍然绑定推导类型

                body_type = cls.check(expr.body, env)
            finally:
                env.pop_scope()  # 无论成功失败必须出栈

            if expr.iterator_type in ["forAll", "exists"]:
                if body_type != "Boolean":
                    raise SemanticError(
                        f"迭代器违例: {expr.iterator_type} 闭包必须返回 Boolean，"
                        f"实际返回 {body_type}"
                    )
                return "Boolean"

            elif expr.iterator_type in ["select", "reject"]:
                if body_type != "Boolean":
                    raise SemanticError(
                        f"迭代器违例: {expr.iterator_type} 闭包必须返回 Boolean"
                    )
                return source_type  # 保持原集合类型

            elif expr.iterator_type == "collect":
                return f"Bag({body_type})"

            elif expr.iterator_type == "isUnique":
                if is_collection_type(body_type):
                    raise SemanticError(
                        f"isUnique 闭包不应返回集合类型，得到 {body_type}"
                    )
                return "Boolean"

            # 未知的迭代器类型 → 精确报错
            raise SemanticError(
                f"未知的迭代器类型: '{expr.iterator_type}'。"
                f"核心子集仅支持: forAll, exists, select, reject, collect, isUnique"
            )

        elif node_type == "LetExpression":
            val_type = cls.check(expr.value, env)

            if expr.variable.declared_type and expr.variable.declared_type not in cls._compatible_types(val_type):
                raise SemanticError(
                    f"Let变量类型声明冲突: '{expr.variable.name}' 声明为 {expr.variable.declared_type}，"
                    f"但赋值表达式推导为 {val_type}"
                )
            env.push_scope()
            try:
                env.bind_variable(expr.variable.name, val_type)
                body_type = cls.check(expr.body, env)
            finally:
                env.pop_scope()  # ✅ 安全出栈
            return body_type

        # 最后的保底拦截：如果还有遗漏的节点类型，直接爆错
        raise SemanticError(
            f"解析器遇到未实现的 AST 节点类型: {node_type}"
        )
