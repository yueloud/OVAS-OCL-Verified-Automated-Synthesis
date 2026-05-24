from pydantic import BaseModel, Field
from typing import List, Optional, Union, Annotated
from typing import Literal as TypeLiteral  # 避免与 AST 节点名冲突

class OCLNode(BaseModel):
    """OCL AST 节点基类"""
    type: str

class LiteralExpression(OCLNode):
    """字面量节点"""
    type: TypeLiteral["LiteralExpression"] = "LiteralExpression"
    value: Union[str, int, float, bool, None]
    literal_type: TypeLiteral["String", "Integer", "Real", "Boolean", "Null"]

class CollectionLiteral(OCLNode):
    """集合字面量节点 (例如: Set{1, 2, 3})"""
    type: TypeLiteral["CollectionLiteral"] = "CollectionLiteral"
    collection_kind: TypeLiteral["Set", "Bag"]
    elements: List["OCLExpression"] = Field(default_factory=list)

class Variable(OCLNode):
    """变量节点"""
    type: TypeLiteral["Variable"] = "Variable"
    name: str
    declared_type: Optional[str] = None  # 语义补丁 1：保留变量类型信息

class PropertyCall(OCLNode):
    """属性或关联导航调用节点"""
    type: TypeLiteral["PropertyCall"] = "PropertyCall"
    source: "OCLExpression"
    property_name: str

class OperationCall(OCLNode):
    """对象操作调用节点"""
    type: TypeLiteral["OperationCall"] = "OperationCall"
    source: "OCLExpression"
    operation_name: str
    arguments: List["OCLExpression"] = Field(default_factory=list)

class BinaryExpression(OCLNode):
    """二元表达式节点"""
    type: TypeLiteral["BinaryExpression"] = "BinaryExpression"
    left: "OCLExpression"
    operator: TypeLiteral["+", "-", "*", "/", "=", "<>", "<", "<=", ">", ">=", "and", "or", "implies", "xor"]
    right: "OCLExpression"

class UnaryExpression(OCLNode):
    """一元表达式节点"""
    type: TypeLiteral["UnaryExpression"] = "UnaryExpression"
    operator: TypeLiteral["not", "-"]
    expression: "OCLExpression"

class IteratorExpression(OCLNode):
    """迭代器表达式节点"""
    type: TypeLiteral["IteratorExpression"] = "IteratorExpression"
    source: "OCLExpression"
    iterator_type: TypeLiteral["forAll", "exists", "select", "reject", "collect", "isUnique"]
    iterator_variables: List[Variable]
    body: "OCLExpression"

class CollectionOperation(OCLNode):
    """集合原生操作节点"""
    type: TypeLiteral["CollectionOperation"] = "CollectionOperation"
    source: "OCLExpression"
    operation_type: TypeLiteral["size", "isEmpty", "notEmpty", "includes", "excludes", "includesAll", "excludesAll", "sum", "count",
        "asSet", "asBag", "flatten", "union", "intersection"]
    arguments: List["OCLExpression"] = Field(default_factory=list)

class IfExpression(OCLNode):
    """条件表达式节点"""
    type: TypeLiteral["IfExpression"] = "IfExpression"
    condition: "OCLExpression"
    then_expr: "OCLExpression"
    else_expr: "OCLExpression"

class LetExpression(OCLNode):
    """局部变量声明节点"""
    type: TypeLiteral["LetExpression"] = "LetExpression"
    variable: Variable
    value: "OCLExpression"
    body: "OCLExpression"

class TypeCast(OCLNode):
    """类型转换节点"""
    type: TypeLiteral["TypeCast"] = "TypeCast"
    expression: "OCLExpression"
    target_type: str



# --- 核心架构：多态鉴别器，确保 LLM 稳定输出 ---
OCLExpression = Annotated[
    Union[
        LiteralExpression,
        CollectionLiteral,
        Variable,
        PropertyCall,
        OperationCall,
        BinaryExpression,
        UnaryExpression,
        IteratorExpression,
        CollectionOperation,
        IfExpression,
        LetExpression,
        TypeCast
    ],
    Field(discriminator="type")
]

# --- 递归引用前向声明更新 ---
CollectionLiteral.model_rebuild()
PropertyCall.model_rebuild()
OperationCall.model_rebuild()
BinaryExpression.model_rebuild()
UnaryExpression.model_rebuild()
IteratorExpression.model_rebuild()
CollectionOperation.model_rebuild()
IfExpression.model_rebuild()
LetExpression.model_rebuild()
TypeCast.model_rebuild()

class OCLConstraint(BaseModel):
    """OCL 约束模型"""
    context_class: str
    context_operation: Optional[str] = None
    stereotype: TypeLiteral["inv", "pre", "post", "body"] = "inv"
    expression: OCLExpression
    name: Optional[str] = None

class OCLDocument(BaseModel):
    """完整的 OCL 文档"""
    constraints: List[OCLConstraint]