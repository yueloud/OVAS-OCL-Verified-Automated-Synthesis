from pydantic import BaseModel, Field
from typing import List, Optional, Union, Annotated
from typing import Literal as TypeLiteral


SCHEMA_VARIANTS = {
    "full": {
        "description": "Full JSON schema",
        "relaxed_fields": [],
    },
}

def get_schema_variant_names() -> List[str]:

    return list(SCHEMA_VARIANTS.keys())

def get_schema_variant_description(name: str) -> str:

    if name not in SCHEMA_VARIANTS:
        raise ValueError(f"Unknown schema variant: '{name}'. Available: {get_schema_variant_names()}")
    return SCHEMA_VARIANTS[name]["description"]


class OCLNode(BaseModel):

    type: str

class LiteralExpression(OCLNode):

    type: TypeLiteral["LiteralExpression"] = "LiteralExpression"
    value: Union[str, int, float, bool, None]
    literal_type: TypeLiteral["String", "Integer", "Real", "Boolean", "Null"]

class CollectionLiteral(OCLNode):

    type: TypeLiteral["CollectionLiteral"] = "CollectionLiteral"
    collection_kind: TypeLiteral["Set", "Bag"]
    elements: List["OCLExpression"] = Field(default_factory=list)

class Variable(OCLNode):

    type: TypeLiteral["Variable"] = "Variable"
    name: str
    declared_type: Optional[str] = None

class PropertyCall(OCLNode):

    type: TypeLiteral["PropertyCall"] = "PropertyCall"
    source: "OCLExpression"
    property_name: str

class OperationCall(OCLNode):

    type: TypeLiteral["OperationCall"] = "OperationCall"
    source: "OCLExpression"
    operation_name: str
    arguments: List["OCLExpression"] = Field(default_factory=list)

class BinaryExpression(OCLNode):

    type: TypeLiteral["BinaryExpression"] = "BinaryExpression"
    operator: str
    left: "OCLExpression"
    right: "OCLExpression"

class UnaryExpression(OCLNode):

    type: TypeLiteral["UnaryExpression"] = "UnaryExpression"
    operator: str
    expression: "OCLExpression"

class IteratorExpression(OCLNode):

    type: TypeLiteral["IteratorExpression"] = "IteratorExpression"
    source: "OCLExpression"
    iterator_type: str
    iterators: List[Variable]
    body: "OCLExpression"

class CollectionOperation(OCLNode):

    type: TypeLiteral["CollectionOperation"] = "CollectionOperation"
    source: "OCLExpression"
    operation_name: str
    arguments: List["OCLExpression"] = Field(default_factory=list)

class IfExpression(OCLNode):

    type: TypeLiteral["IfExpression"] = "IfExpression"
    condition: "OCLExpression"
    then_expression: "OCLExpression"
    else_expression: "OCLExpression"

class LetExpression(OCLNode):

    type: TypeLiteral["LetExpression"] = "LetExpression"
    variable: Variable
    value: "OCLExpression"
    body: "OCLExpression"


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
        LetExpression
    ],
    Field(discriminator="type")
]


CollectionLiteral.model_rebuild()
PropertyCall.model_rebuild()
OperationCall.model_rebuild()
BinaryExpression.model_rebuild()
UnaryExpression.model_rebuild()
IteratorExpression.model_rebuild()
CollectionOperation.model_rebuild()
IfExpression.model_rebuild()
LetExpression.model_rebuild()

class OCLConstraint(BaseModel):

    context_class: str
    context_operation: Optional[str] = None
    stereotype: TypeLiteral["inv", "pre", "post", "body"] = "inv"
    expression: OCLExpression
    name: Optional[str] = None

class OCLDocument(BaseModel):

    constraints: List[OCLConstraint]


def build_schema_variant(variant_name: str = "full") -> type[BaseModel]:

    if variant_name not in SCHEMA_VARIANTS:
        raise ValueError(
            f"Unknown schema variant: '{variant_name}'. "
            f"Available: {get_schema_variant_names()}"
        )


    if variant_name == "full":
        return OCLDocument


    print(f"[Ablation] Schema variant '{variant_name}' requested. "
          f"Falling back to full schema (dynamic generation not yet implemented).")
    return OCLDocument
