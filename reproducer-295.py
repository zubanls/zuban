from typing import Any, Generic, TypeVar

_T = TypeVar("_T")
_T_co = TypeVar("_T_co", covariant=True)

class TypedColumnsClauseRole(Generic[_T_co]): ...
class ExpressionElementRole(TypedColumnsClauseRole[_T_co]): ...
class BinaryElementRole(ExpressionElementRole[_T]): ...
class ColumnElement(BinaryElementRole[_T], Generic[_T]):
    def label(self, name: str) -> Label[_T]: raise NotImplementedError
class Label(ColumnElement[_T]): ...
class BindParameter(ColumnElement[_T]): ...
def literal(value: _T) -> BindParameter[_T]: raise NotImplementedError
def asc(value: ColumnElement[_T] | TypedColumnsClauseRole[_T]) -> None: ...

def build_query(order: int) -> None:
    sort_column: ColumnElement[Any]
    asc(sort_column)
    match order:
        case 0: sort_column = literal(1.0).label("zero")
        case _: sort_column = literal(None).label("order")
    asc(sort_column)
