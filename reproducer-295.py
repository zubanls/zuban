from typing import Any, Generic, TypeVar

T = TypeVar("T")
Tc = TypeVar("Tc", covariant=True)

class TypedColumnsClauseRole(Generic[Tc]): ...

class ColumnElement(TypedColumnsClauseRole[T]):
    def label(self, name: str) -> ColumnElement[T]: raise NotImplementedError

def literal(value: T) -> ColumnElement[T]: raise NotImplementedError
def asc(value: ColumnElement[T] | TypedColumnsClauseRole[T]) -> None: ...

def build_query(order: int):
    sort_column: ColumnElement[Any]
    match order:
        case 0: sort_column = literal(1.0).label("zero")
        case _: sort_column = literal(None).label("order")
    asc(sort_column)
