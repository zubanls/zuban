from typing import Any, Generic, TypeVar

_T = TypeVar("_T")
_ColumnType = TypeVar("_ColumnType", covariant=True)
_SortType = TypeVar("_SortType", float, None)


class ColumnElement(Generic[_ColumnType]):
    def label(self, name: str) -> "Label[_ColumnType]":
        raise NotImplementedError


class Label(ColumnElement[_ColumnType]):
    ...


def literal(value: _T) -> ColumnElement[_T]:
    raise NotImplementedError


def asc(column: ColumnElement[_SortType]) -> None:
    ...


def build_query(order: int) -> None:
    sort_column: ColumnElement[Any]
    asc(sort_column)
    match order:
        case 0:
            sort_column = literal(1.0).label("zero")
        case _:
            sort_column = literal(None).label("order")
    asc(sort_column)
