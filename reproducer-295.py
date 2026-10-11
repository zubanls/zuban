from typing import Any

import sqlalchemy as sa


def build_query(order: int):
    sort_column: sa.ColumnElement[Any]
    match order:
        case 0:
            sort_column = sa.literal(1.0)
        case _:
            sort_column = sa.literal(None)
    sa.asc(sort_column)
