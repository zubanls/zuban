def asc[T: (float, None)](value: type[T]): ...
def build_query(order):
    sort_column: type
    match order:
        case 0: sort_column = float
        case _: sort_column = type(None)
    asc(sort_column)
