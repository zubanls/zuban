from typing import TypeVar

T = TypeVar("T")


def foo(y: T) -> T:
    ...


#? int()
foo(1)

#? str()
foo("")
