from typing import Callable, TypeVar, Tuple

T = TypeVar('T')
U = TypeVar('U')

def return_callable1(x: T) -> Callable[[U], Tuple[T, U]]: ...

#? int()
return_callable1(7)("")[0]
#? str()
return_callable1(7)("")[1]
