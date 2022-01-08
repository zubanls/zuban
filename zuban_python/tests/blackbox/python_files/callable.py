from typing import Callable, TypeVar, Tuple, Generic

T = TypeVar('T')
U = TypeVar('U')
V = TypeVar('V')

def return_callable1(x: T) -> Callable[[U], Tuple[T, U]]: ...

#? int()
return_callable1(7)("")[0]
#? str()
return_callable1(7)("")[1]

def return_callable2() -> Callable[[U], Tuple[T, U]]: ...

#?
return_callable2(7)("")[0]
#? str()
return_callable2(7)("")[1]

class Foo(Generic[V]):
    def __init__(self, foo: V): ...
    def return_callable3(self, x: T) -> Callable[[U], Tuple[T, U, V]]: ...

ret = Foo(1.0).return_callable3(7)("")
#? int()
ret[0]
#? str()
ret[1]
#? float()
ret[2]
