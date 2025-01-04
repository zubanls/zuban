from typing import Callable, TypeVar, Tuple, Generic

T = TypeVar('T')
U = TypeVar('U')
V = TypeVar('V')
W = TypeVar('W')
X = TypeVar('X')

def return_callable1(x: T) -> Callable[[U], Tuple[T, U]]: ...

#? int()
return_callable1(7)("")[0]
#? str()
return_callable1(7)("")[1]

def return_callable2() -> Callable[[U], Tuple[T, U]]: ...

##?
return_callable2(7)("")[0]
#? str()
return_callable2(7)("")[1]

class Foo(Generic[V]):
    def __init__(self, foo: V): ...
    def return_callable3(self, x: T) -> Callable[[U], Tuple[T, U, V]]: ...
    def return_callable4(self) -> Callable[[U], Tuple[T, U, V]]: ...
    def return_callable5(self, x: T) -> Callable[[U], Callable[[W], Tuple[T, U, V, W]]]: ...
    def return_callable6(self, x: T) -> Callable[[U], Tuple[Callable[[W], Tuple[T, U, V, W]],
                                                            Callable[[W], Tuple[T, U, V, W]]
                                                            ]]: ...
    def return_callable7(self, x: T) -> Callable[[U], Tuple[Callable[[W], Tuple[T, U, V, W]],
                                                            Callable[[X], Tuple[T, U, V, X]]
                                                            ]]: ...

ret = Foo(1.0).return_callable3(7)("")
#? int()
ret[0]
#? str()
ret[1]
#? float()
ret[2]

ret = Foo(1.0).return_callable4(7)("")
##?
ret[0]
#? str()
ret[1]
#? float()
ret[2]

ret = Foo(1.0).return_callable5(7)("")(list)
#? int()
ret[0]
#? str()
ret[1]
#? float()
ret[2]
#? list
ret[3]

callables = Foo(1.0).return_callable6(7)("")
ret = callables[0](list)
#? int()
ret[0]
#? str()
ret[1]
#? float()
ret[2]
#? list
ret[3]

ret = callables[1](set)
#? int()
ret[0]
#? str()
ret[1]
#? float()
ret[2]
#? set
ret[3]

callables = Foo(1.0).return_callable7(7)("")
ret = callables[0](list)
#? int()
ret[0]
#? str()
ret[1]
#? float()
ret[2]
#? list
ret[3]

ret = callables[1](set)
#? int()
ret[0]
#? str()
ret[1]
#? float()
ret[2]
#? set
ret[3]
