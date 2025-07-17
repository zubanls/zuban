class A:
    hello_a: str
    hello_both: str
class B:
    hello_b: int
    hello_both: int
class C:
    hello_c: int

def type_of_union(x: type[A | B], a: type[A]):
    #? ["hello_a", "hello_b", "hello_both"]
    x.hello
    #? str()
    x.hello_a
    #? int()
    x.hello_b
    #! ["hello_a: str"]
    x.hello_a
    #! ["hello_b: int"]
    x.hello_b

    #! ["hello_both: str", "hello_both: int"]
    x.hello_both
    #? str() int()
    x.hello_both

    #! ["hello_a: str"]
    a.hello_a
    #! []
    a.hello_b

def union(x: A | B):
    #? ["hello_a", "hello_b", "hello_both"]
    x.hello
    #? str()
    x.hello_a
    #? int()
    x.hello_b
    #! ["hello_a: str"]
    x.hello_a
    #! ["hello_b: int"]
    x.hello_b

def intersections(a: A):
    if isinstance(a, B):
        #? A()
        a
        #? ["hello_a", "hello_both"]
        a.hello
        #? str()
        a.hello_both

    if isinstance(a, C):
        #? A() C()
        a
        #? ["hello_a", "hello_both", "hello_c"]
        a.hello
        #? str()
        a.hello_both
    #? A()
    a
    #? ["hello_a", "hello_both"]
    a.hello

#? 20 typing.TypeVar()
def type_var_infer[T](
        #? 12 typing.TypeVar()
        x: T,
        #? 16 typing.TypeVar()
        *args: T,
        #? 19 typing.TypeVar()
        **kwargs: T,
        ):
    #? tuple()
    args
    #? dict()
    kwargs
    #? typing.TypeVar()
    T

#! 19 ['class TypeVar:']
def type_var_goto[T](
        #! 12 ["T"]
        x: T,
        #! 16 ["T"]
        *args: T,
        #! 19 ["T"]
        **kwargs: T,
        ):
    #! ["*args: T"]
    args
    #! ["**kwargs: T"]
    kwargs
    #! ["T"]
    T

#? 26 typing.TypeVarTuple()
def type_var_tuple_infer[*Ts](
        #? 17 typing.TypeVarTuple()
        *args: *Ts,
        ):
    #? tuple()
    args
    #? typing.TypeVarTuple()
    Ts

#! 26 ['class TypeVarTuple:']
def type_var_tuple_goto[*Ts](
        #! 16 ["*Ts"]
        *args: *Ts,
        ):
    #! ["*args: *Ts"]
    args
    #! ["*Ts"]
    Ts

#? 24 typing.ParamSpec()
def param_spec_infer[**P](
        #? 20 typing.ParamSpecArgs()
        *args: P.args,
        #? 23 typing.ParamSpecKwargs()
        **kwargs: P.kwargs,
        ):
    #? P()
    args
    #? P()
    kwargs
    #? typing.ParamSpec()
    P

#! 23 ["class ParamSpec:"]
def param_spec_goto[**P](
        #! 20 ['def args(self) -> ParamSpecArgs: ...']
        *args: P.args,
        #! 23 ["def kwargs(self) -> ParamSpecKwargs: ..."]
        **kwargs: P.kwargs,
        ):
    #! ["*args: P.args"]
    args
    #! ["**kwargs: P.kwargs"]
    kwargs
    #! ["**P"]
    P

type Recursive = A | list[Recursive]

def recursive_types(x: Recursive):
    #? --contains-subset ["append", "hello_a", "hello_both"]
    x.
    #? ["hello_a", "hello_both"]
    x.hello
    #? --contains-subset ["append", "hello_a", "hello_both"]
    x[0].
    #? ["hello_a", "hello_both"]
    x[0].hello

    #? A() list()
    x
    #? A() list()
    z = x[0]
    #? A() list()
    z

    #! ["z = x[0]"]
    z
    #! ["class A:", "class list(MutableSequence[_T]):"]
    x[0]
    #! ["x: Recursive"]
    x

from dataclasses import dataclass

@dataclass
class D_A():
    attr_x: str

@dataclass
class D_B(D_A):
    attr_y: list[int]

class NormalWithDataclass(D_B):
    attr_z: set[bytes]

#? --contains-subset ['attr_x', 'attr_y']
D_B().
#? ['attr_x', 'attr_y']
D_B().attr_
#? D_B()
D_B()

#? --contains-subset ['attr_x', 'attr_y', 'attr_z']
NormalWithDataclass().
#? ['attr_x', 'attr_y', 'attr_z']
NormalWithDataclass().attr_
#? NormalWithDataclass()
NormalWithDataclass()

def dataclass_test(a: D_A, b: D_B, c: NormalWithDataclass):
    #? D_A()
    a
    #? D_B()
    b
    #? NormalWithDataclass()
    c

    #? str()
    a.attr_x
    #? str()
    b.attr_x
    #? str()
    c.attr_x

    #? ['attr_x']
    a.attr_
    #? ['attr_x', 'attr_y']
    b.attr_
    #? ['attr_x', 'attr_y', 'attr_z']
    c.attr_

from typing import dataclass_transform

@dataclass_transform()
def my_dataclass(cls):
    ...

#? 1 my_dataclass
my_dataclass()

#? my_dataclass
@my_dataclass
class DataclassTransformClass:
    attr: int

#! ["def my_dataclass(cls):"]
@my_dataclass
class OtherDataclassTransformClass:
    attr: int

@dataclass_transform()
class SomeTransfomer: ...

def use_dataclass_transform(x: DataclassTransformClass):
    #? DataclassTransformClass()
    x
    #? int()
    x.attr
    #? ['attr']
    x.att

from enum import Enum

class Enum1(Enum):
    value_a = 1
    value_b = "value_a"

    def value_getter(self) -> str:
        return""

#? ['value_a', 'value_b', 'value_getter']
Enum1.value_
#! ['value_a = 1']
Enum1.value_a
#? value_a()
Enum1.value_a

FunctionalEnum = Enum("FunctionalEnum", {"item_a": int, "item_b": str})

def enum_test(e: Enum1, f: FunctionalEnum):
    #? ['value_a', 'value_b', 'value', 'value_getter']
    e.valu
    #? Enum1()
    e
    #? value_b()
    e.value_b
    #! ["value_b = "value_a""]
    e.value_b

    #? ['item_a', 'item_b']
    f.item
    #? FunctionalEnum()
    f
    #? FunctionalEnum()
    f.item_b
    #! [""FunctionalEnum""]
    f.item_b
