class A:
    hello_a: str
    hello_both: str
class B:
    hello_b: int
    hello_both: int

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

#? 21
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

#! 21 []
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
