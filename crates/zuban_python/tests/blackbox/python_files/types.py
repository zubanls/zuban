class A:
    hello_a: str
class B:
    hello_b: int

def foo(x: type[A | B], a: type[A]):
    #? ["hello_a", "hello_b"]
    x.hello
    #? str()
    x.hello_a
    #? int()
    x.hello_b
    #! [""]
    x.hello_a
    #! [""]
    x.hello_b

    #! ["hello_a: str"]
    a.hello_a
    #! []
    a.hello_b
