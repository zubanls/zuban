class A:
    hello_a: str
class B:
    hello_b: int

def foo(x: type[A | B]):
    #? ["hello_a", "hello_b"]
    x.hello
    #? str()
    x.hello_a
    #? int()
    x.hello_b
