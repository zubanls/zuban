def foo(y):
    def bar():
        return y
    return bar


x = foo(1)()
#? int()
x

z = foo("")
##? str()
z()

def foo2(y):
    def decorator():
        def bar():
            return y

        x = bar
        return x
    return decorator


class Foo:
    def __init__(self, a):
        self.a = a

    x = 3

#? Foo
foo2(Foo)()()
##? int()
foo2(1)()()
##? str()
foo2("")()()


def executor(cls):
    def wrapper(x):
        return cls(x)
    return wrapper

#? Foo()
executor(Foo)(1)
##? int()
executor(Foo)(1).a
