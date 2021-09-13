def foo(y):
    def bar():
        return y
    return bar


x = foo(1)()
#? int()
x

z = foo("")
#? str()
z()

def foo2(y):
    def decorator():
        def bar():
            return y

        x = bar
        return x
    return decorator


class Foo:
    x = 3

#? Foo
foo2(Foo)()()
#? int()
foo2(1)()()
#? str()
foo2("")()()
