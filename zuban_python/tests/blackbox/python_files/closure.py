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
