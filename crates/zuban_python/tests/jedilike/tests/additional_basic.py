class A:
    def __init__(self, val):
        self.val = val

x = (A(""), A(1))
#? str()
x[0].val
#? A()
x[1]
#? int()
x[1].val

def f(x):
    return x

add1 = f(1) + f(1)
add2 = f("") + f("")
add3 = f("") + f(1)
#? int()
add1
#? str()
add2
#?
add3
