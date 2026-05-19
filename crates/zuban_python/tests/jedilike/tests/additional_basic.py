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

or1 = f(1) or f(1)
or2 = f(1) or f("")
and1 = f("") and f("")
and2 = f("") and f(1.0)
#? int()
or1
#? int() str()
or2
#? str()
and1
#? str() float()
and2

ternary1 = f(1) if bool() else f(1)
ternary2 = f(1) if bool() else f("")
#? int()
ternary1
#? int() str()
ternary2
