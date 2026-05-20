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

factor1 = ~f(1)
factor2 = -f(1)
factor3 = +f("")  # This makes no sense
#? int()
factor1
#? int()
factor2
#? str()
factor3

def return_next(x):
    return next(x)

#? int()
return_next((x for x in [1]))
#? int()
return_next(x for x in [1])
#? int()
return_next((x for x in f([1])))
#? int()
return_next(x for x in f([1]))

#? types.GeneratorType()
f((x for x in [1]))
#? types.GeneratorType()
f(x for x in [1])
#? int()
next(f((x for x in [1])))
#? int()
next(f(x for x in [1]))

list_comp1 = [x for x in f([1])]
#? list()
list_comp1
#? int()
list_comp1[0]

set_comp1 = [x for x in f([1])]
#? list()
set_comp1
#? int()
set_comp1[0]

list1 = [A(1)]
#? list()
list1
#? A()
list1[0]
#? int()
list1[0].val

set1 = {A(1)}
#? set()
set1
#? A()
next(iter(set1))
#? int()
next(iter(set1)).val
