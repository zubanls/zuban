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

list2 = [A(1), A(""), f(1.0)]
#? list()
list2
#? A() float()
list2[0]
#? int() str()
list2[0].val

set2 = {A(1), A(""), f(1.0)}
#? set()
set2
#? A() float()
next(iter(set2))
#? int() str()
next(iter(set2)).val

dict_comp1 = {"x": x for x in f([1])}
#? dict()
dict_comp1
#? int()
dict_comp1["x"]
#? str()
next(iter(dict_comp1.keys()))

dict_comp2 = {x: x for x in f([1.0])}
#? dict()
dict_comp2
#? float()
dict_comp2["x"]
#? float()
dict_comp2[1]
#? float()
next(iter(dict_comp2.keys()))

for tup in dict_comp2.items():
    #? float()
    tup[0]
    #? float()
    tup[1]

dict1 = {"": A(1)}
#? dict()
dict1
#? A()
dict1[""]
#? int()
dict1[""].val
#? A()
dict1["nothing"]
#? int()
dict1["nothing"].val

dict2 = {f("a"): A(1), f("b"): A(""), f("c"): f(1.0)}
#? dict()
dict2
#? A() float()
dict2[""]
#? int() str()
dict2[""].val
#? int() str()
dict2.get("a").val
#? int() str()
dict2.get(NOT_DEFINED).val
# TODO?
#?
dict2.get("not-in-dict").val
#? str()
next(iter(dict2))
#? A() float()
next(iter(dict2.values()))
#? str() int()
next(iter(dict2.values())).val
#? str()
next(iter(dict2.keys()))
for key1 in dict2.keys():
    #? str()
    key1
