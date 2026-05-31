"""
Code that might cause recursion issues (or has caused in the past).
"""

def Recursion():
    def recurse(self):
        self.a = self.a
        self.b = self.b.recurse()

#?
Recursion().a

#?
Recursion().b


class X():
    def __init__(self):
        self.recursive = [1, 3]

    def annoying(self):
        self.recursive = [self.recursive[0]]

    def recurse(self):
        self.recursive = [self.recursive[1]]

#? int()
X().recursive[0]


def to_list(iterable):
    return list(set(iterable))


def recursion1(foo):
    return to_list(to_list(foo)) + recursion1(foo)

# zuban-diff: #? int()
#?
recursion1([1,2])[0]


class FooListComp():
    def __init__(self):
        self.recursive = [1]

    def annoying(self):
        self.recursive = [x for x in self.recursive]


#? int()
FooListComp().recursive[0]


class InstanceAttributeIfs:
    def b(self):
        self.a1 = 1
        self.a2 = 1

    def c(self):
        self.a2 = ''

    def x(self):
        self.b()

        if self.a1 == 1:
            self.a1 = self.a1 + 1
        if self.a2 == UNDEFINED:
            self.a2 = self.a2 + 1

        #? int()
        self.a1
        # zuban-diff: #? int() str()
        #? int()
        self.a2

#? int()
InstanceAttributeIfs().a1
# zuban-diff: #? int() str()
#? int()
InstanceAttributeIfs().a2



class A:
    def a(self, b):
        for x in [self.a(i) for i in b]:
            #?
            x

class B:
    def a(self, b):
        for i in b:
            for i in self.a(i):
                #?
                yield i


foo = int
foo = foo  # type: foo
#? int
foo

while True:
    bar = int
    bar = bar  # type: bar
    # zuban-diff: #? int()
    #? int
    bar


class Comprehension:
    def __init__(self, foo):
        self.foo = foo

    def update(self):
        self.foo = (self.foo,)


# zuban-diff: #? int() tuple()
#?
Comprehension(1).foo[0]
#? int()
Comprehension(1).foo

# Only for zuban

class Container:
    def __init__(self, x):
        self.x = x

def f1(x): return f2(x)
def f2(x): return f3(x)
def f3(x): return f4(x)
def f4(x): return f5(x)
def f5(x): return f6(x)
def f6(x): return f7(x)
def f7(x): return f8(x)
def f8(x): return f9(x)
def f9(x): return f10(x)
def f10(x): return f11(x)
def f11(x): return Container(x)

#?
f1(1).x
#?
f1("").x

f2(1).x
#? str()
f2("").x

def g1(x): return g2(x)
def g2(x): return g3(x)
def g3(x): return g4(x)
def g4(x): return g5(x)
def g5(x): return g6(x)
def g6(x): return g7(x)
def g7(x): return g8(x)
def g8(x): return g9(x)
def g9(x): return g10(x)
def g10(x): return g11(x)
def g11(x): return g12(x)
def g12(x): return g13(x)
def g13(x): return g14(x)
def g14(x): return g15(x)
def g15(x): return g16(x)
def g16(x): return g17(x)
def g17(x): return g18(x)
def g18(x): return g19(x)
def g19(x): return g20(x)
#? 24 int() str()
def g20(x): return g21(x)
#?
def g21(x): return g22(x)
def g22(x): return x

#?
g1(1)
#?
g1("")
