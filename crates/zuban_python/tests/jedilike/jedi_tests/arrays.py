# -----------------
# basic array lookups
# -----------------

# zuban-diff: all lists are inferred without positionals

#? int() str()
[1,""][0]
#? int() str()
[1,""][1]
#? int() str()
[1,""][2]
#? int() str()
[1,""][20]
# zuban-diff: #? int() str()
#?
[1,""][str(hello)]

a = list()
#? list()
[a][0]

#? list()
[[a,a,a]][2][100]

c = [[a,""]]
#? list() str()
c[0][1]

b = [6,7]

#? int()
b[8-7]
# Something unreasonable:
#? int()
b['']

# -----------------
# Slices
# -----------------
#? list()
b[8:]

#? list()
b[int():]

#? list()
b[:]
#? int()
b[:, :-1]

#? 3
b[:]

#? int()
b[:, 1]
#? int()
b[:1, 1]
#? int()
b[1:1, 1]
#? int()
b[1:1:, ...]
#? int()
b[1:1:5, ...]

class _StrangeSlice():
    def __getitem__(self, sliced):
        return sliced

# Should not result in an error, just because the slice itself is returned.
#? slice()
_StrangeSlice()[1:2]

for x in b[:]:
    #? int()
    x

for x in b[:, :-1]:
    #? int()
    x

class Foo:
    def __getitem__(self, item):
        return item

#?
Foo()[:, :-1][0]

# -----------------
# iterable multiplication
# -----------------
c = ['']*2
#? list()
c

# -----------------
# tuple assignments
# -----------------
a1, b1 = (1, "")
#? int()
a1
#? str()
b1

(a2, b2) = (1, "")
#? int()
a2
#? str()
b2

# list assignment
[list1, list2] = (1, "")
#? int()
list1
#? str()
list2

[list3, list4] = [1, ""]
#? int() str()
list3
#? str() int()
list4

# -----------------
# subtuple assignment
# -----------------
(a3, (b3, c3)) = (1, ("", list))
#? list
c3

a4, (b4, c4) = (1, ("", list))
#? list
c4
#? int()
a4
#? str()
b4


# -----------------
# multiple assignments
# -----------------
f1 = g1 = 1
#? int()
f1
#? int()
g1

(f1, g1) = (c, (e, f)) = ('2', (3, 4))
#? str()
f1
#? tuple()
g1
#? str()
c
#? int()
e
#? int()
f


# -----------------
# unnessecary braces
# -----------------
f2 = (1)
#? int()
f2
#? int()
(1)
#? int()
((1))
#? int()
((1)+1)

u, v = 1, ""
#? int()
u

((u1, v1)) = 1, ""
#? int()
u1
#? int()
(u1)

(f3), b = 1, ''
#? int()
f3

def new_func(): return ''
#? str()
(new_func)()
#? str()
(new_func)().title()
#? int()
(tuple).index()
#? int()
(tuple)().index()

class C():
    def __init__(self):
        self.a = (str()).upper()

#? str()
C().a

# -----------------
# imbalanced sides
# -----------------
(f4, g4) = (1,)
# zuban-diff: #? int()
#?
f4
#? []
g4.

(f5, g5, h5) = (1,'')
# zuban-diff: #? int()
#?
f5
# zuban-diff: #? str()
#?
g5
#? []
h5.

(f6, g6) = 1
#? []
f6.
#? []
g6.

(f7, g7) = (1,'',1.0)
# zuban-diff: #? int()
#?
f7
# zuban-diff: #? str()
#?
g7

# -----------------
# setitem
# -----------------

class F:
    setitem_x = [1,2]
    setitem_x[0] = 3

#? ['setitem_x']
F().setitem_x
#? list()
F().setitem_x


# -----------------
# dicts
# -----------------
dic2 = {'asdf': 3, 'b': 'str'}
#? int() str()
dic2['asdf']
#? types.NoneType() int() str()
dic2.get('asdf')

# string literal
#? int() str()
dic2[r'asdf']
#? int() str()
dic2[r'asdf']
#? int() str()
dic2[r'as' 'd' u'f']
#? int() str()
dic2['just_something']

# unpacking
a, b = dic2
#? str()
a
a, b = {1: 'x', 2.0: 1j}
#? int() float()
a
#? int() float()
b


def funcfunc():
    """ github #83 """
    r = {}
    r['status'] = (200, 'ok')
    return r

#? dict()
funcfunc()

# completion within dicts
#? 9 ['str']
{str: str}

# iteration problem (detected with sith)
d = dict({'a':''})
def y(a):
    return a
# zuban-diff: #?
#? str()
y(**d)

#? str()
d['a']

# problem with more complicated casts
dic = {str(key): ''}
#? str()
dic['']


for x in {1: 3.0, '': 1j}:
    #? int() str()
    x

#? ['__iter__']
dict().values().__iter__

d = dict(a=3, b='')
x, = d.values()
#? int() str()
x
#? int() str()
d['a']
#? int() str() types.NoneType()
d.get('a')

some_dct = dict({'a': 1, 'b': ''}, a=1.0)
#? float() str() int()
some_dct['a']
#? int() float() str()
some_dct['b']
#? int() float() str()
some_dct['c']

class Foo:
    pass

objects = {object(): 1, Foo: '', Foo(): 3.0}
#? int() float() str()
objects[Foo]
#? int() float() str()
objects[Foo()]
#? int() float() str()
objects['']

# -----------------
# with variable as index
# -----------------
m1 = (1, "")
index = 1
#? str()
m1[index]

# these should just ouput the whole array
index2 = int
#? int() str()
m1[index2]
index = int()
#? int() str()
m1[index2]

# dicts
index3 = 'asdf'

dic2 = {'asdf': 3, 'b': 'str'}
#? int() str()
dic2[index3]

# -----------------
# __getitem__
# -----------------

class GetItem():
    def __getitem__(self, index):
        return 1.0

#? float()
GetItem()[0]

class GetItem2():
    def __init__(self, el):
        self.el = el

    def __getitem__(self, index):
        return self.el

#? str()
GetItem2("")[1]

class GetItemWithList():
    def __getitem__(self, index):
        return [1, 1.0, 's'][index]

#? float()
GetItemWithList()[1]

for i in 0, 2:
    #? int() float() str()
    GetItemWithList()[i]


# With super
class SuperYeah(list):
    def __getitem__(self, index):
        return super()[index]

#?
SuperYeah([1])[0]
#?
SuperYeah()[0]

# -----------------
# conversions
# -----------------

m2 = [1, ""]
#? int() str()
list(m2)[1]

#? int() str()
list(m2)[0]
#?
set(m2)[0]

#? int() str()
list(set(m2))[1]
#? int() str()
next(iter(set(m2)))
#? int() str()
list(list(set(m2)))[1]

# does not yet work, because the recursion catching is not good enough (catches # to much)
#? int() str()
list(set(list(set(m2))))[1]
#? int() str()
list(set(set(m2)))[1]

# frozenset
#? int() str()
list(frozenset(m2))[1]
#? int() str()
list(set(frozenset(m2)))[1]

# iter
#? int() str()
list(iter(m2))[1]
#? int() str()
list(iter(list(set(m2))))[1]

# tuple
#? int() str()
tuple(m2)[1]
#? int() str()
tuple(list(set(m2)))[1]

#? int()
tuple((1,))[0]

# implementation detail for lists, should not be visible
#? []
list().__iterable

# With a list comprehension.
for i in set(a for a in [1]):
    #? int()
    i


# -----------------
# Merged Arrays
# -----------------

for x in [1] + ['']:
    #? int() str()
    x

# -----------------
# Potential Recursion Issues
# -----------------
class X():
    def y(self):
        self.a = [1]

    def x(self):
        self.a = list(self.a)
        #? int()
        self.a[0]

# -----------------
# For loops with attribute assignment.
# -----------------
def test_func():
    x = 'asdf'
    for x.something in [6,7,8]:
        pass
    #? str()
    x

    for x.something, b in [[6, 6.0]]:
        pass
    #? str()
    x


#? int()
tuple({1})[0]

# -----------------
# PEP 3132 Extended Iterable Unpacking (star unpacking)
# -----------------

a8, *b8, c8 = [1, 'b', list, dict]
#? str() int() dict list
a8
# zuban-diff: #?
#? list()
b8
#? str() int() list dict
c8

# Not valid syntax
a9, *b9, *c9 = [1, 'd', list]
# zuban-diff: #? int()
#?
a9
# zuban-diff: #?
#? list()
b9
# zuban-diff: #?
#? list()
c9

lc = [x for a, *x in [(1, '', 1.0)]]

# zuban-diff #?
#? str() float()
lc[0][0]
# zuban-diff #?
#? str() float()
lc[0][1]
