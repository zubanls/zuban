# -----------------
# non array
# -----------------

#? ['imag']
int.imag

# zuban-diff: #? []
#? ['is_integer']
int.is_integer

#? ['is_integer']
float.is_int

#? ['is_integer']
1.0.is_integer

#? ['upper']
"".upper

#? ['upper']
r"".upper

# strangely this didn't work, because the = is used for assignments
#? ['upper']
"=".upper
a = "="
#? ['upper']
a.upper


# -----------------
# lists
# -----------------
arr = []
#? ['append']
arr.app

#? ['append']
list().app
#? ['append']
[].append

arr2 = [1,2,3]
#? ['append']
arr2.app

#? int()
arr.count(1)

x = []
# zuban-diff: #?
#? int()
x.pop()
x = [3]
#? int()
x.pop()
x = []
x.append(1.0)
# zuban-diff: #? float()
#? int()
x.pop()

# -----------------
# dicts
# -----------------
dic = {}

#? ['clear', 'copy']
dic.c

dic2 = dict(a=1, b=2)
#? ['pop', 'popitem']
dic2.p
#? ['popitem']
{}.popitem

dic2 = {'asdf': 3}
#? ['popitem']
dic2.popitem

#? int()
dic2['asdf']

d = {'a': 3, 1.0: list}

# zuban-diff: #? int() list
#?
d.values()[0]
#? int() list
next(iter(d.values()))
#? int() list
next(iter(dict(d).values()))

#? float() str()
next(iter(d.items()))[0]
#? int() list
next(iter(d.items()))[1]

(a, b), = {a:1 for a in [1.0]}.items()
#? float()
a
#? int()
b

# -----------------
# tuples
# -----------------
tup = ('',2)

#? ['count']
tup.c

tup2 = tuple()
#? ['index']
tup2.i
#? ['index']
().i

tup3 = 1,""
#? ['index']
tup3.index

tup4 = 1,""
#? ['index']
tup4.index

# -----------------
# set
# -----------------
set_t = {1,2}

#? ['clear', 'copy']
set_t.c

set_t2 = set()

#? ['clear', 'copy']
set_t2.c

# -----------------
# pep 448 unpacking generalizations
# -----------------

d = {'a': 3}
dc = {v: 3 for v in ['a']}

#? dict()
{**d}

#? dict()
{**dc}

# zuban-diff: #? str()
#? str() int() list
{**d, "b": "b"}["b"]

# zuban-diff: #? str()
#? str() int()
{**dc, "b": "b"}["b"]

# Should resolve to int() but jedi is not smart enough yet
# Here to make sure it doesn't result in crash though
# zuban-diff: #? 
#? int() list
{**d}["a"]

# Should resolve to int() but jedi is not smart enough yet
# Here to make sure it doesn't result in crash though
# zuban-diff: #? 
#? int()
{**dc}["a"]

s = {1, 2, 3}

#? set()
{*s}

#? set()
{*s, 4, *s}

s = {1, 2, 3}
# Should resolve to int() but jedi is not smart enough yet
# Here to make sure it doesn't result in crash though
# zuban-diff: #? 
#? int()
{*s}.pop()

#? int()
{*s, 4}.pop()

# Should resolve to int() but jedi is not smart enough yet
# Here to make sure it doesn't result in crash though
# zuban-diff: #? 
#? int()
[*s][0]

#? int()
[*s, 4][0]
