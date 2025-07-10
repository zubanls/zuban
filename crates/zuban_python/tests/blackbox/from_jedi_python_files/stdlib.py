"""
std library stuff
"""

# -----------------
# builtins
# -----------------
arr = ['']

#? str()
sorted(arr)[0]

#? str()
next(reversed(arr))
next(reversed(arr))

# should not fail if there's no return value.
def yielder():
    yield None

#? None
next(reversed(yielder()))

# empty reversed should not raise an error
#?
next(reversed())

# jedi-diff: #? str() bytes()
#? str()
next(open(''))

#? int()
{'a':2}.setdefault('a', 3)

# Compiled classes should have the meta class attributes.
#? ['__itemsize__']
tuple.__itemsize__
#? []
tuple().__itemsize__

# -----------------
# type() calls with one parameter
# -----------------
#? int
type(1)
#? int
type(int())
#? type
type(int)
#? type
type(type)
#? list
type([])

def x():
    yield 1
generator = type(x())
# jedi-diff: #? generator
#? typing.Generator
type(x for x in [])
#? type(x)
type(lambda: x)

import math
import os
# jedi-diff: #? type(os)
#? types.ModuleType
type(math)
class XX(): pass
#? type
type(XX)

# -----------------
# type() calls with multiple parameters
# -----------------

Xt = type('Xt', (object,), dict(a=1))

# Doesn't work yet.
#?
Xt.a
#?
Xt

if os.path.isfile():
    #? ['abspath']
    fails = os.path.abspath

# The type vars and other underscored things from typeshed should not be
# findable. (in zuban errors are raised, but you can find them)
# jedi-diff: #?
#? typing.TypeVar()
os._T


with open('foo') as f:
    for line in f.readlines():
        # jedi-diff: #? str() bytes()
        #? str()
        line
# -----------------
# enumerate
# -----------------
for i, j in enumerate(["as", "ad"]):
    #? int()
    i
    #? str()
    j

# -----------------
# re
# -----------------
import re
c = re.compile(r'a')
# re.compile should not return str -> issue #68
#? []
c.startswith
#? int()
c.match().start()

#? int()
re.match(r'a', 'a').start()

for a in re.finditer('a', 'a'):
    #? int()
    a.start()

# -----------------
# ref
# -----------------
import weakref

#? int()
weakref.proxy(1)

# jedi-diff: #? weakref.ref()
#? weakref.ReferenceType()
weakref.ref(1)
#? int() types.NoneType()
weakref.ref(1)()

# -----------------
# sqlite3 (#84)
# -----------------

import sqlite3
#? sqlite3.Connection()
con = sqlite3.connect()
#? sqlite3.Cursor()
c = con.cursor()

def huhu(db):
    """
        :type db: sqlite3.Connection
        :param db: the db connection
    """
    #? sqlite3.Connection()
    db

with sqlite3.connect() as c:
    #? sqlite3.Connection()
    c

# -----------------
# hashlib
# -----------------

import hashlib

#? ['md5']
hashlib.md5

# -----------------
# copy
# -----------------

import copy
#? int()
copy.deepcopy(1)

#?
copy.copy()

# -----------------
# json
# -----------------

# We don't want any results for json, because it depends on IO.
import json
#?
json.load('asdf')
#?
json.loads('[1]')

# -----------------
# random
# -----------------

import random
class A(object):
    def say(self): pass
class B(object):
    def shout(self): pass
cls = random.choice([A, B])
#? ['say', 'shout']
cls().s

# -----------------
# random
# -----------------

import zipfile
z = zipfile.ZipFile("foo")
#? ['upper']
z.read('name').upper

# -----------------
# contextlib
# -----------------

from typing import Iterator
import contextlib
with contextlib.closing('asd') as string:
    #? str()
    string

@contextlib.contextmanager
def cm1() -> Iterator[float]:
    yield 1
with cm1() as xcontext:
    #? float()
    xcontext

@contextlib.contextmanager
def cm2() -> float:
    yield 1
with cm2() as xcontext:
    #?
    xcontext

@contextlib.contextmanager
def cm3():
    yield 3
with cm3() as xcontext:
    #? int()
    xcontext

# -----------------
# operator
# -----------------

import operator

f = operator.itemgetter(1)
#? float()
f([1.0])
#? str()
f([1, ''])

g = operator.itemgetter(1, 2)
x1, x2 = g([1, 1.0, ''])
#? float()
x1
#? str()
x2

x1, x2 = g([1, ''])
#? str()
x1
#? int() str()
x2

# -----------------
# shlex
# -----------------

# Github issue #929
import shlex
qsplit = shlex.split("foo, ferwerwerw werw werw e")
for part in qsplit:
    #? str()
    part

# -----------------
# staticmethod, classmethod params
# -----------------

class F():
    def __init__(self):
        self.my_variable = 3

    @staticmethod
    def my_func(param):
        #? []
        param.my_
        #? ['upper']
        param.uppe
        #? str()
        return param

    @staticmethod
    def my_func_without_call(param):
        #? []
        param.my_
        #? []
        param.uppe
        #?
        return param

    @classmethod
    def my_method_without_call(cls, param):
        #?
        cls.my_variable
        #? ['my_method', 'my_method_without_call']
        cls.my_meth
        #?
        return param

    @classmethod
    def my_method(cls, param):
        #?
        cls.my_variable
        #? ['my_method', 'my_method_without_call']
        cls.my_meth
        #?
        return param

#? str()
F.my_func('')
#? str()
F.my_method('')

# -----------------
# Unknown metaclass
# -----------------

# Github issue 1321
class Meta(object):
    pass

class Test(metaclass=Meta):
    def test_function(self):
        result = super(Test, self).test_function()
        #? []
        result.

# -----------------
# Enum
# -----------------

import enum

class XE(enum.Enum):
    attr_x = 3
    attr_y = 2.0

#? ['mro']
XE.mro
#? ['attr_x', 'attr_y']
XE.attr_
#? str()
XE.attr_x.name
#? int()
XE.attr_x.value
#? str()
XE.attr_y.name
#? float()
XE.attr_y.value
#? str()
XE().name
#? float()
XE().attr_x.attr_y.value

# -----------------
# functools
# -----------------
import functools

basetwo = functools.partial(int, base=2)
#? int()
basetwo()

def function(a, b):
    return a, b
a = functools.partial(function, 0)

#? int()
a('')[0]
#? str()
a('')[1]

kw = functools.partial(function, b=1.0)
tup = kw(1)
#? int()
tup[0]
#? float()
tup[1]

def my_decorator(f):
    @functools.wraps(f)
    def wrapper(*args, **kwds):
        return f(*args, **kwds)
    return wrapper

@my_decorator
def example(a):
    return a

#? str()
example('')

# From GH #1574
#? float()
functools.wraps(functools.partial(str, 1))(lambda: 1.0)()

class X:
    def function(self, a, b):
        return a, b
    a = functools.partialmethod(function, 0)
    kw = functools.partialmethod(function, b=1.0)
    just_partial = functools.partial(function, 1, 2.0)

#? int()
X().a('')[0]
#? str()
X().a('')[1]

# The access of partialmethods on classes are not 100% correct. This doesn't
# really matter, because nobody uses it like that anyway and would take quite a
# bit of work to fix all of these cases.
#? str()
X.a('')[0]
#?
X.a('')[1]

#? X()
X.a(X(), '')[0]
#? str()
X.a(X(), '')[1]

tup = X().kw(1)
#? int()
tup[0]
#? float()
tup[1]

tup = X.kw(1)
#?
tup[0]
#? float()
tup[1]

tup = X.kw(X(), 1)
#? int()
tup[0]
#? float()
tup[1]

#? float()
X.just_partial('')[0]
#? str()
X.just_partial('')[1]
#? float()
X().just_partial('')[0]
#? str()
X().just_partial('')[1]

# python >= 3.8

@functools.lru_cache
def cached_x() -> int: ...
@functools.lru_cache()
def cached_y() -> float: ...
@functools.lru_cache(8)
def cached_z() -> str: ...

#? int()
cached_x()
#? float()
cached_y()
#? str()
cached_z()
