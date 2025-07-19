"""
Special cases of completions (typically special positions that caused issues
with value parsing.
"""

def pass_decorator(func):
    return func


def x():
    return (
        1,
#? ["tuple"]
tuple
    )

    # Comment just somewhere


class MyClass:
    @pass_decorator
    def x(foo,
#? 5 []
tuple,
          ):
        return 1


if x:
    pass
#? ['else']
else

try:
    pass
#? ['except', 'Exception']
except

try:
    pass
#? 6 ['except', 'Exception']
except AttributeError:
    pass
#? ['finally']
finally

for x in y:
    pass
#? ['else']
else

def star_completions1():
    from math import *
    #? ['cos', 'cosh']
    cos

def star_completions2():
    from import_tree.pkg import *
    #? ['cos', 'cosh']
    cos

def star_completions3():
    from import_tree import pkg
    #? ["comb", "copysign", "cos", "cosh"]
    pkg.co

from import_tree.pkg.base import *

#? ['MyBase']
MyBas
