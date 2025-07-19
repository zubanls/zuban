var_global1 = 1
def func_completions():
    def var_nested():
        var_inner = 1
        #? ["var_global1", "var_global2", "var_inner", "var_local1", "var_local2", "var_nested"]
        var_
    var_local1 = 1
    #? ["var_global1", "var_global2", "var_local1", "var_local2", "var_nested"]
    var_
    var_local2 = 1

var_global2 = 1


class ClassCompletions:
    def var_nested(self):
        var_inner = 1
        #? ["var_global1", "var_global2", "var_inner"]
        var_
        #? ["var_in_other", "var_local1", "var_local2", "var_nested", "var_other"]
        self.var_
    var_local1 = 1
    #? ["var_global1", "var_global2", "var_local1", "var_local2", "var_nested", "var_other"]
    var_
    var_local2 = 1

    def var_other(self):
        self.var_in_other = 1


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

class StarCompletions1:
    from math import *
    #? ['cos', 'cosh']
    cos

class StarCompletions2:
    from import_tree.pkg import *
    #? ['cos', 'cosh']
    cos

class StarCompletions3:
    from import_tree import pkg
    #? ["comb", "copysign", "cos", "cosh"]
    pkg.co
