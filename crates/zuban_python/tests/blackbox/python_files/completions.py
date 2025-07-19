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
        var_in_other2 = 1

def deeply_nested():
    var_in_nested = 1
    class NestedClassCompletions:
        var_in_outer_class = 1
        class Inner:
            def var_inner_nested(self):
                var_inner = 1
                #? ["var_global1", "var_global2", "var_in_nested", "var_inner"]
                var_
                #? ["var_in_other_inner", "var_inner_nested", "var_local1", "var_local2", "var_other_inner"]
                self.var_
            var_local1 = 1
            #? ["var_global1", "var_global2", "var_in_nested", "var_inner_nested", "var_local1", "var_local2", "var_other_inner"]
            var_
            var_local2 = 1

            def var_other_inner(self):
                self.var_in_other_inner = 1
                var_in_other2 = 1

        #? ["var_global1", "var_global2", "var_in_nested", "var_in_outer_class", "var_other_outer"]
        var_

        def var_other_outer(self):
            self.var_in_other_outer = 1
            var_in_other2 = 1
            #? ["var_global1", "var_global2", "var_in_nested", "var_in_other2"]
            var_
            #? ["var_in_other_outer", "var_in_outer_class", "var_other_outer"]
            self.var_

var_global2 = 1


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


def lambda_completion(lambda_outer):
    #? ["lambda_completion", "lambda_inner", "lambda_outer"]
    x = lambda lambda_inner: lambda_

    #? ["lambda_completion", "lambda_inner_inner", "lambda_nested", "lambda_outer"]
    x = lambda lambda_nested: lambda lambda_inner_inner: lambda_

# Should not complete, because it's in typing and not builtins
#? []
TypeVa

#? []
import_tre

def dunder_all_test():
    import dunder_all_file
    #? ["attr_x", "attr_y"]
    dunder_all_file.attr_

    import dunder_all_file_i
    #? ["attr_x", "attr_y"]
    dunder_all_file_i.attr_

    #? ["attr_x", "attr_y"]
    from dunder_all_file import attr_

    #? ["attr_x", "attr_y"]
    from dunder_all_file_i import attr_

def dunder_all_star_import_test():
    from dunder_all_file import *
    #? ['attr_x']
    attr_
