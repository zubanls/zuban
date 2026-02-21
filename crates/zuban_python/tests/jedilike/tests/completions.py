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

def primary_target_completions():
    import import_tree
    #? 14 ['import_tree']
    import_tre.mod1.a = 3
    #? 17 ['mod1', 'mod2']
    import_tree.m.a = 4
    #? 22 ['a']
    import_tree.mod1.a = 5
    #? 22 ['a']
    import_tree.mod1.a.x = 5
    #? 21 --contains-subset ['a', 'c', 'foobarbaz']
    import_tree.mod1. = 5
    #? 4 --contains-subset ["help", "str"]
    .mod1.a = 6

def no_completion_inside_string_test():
    some_variable = 1
    #? 14 --no-name-filter []
    " some_var "
    #? 16 --no-name-filter []
    """ some_var """

def typed_dict():
    from typing import TypedDict
    class NestedTypedDict(TypedDict):
        nested_field_foo: str
        nested_field_bar: int
    class SomeTypedDict(TypedDict):
        some_field_foo: str
        some_field_bar: int
        nested_dict: NestedTypedDict

    def complete_typed_dict_key(_dict: SomeTypedDict):
        #? ['some_field_foo"', 'some_field_bar"', 'nested_dict"']
        _dict["
        #? ['some_field_foo"', 'some_field_bar"']
        _dict["some
        #? 18 ['some_field_foo', 'some_field_bar']
        _dict["some"]
        #? ['nested_field_foo"', 'nested_field_bar"']
        _dict["nested_dict"]["nested
        #? 15 []
        _dict[""]
        #? 14 ['some_field_foo', 'some_field_bar', 'nested_dict']
        _dict[""]
        #? ['some_field_foo'', 'some_field_bar'']
        _dict['some
        #? --contains-subset [""some_field_foo"", ""some_field_bar"", ""nested_dict"", "ArithmeticError", "AssertionError", "AttributeError"]
        _dict[

def default_and_annotation_completion():
    class FooBarBaz: ...
    #? 19 ["FooBarBaz"]
    def f1(f=FooBarB)
    #? 19 ["FooBarBaz"]
    def f2(f=FooBarB): ...
    #? 19 ["FooBarBaz"]
    def f3(f:FooBarB)
    #? 19 ["FooBarBaz"]
    def f4(f:FooBarB): ...
