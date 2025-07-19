def normal_imports():
    import import_tree
    #! ['import import_tree']
    import_tree
    #! --follow-imports ['module import_tree']
    import_tree

    from import_tree import mod1
    #! ['from import_tree import mod1']
    mod1
    #! --follow-imports ["module import_tree.mod1"]
    mod1

    from import_tree.mod1 import a
    #! ['from import_tree.mod1 import a']
    a
    #! --follow-imports ["a = 1"]
    a

def nested_import_name():
    import import_tree.pkg
    #! ['import import_tree.pkg']
    import_tree
    #! --follow-imports ['module import_tree']
    import_tree

def alias_as_import_name():
    import import_tree as imp1
    #! ['import import_tree as imp1']
    imp1
    #! --follow-imports ['module import_tree']
    imp1

    import import_tree.mod2 as imp2
    #! ['import import_tree.mod2 as imp2']
    imp2
    #! --follow-imports ['module import_tree.mod2']
    imp2

    # a is not a module, but a statement
    import import_tree.mod2.a as imp2
    #! ['import import_tree.mod2 as imp2']
    imp2
    #! --follow-imports ['module import_tree.mod2']
    imp2

def alias_as_import_from():
    from import_tree import mod1 as m1
    #! ['from import_tree import mod1 as m1']
    m1
    #! --follow-imports ["module import_tree.mod1"]
    m1

    from import_tree.mod1 import a as a1
    #! ['from import_tree.mod1 import a as a1']
    a1
    #! --follow-imports ["a = 1"]
    a1

def import_from_multi1():
    from import_tree.mod1 import \
        a as a1,foobarbaz,undefined
    #! ['from import_tree.mod1 import \']
    a1
    #! --follow-imports ["a = 1"]
    a1

    #! ['from import_tree.mod1 import \']
    foobarbaz
    #! --follow-imports ["foobarbaz = 3.0"]
    foobarbaz
    #? float()
    foobarbaz

    #! ['from import_tree.mod1 import \']
    undefined
    #! ['from import_tree.mod1 import \']
    undefined
    #?
    undefined

def import_from_multi2():
    from import_tree.mod1 import (
        a as a1,
        foobarbaz,
        undefined
    )
    #! ['from import_tree.mod1 import (']
    a1
    #! --follow-imports ["a = 1"]
    a1

    #! ['from import_tree.mod1 import (']
    foobarbaz
    #! --follow-imports ["foobarbaz = 3.0"]
    foobarbaz
    #? float()
    foobarbaz

    #! ['from import_tree.mod1 import (']
    undefined
    #! ['from import_tree.mod1 import (']
    undefined
    #?
    undefined

def on_import_no_follow():
    #! 22 ['module import_tree.mod1']
    from import_tree.mod1 import (
        #! 14 ["a = 1"]
        a as a1,
        #! 9 ["a = 1"]
        a as a2,
        #! 9 ["a = 1"]
        a,
        #! 14 ["foobarbaz = 3.0"]
        foobarbaz,
        #! 14 []
        undefined
    )
    #! ['a = 1']
    from import_tree.mod1 import a
    #! ['module import_tree.mod1']
    from import_tree import mod1
    #! ['module import_tree']
    import import_tree
    #! 14 ['module import_tree']
    import import_tree.mod1
    #! ['module import_tree.mod1']
    import import_tree.mod1
    #! []
    import import_tree.mod1.a

    #! 14 ['module import_tree']
    import import_tree.mod1 as m1
    #! 26 ['module import_tree.mod1']
    import import_tree.mod1 as m2
    #! ['module import_tree.mod1']
    import import_tree.mod1 as m2

def on_import_follow():
    #! 22 --follow-imports ['module import_tree.mod1']
    from import_tree.mod1 import (
        #! 14 --follow-imports ["a = 1"]
        a as a1,
        #! 9 --follow-imports ["a = 1"]
        a as a2,
        #! 9 --follow-imports ["a = 1"]
        a,
        #! 14 --follow-imports ["foobarbaz = 3.0"]
        foobarbaz,
        #! 14 --follow-imports []
        undefined
    )
    #! ['a = 1']
    from import_tree.mod1 import a
    #! --follow-imports ['module import_tree.mod1']
    from import_tree import mod1
    #! --follow-imports ['module import_tree']
    import import_tree
    #! 14 --follow-imports ['module import_tree']
    import import_tree.mod1
    #! --follow-imports ['module import_tree.mod1']
    import import_tree.mod1
    #! --follow-imports []
    import import_tree.mod1.a

    #! 14 --follow-imports ['module import_tree']
    import import_tree.mod1 as m1
    #! 26 --follow-imports ['module import_tree.mod1']
    import import_tree.mod1 as m2
    #! ['module import_tree.mod1']
    import import_tree.mod1 as m2

def on_import_infer():
    #? 22 import_tree.mod1
    from import_tree.mod1 import (
        #? 14 int()
        a as a1,
        #? 9 int()
        a as a2,
        #? 9 int()
        a,
        #? 14 float()
        foobarbaz,
        #? 14
        undefined
    )
    #? int()
    from import_tree.mod1 import a
    #? import_tree.mod1
    from import_tree import mod1
    #? import_tree
    import import_tree
    #? 14 import_tree
    import import_tree.mod1
    #? import_tree.mod1
    import import_tree.mod1
    #? 
    import import_tree.mod1.a

    #? 14 import_tree
    import import_tree.mod1 as m1
    #? 26 import_tree.mod1
    import import_tree.mod1 as m2
    #? import_tree.mod1
    import import_tree.mod1 as m2

def on_star_import_follow():
    # pkg has a star import of math
    from import_tree.pkg import *
    #? float()
    pi
    #! ["pi: Final[float]"]
    pi
    #! --follow-imports ["pi: Final[float]"]
    pi

def on_star_import_attr_follow1():
    from import_tree import pkg
    #? float()
    pkg.pi
    ##! ["pi: Final[float]"]
    pkg.pi
    ##! --follow-imports ["pi: Final[float]"]
    pkg.pi

def on_star_import_attr_follow2():
    import import_tree
    #? float()
    import_tree.pkg.pi
    ##! ["pi: Final[float]"]
    import_tree.pkg.pi
    ##! --follow-imports ["pi: Final[float]"]
    import_tree.pkg.pi

def on_star_import_attr_follow3():
    import import_tree
    #! 8 --follow-imports ["module import_tree"]
    import_tree.pkg.pi
    #! 18 --follow-imports ["module import_tree.pkg"]
    import_tree.pkg.pi

    #! 8 ["import import_tree"]
    import_tree.pkg.pi
    #! 18 ["module import_tree.pkg"]
    import_tree.pkg.pi

def on_star_import_attr_follow4():
    import import_tree.pkg
    #! 8 --follow-imports ["module import_tree"]
    import_tree.pkg.pi
    #! 18 --follow-imports ["module import_tree.pkg"]
    import_tree.pkg.pi

    #! 8 ["import import_tree.pkg"]
    import_tree.pkg.pi
    #! 18 ["module import_tree.pkg"]
    import_tree.pkg.pi
