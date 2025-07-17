def from_names():
    #? ['base', 'mod1']
    from import_tree.pkg.
    #? ['mod1']
    from import_tree.pkg.mod
    #? ['path']
    from os.

    #? --contains-subset ["import_tree", "math", "os"]
    from 
    #? 9 --contains-subset ["import_tree", "math", "os"]
    from import
    #? 9 --contains-subset ["import_tree", "math", "os"]
    from . import
    #? 9 --contains-subset ["import_tree", "math", "os"]
    from . import whatever
    #? 9 --contains-subset ["import_tree", "math", "os"]
    from import_
    #? 9 --contains-subset ["import_tree", "math", "os"]
    from import_tree.
    #? 9 --contains-subset ["import_tree", "math", "os"]
    from import_tree.pkg
    #? 9 --contains-subset ["import_tree", "math", "os"]
    from import_tree import 
    #? 9 --contains-subset ["import_tree", "math", "os"]
    from import_tree. import 
    #? 9 --contains-subset ["import_tree", "math", "os"]
    from import_tree.pkg import 
    #? 9 --contains-subset ["import_tree", "math", "os"]
    from import_tree.pkg import a

def from_names_goto():
    from import_tree import pkg
    #? import_tree.pkg
    from import_tree.pkg

def builtin_test():
    #? ['math']
    import math
    #? ['mmap']
    import mmap


def import_name_completions():
    #? --contains-subset ['pkg', 'mod1', 'mod2']
    import import_tree.
    #? 25 --contains-subset ['pkg', 'mod1', 'mod2']
    import import_tree.   # whitespace

    #? ['pkg']
    import import_tree.pkg

    #? ['base', 'mod1']
    import import_tree.pkg.
    #? 27 ['base', 'mod1']
    import import_tree.pkg.   # whitespace

    #? ['base']
    import import_tree.pkg.bas

def import_name_completions_with_as():
    #? 23 --contains-subset ['pkg', 'mod1', 'mod2']
    import import_tree. as a1
    #? 25 --contains-subset ['pkg', 'mod1', 'mod2']
    import import_tree.   as a2 # whitespace

    #? 26 ['mod1', 'mod2']
    import import_tree.mod as a3

    #? 27 ['base', 'mod1']
    import import_tree.pkg. as a4
    #? 29 ['base', 'mod1']
    import import_tree.pkg.   as a5 # whitespace

    #? 30 ['base']
    import import_tree.pkg.bas as a6

# -----------------
# completions within imports
# -----------------

#? ['sqlite3']
import sqlite3

# classes is a local module that has an __init__.py and can therefore not be
# found.
# jedi-diff: #? []
#? ['classes']
import classes

#? ['timedelta']
from datetime import timedel
#? 21 []
from datetime.timedel import timedel

# should not be possible, because names can only be looked up 1 level deep.
#? []
from datetime.timedelta import resolution
#? []
from datetime.timedelta import 

#? ['Cursor']
from sqlite3 import Cursor

#? ['some_variable']
from . import some_variable
#? ['arrays']
from . import arrays
#? []
from . import import_tree as ren
#? []
import json as 

import os
# Has different paths depending on operating system so we're removing the test and adding another one
# jedi-diff: #? posixpath.join
from os.path import join
#? typing.get_origin
from typing import get_origin

# -----------------
# special positions -> edge cases
# -----------------
import datetime

#? 6 datetime
from datetime.time import time

#? []
import datetime.
#? []
import datetime.date

#? 21 ['import']
from import_tree.pkg import pkg
#? 49 ['a', 'foobar', "__dict__", "__doc__", "__file__", "__loader__", "__name__", "__package__", "__spec__"]
from import_tree.pkg.mod1 import not_existant,    # whitespace before
#? ['a', 'foobar', "__dict__", "__doc__", "__file__", "__loader__", "__name__", "__package__", "__spec__"]
from import_tree.pkg.mod1 import not_existant, 
#? ['a', 'foobar', "__dict__", "__doc__", "__file__", "__loader__", "__name__", "__package__", "__spec__"]
from import_tree.pkg.mod1 import not_existant,
#? 33 ['a', 'foobar', "__dict__", "__doc__", "__file__", "__loader__", "__name__", "__package__", "__spec__"]
from import_tree.pkg.mod1 import , not_existant
#? 36 ['foobar']
from import_tree.pkg.mod1 import foo, not_existant
#? ['foobar']
from import_tree.pkg.mod1 import not_existant, foo
#? 22 ['base', 'mod1']
from import_tree.pkg. import mod1
#? 17 ['classes', 'flow_import', 'globals', 'invisible_pkg', 'mod1', 'mod2', 'pkg', 'random', 'recurse_class1', 'recurse_class2', 'references', 'rename1', 'rename2']
from import_tree. import new_pkg

#? ['foobar']
from import_tree.pkg.mod1 import (not_existant, foo
#? 51 ['foobar']
from import_tree.pkg.mod1 import (not_existant, foo)
#? 48 --contains-subset ['a', 'foobar', '__file__']
from import_tree.pkg.mod1 import (not_existant, )
from import_tree.pkg.mod1 import (
    not_existant,
#? ['foobar']
    foo
from import_tree.pkg.mod1 import (
    not_existant,
#? ['foobar']
    foo
)

#? 18 ['pkg']
from import_tree.p import pkg

#? 14 ['import_tree']
from import_tre import 
#? 14 ['import_tree']
from import_tre import whatever
#? 18 ['pkg']
from import_tree.p import 
#? 18 ['pkg']
from import_tree.p import whatever
#? 17 --contains-subset ['mod1', 'pkg']
from import_tree. import whatever

#? 17 ['import_tree']
from .import_tree import 
##? 10 ['run']
from ..run import 
##? ['run']
from ..run
##? 10 ['run']
from ..run.
#? []
from ..run.

##? ['run']
from .. import run

#? []
from not_a_module import 


#? json
import json
#? 23 json.dump
from json import load, dump
#? 17 json.load
from json import load, dump
# without the from clause:
import json, datetime
#? 7 json
import json, datetime
#? 13 datetime
import json, datetime

