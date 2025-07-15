def from_names():
    #? ['base', 'mod1']
    from import_tree.pkg.
    #? ['path']
    from os.

def from_names_goto():
    from import_tree import pkg
    #? import_tree.pkg
    from import_tree.pkg

def builtin_test():
    #? ['math']
    import math
    #? ['mmap']
    import mmap

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
#? 49 ['a', 'foobar', '__name__', '__doc__', '__file__', '__package__']
from import_tree.pkg.mod1 import not_existant,    # whitespace before
#? ['a', 'foobar', '__name__', '__doc__', '__file__', '__package__']
from import_tree.pkg.mod1 import not_existant, 
#? 22 ['base', 'mod1']
from import_tree.pkg. import mod1
#? 17 ['classes', 'flow_import', 'globals', 'invisible_pkg', 'mod1', 'mod2', 'pkg', 'random', 'recurse_class1', 'recurse_class2', 'references', 'rename1', 'rename2']
from import_tree. import new_pkg

#? 18 ['pkg']
from import_tree.p import pkg

#? 17 ['import_tree']
from .import_tree import 
#? 10 ['run']
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

