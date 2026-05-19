import sys
import os
from os.path import dirname

sys.path.insert(0, os.path.join(dirname(__file__), 'namespace2'))
sys.path.insert(0, os.path.join(dirname(__file__), 'namespace1'))

# zuban-diff: #? ['mod1']
#? []
import pkg1.pkg2.mod1

# zuban-diff: #? ['mod2']
#? []
import pkg1.pkg2.mod2

# zuban-diff: #? ['mod1_name']
#? []
pkg1.pkg2.mod1.mod1_name

# zuban-diff: #? ['mod2_name']
#? []
pkg1.pkg2.mod2.mod2_name
