from pathlib import *
from .x import *
# This import is stupid, because it cycles, but let's keep it in here
from with_star_imports import *
from with_star_imports.y import *

def no_star_import():
    from .z import *

class WithStarImportClass:
    from .z import *

# A symbol that is also present in the stdlib
class MIMEMessage: ...
