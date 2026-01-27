""" Mostly for stupid error reports of @dbrgn. :-) """

import time

class Foo(object):
    global time
    asdf = time

def asdfy():
    return Foo

xorz = getattr(asdfy()(), 'asdf')
# zuban-diff: #? time
#? 
xorz



def args_returner(*args):
    return args


#? tuple()
args_returner(1)[:]
# zuban-diff #? int()
#? 
args_returner(1)[:][0]


def kwargs_returner(**kwargs):
    return kwargs


#? dict()
kwargs_returner(a=1)
#?
kwargs_returner(a=1)[:]
#?
kwargs_returner(b=1)[:][0]
