#!/usr/bin/env python3

from ast import parse
from timeit import timeit
from parser import suite

code = open('/home/dave/source/stuff_jedi/quickfix_huge.py').read()*10

#x = suite(code)
#x = parse(code)
#compile(code, 'foo', 'exec')
#print(timeit(lambda: suite(code), number=5))
