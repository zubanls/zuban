#!/usr/bin/env python3
import parso
from timeit import timeit

code = open('/home/dave/source/stuff_jedi/quickfix_huge.py').read()*10

x = parso.parse(code)
print(len(x.children))

#print(timeit(lambda: parso.parse(code), number=5))
