# Additional tests to the ones in from_jedi_python_files/named_param.py
def foo(abcdef, abcdgg, abcdhh):
    pass

#? 8 ["abcdef=", "abcdgg=", "abcdhh="]
foo(abcd).a = 1
#? 8 ["abcdef=", "abcdgg=", "abcdhh="]
foo(abcd.a = 1
#? 9 []
foo([abcd])
#? 14 []
foo([abcd, abcd])
#? 14 []
foo([abcd, abc)
#? 14 []
foo([abcd, abc
#? 14 []
foo(abcdef.abc)
#? 14 []
foo(abcdef.abc)
#? 17 []
foo(1, abcdef.abc)
#? 17
foo(1, abcdef.abc
