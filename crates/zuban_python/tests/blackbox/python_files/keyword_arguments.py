# Additional tests to the ones in from_jedi_python_files/named_param.py
def foo(abcdef, abcdgg, abcdhh):
    pass

#? 8 ["abcdef=", "abcdgg=", "abcdhh="]
foo(abcd).a = 1
#? 8 ["abcdef=", "abcdgg=", "abcdhh="]
foo(abcd.a = 1
