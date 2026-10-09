from multi_file2 import recursive_func2, in_multi_file2_func

class Container:
    def __init__(self, x):
        self.x = x

def recursive_func1(x):
    #? int()
    x
    #?
    return recursive_func2(x)

#?
recursive_func1()
#?
recursive_func1(1)

#? int()
in_multi_file2_func(1)
#? int()
in_multi_file2_func(Container(1)).x
