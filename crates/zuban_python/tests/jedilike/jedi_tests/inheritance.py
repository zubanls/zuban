
class Super(object):
    attribute = 3

    def func(self):
        return 1

    class Inner():
        pass


class Sub(Super):
    #? 13 Sub.attribute
    def attribute(self):
        pass

    # zuban-diff: #! 8 ['attribute = 3']
    #! 8 ['def attribute(self):']
    def attribute(self):
        pass

    #! 4 ['def func(self):']
    func = 3
    # zuban-diff #! 12 ['class func(): pass']
    #! 12 ['func = 3']
    class func(): pass

    #! 8 ['class Inner']
    def Inner(self): pass

# -----------------
# Finding self
# -----------------

class Test1:
    class Test2:
        def __init__(self):
            self.foo_nested = 0
            #? ['foo_nested']
            self.foo_
            #?
            self.foo_here

    def __init__(self, self2):
        self.foo_here = 3
        # zuban-diff #? ['foo_here', 'foo_in_func']
        #? ['foo_here', 'foo_in_func', 'foo_not_on_self']
        self.foo_
        #? int()
        self.foo_here
        #?
        self.foo_nested
        # zuban-diff #?
        #? int()
        self.foo_not_on_self
        #? float()
        self.foo_in_func
        self2.foo_on_second = ''

        def closure():
            self.foo_in_func = 4.

    def bar(self):
        self = 3
        self.foo_not_on_self = 3


class SubTest(Test1):
    def __init__(self):
        self.foo_sub_class = list

    def bar(self):
        # zuban-diff: #? ['foo_here', 'foo_in_func', 'foo_sub_class']
        #? ['foo_here', 'foo_in_func', 'foo_not_on_self', 'foo_sub_class']
        self.foo_
        #? int()
        self.foo_here
        #?
        self.foo_nested
        # zuban-diff #?
        #? int()
        self.foo_not_on_self
