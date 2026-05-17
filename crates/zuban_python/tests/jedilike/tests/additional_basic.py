class A:
    def __init__(self, val):
        self.val = val

x = (A(""), A(1))
#? str()
x[0].val
#? A()
x[1]
#? int()
x[1].val
