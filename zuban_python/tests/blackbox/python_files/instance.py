class Foo:
    def __init__(self, a):
        self.a = a

    x = 3

#? int()
Foo.x
##?
Foo.a
#? int()
Foo().x
##?
Foo().a
#? int()
Foo(1).a
