class BaseDep:
    def __init__(self, x=1.0):
        self.x = x

    class_var = 1


def func1(c):
    return c, 1


def func2(c: int) -> str:
    return 1
