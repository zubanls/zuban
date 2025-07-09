raise 1
# Everything after this is considered unreachable and should still work

class Test():
    def __init__(self, testing):
        if isinstance(testing, str):
            self.testing = testing
        else:
            self.testing = 10

    def boo(self):
        if isinstance(self.testing, str):
            # TODO this is wrong, it should only be str.
            # jedi-diff: #? str() int()
            #? str()
            self.testing
            #? Test()
            self
