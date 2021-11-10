#? int()
[1,""][0]
#? str()
[1,""][1]
#? str() int()
[1,""][x]

foo: list[int] = ""

#? list()
foo

#? int()
foo[0]

#? int()
foo.pop()

bar = list([1])

#? list()
bar

foo = list([1, 2])
#? int()
foo[0]
