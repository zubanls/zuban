def normal_imports() -> None:
    import import_tree
    #! ['import import_tree']
    import_tree
    #! --follow-imports ['module import_tree']
    import_tree

    from import_tree import mod1
    #! ['from import_tree import mod1']
    mod1
    #! --follow-imports ["module import_tree.mod1"]
    mod1

    from import_tree.mod1 import a
    #! ['from import_tree.mod1 import a']
    a
    #! --follow-imports ["a = 1"]
    a
