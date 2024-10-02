extern crate insta;

use parsa_python::*;

fn dedent(s: &'static str) -> String {
    let mut indent = usize::MAX;
    let lines: &Vec<_> = &s.split('\n').collect();
    for line in lines {
        if !line.trim().is_empty() {
            indent = std::cmp::min(indent, line.len() - line.trim_start().len());
        }
    }
    if indent == usize::MAX {
        return s.to_string();
    }
    let new_lines: Vec<_> = lines
        .iter()
        .map(|line| {
            if line.len() >= indent {
                &line[indent..]
            } else {
                line
            }
        })
        .collect();
    new_lines.join("\n")
}

fn tree_to_string(tree: PyTree) -> String {
    fn recurse(code: &mut String, node: &PyNode, depth: usize) {
        *code += &" ".repeat(depth);
        *code += &format!(
            "{}: {}-{}{}\n",
            node.type_str(),
            node.start(),
            node.end(),
            if node.is_leaf() {
                format!(" {:?}", node.as_code())
            } else {
                "".to_string()
            }
        );
        for c in node.iter_children() {
            assert_eq!(node.index, c.parent().unwrap().index);
            recurse(code, &c, depth + 1);
        }
    }

    let root = tree.root_node();
    assert!(root.parent().is_none());
    let mut code = String::new();
    recurse(&mut code, &root, 0);
    code
}

macro_rules! parametrize_snapshots {
    ($($name:ident : $input:expr;)*) => {$(
        #[test]
        fn $name() {
            let tree = parse($input.into());
            insta::assert_snapshot!(stringify!($name), tree_to_string(tree));
        }
    )*}
}

parametrize_snapshots!(
    empty: "".to_owned();
    very_simple: "1".to_owned();
    json: "{foo: 1}\n".to_owned();
    simple: dedent("
        a(bar:=1, foo=1);
        if a:
         1
        else: 2
        ");
    assignments_simple: dedent("
        a = 1
        a, b = 2
        a, b, = 2
        (a, b) = 2
        ((a, b)) = 2
        a = b = 3
        a = (b, c) = 3
        a = (b, c,) = 3
        a = b, c, = 3
        ");
    assignments_star: dedent("
        *foo = *bar = *baz
        i, *foo = ((j, [*bar, k])) = *baz
        *foo, *bar = yield baz
        ");
    assignments_aug: dedent("
        foo += 3
        foo.bar |= 3
        foo, bar += 3
        ");
    assignments_setitem: dedent("
        foo[0] += 3
        foo[0] = a = 3
        foo[a, b] = c
        foo[a::, b:f, c:=3] = c
        ");
    assignments_annotation: dedent("
        foo: bar
        foo: int = 3
        foo.bar: baz
        foo: bar = a = 4
        ");
    assignments_with_call: dedent("
        foo().bar = 1
        foo(1,).bar[1] = 1
        foo(a for a in b).bar[1] = 1
        ");
    for_stmt: dedent("
        for x in [1,2]:
            ...
        for *b in *c: ...
        for c.x, (*b, d.y[0]) in i, *j, k: ...
        ");
    comprehension_simple: dedent("
        [1 for a in b]
        [a for *a, c in b if c if d]
        foo(a for (*a, (*c, b),), in d)
        ");
    comprehension_fails: dedent("
        # fails
        [1 for a in *b]
        [1 for a in b if a else c]
        ");
    del_stmt: dedent("
        del foo
        del foo,
        del foo, bar.baz
        del foo[1]
        ");
    cls: dedent("
        class Foo(object):
            def __init__(self, /, f, *, g):
                pass

            @property
            def prop(self):
                pass
        ");
    import_names: dedent("
        import foo
        import foo.bar as baz
        import foo, bar, baz
        import foo.bar.baz
        ");
    import_name_fails: dedent("
        import foo,
        import foo, bar,
        ");
    import_from_normal: dedent("
        from foo import bar
        from foo import bar as baz
        from foo.bar.baz import *
        ");
    import_from_dotted: dedent("
        from . import (foo as baz, bar)
        from . import (foo, bar,)
        from ..foo import bar as baz
        from ... import *
        ");
    import_from_fails: dedent("
        from . import foo,
        from . import foo, bar,
        ");
    calls: dedent("
        foo(bar)
        foo(bar_foo=3)
        foo(bar_baz:=2)
        foo(**kwargs)
        ");
    nested_call: dedent("
        foo(1)()
        ");
    complex_calls: dedent("
        foo(bar, 3)
        foo(bar, *foo)
        foo(bar, *foo, name=3)
        foo(bar, *foo, name=3, **kwargs)
        foo(bar, *foo, name=3, **kwargs, b=3)
        foo(**kwargs, b=3, **foo)
        ");
    operators: dedent("
        f | d | c + 5 & 2 * 3 * 4 ** 5 ** 6
        ");
    simple_error_recovery: dedent("
        a + 3 +
        b = 3
        ");
    terminal_error_recovery: dedent("
        ?
        ");
    terminal_and_nonterminal_error_recovery: dedent("
        foo
        (1) + ? + c
        bar
        ");
    keyword_recovery: dedent("
        foo
        def
        bar
        else:
        baz
        ");
    match_simple: dedent("
        match foo:
            case ['a']: ...
            case _:
                pass
        ");
    soft_keyword_underscore: dedent("
        match _:
            case ['a']: _(_)
            case _:
                _
        match = 3
        ");
    match_underscore_with_as: dedent("
        match foo:
            case bar as _: pass
        ");
    match_class_pattern: dedent("
        match a:
            case A():
                pass
            case B(1, 2):
                pass
            case B(1, b=2):
                pass
            case B(a=1, b=2):
                pass
        ");
    dict_literal1: dedent("
        {1: 2}
        {**foo}
        {**foo, 1: 2}
        {**foo, **bar}
        ");
    function_simple: dedent("
        def foo(): ...
        def foo(a: 3): ...
        def foo(a, b,): ...
        def foo(a: f = 3, b=4): ...
        def foo(a=3, b=4): ...
        ");
    function_args: dedent("
        def foo(a, *, b=3): ...
        def foo(a=3, *, c): ...
        def foo(a, *, x, **kwargs): ...
        def foo(a, *args: int, **fooo: str,): ...
        def foo(a, /, b: i, c: i=3, **kwargs): ...
        def foo(*args): ...
        ");
    lambda_simple: dedent("
        lambda: ...
        lambda a: ...
        lambda a, b,: ...
        lambda a=3, b=4: ...
        ");
    lambda_slash: dedent("
        lambda a, /, b=3: ...
        lambda a=3, /,: ...
        lambda a=3, /: ...
        lambda a=3, /, *args, c=3: ...
        lambda a=3, /, c=3: ...
        lambda a, /, b, c=3, **kwargs: ...
        lambda a, a=3, /, c=3, *, d: ...
        ");
    lambda_args: dedent("
        lambda a, *, b=3: ...
        lambda a=3, *, c: ...
        lambda a, *, x, **kwargs: ...
        lambda a, *args, **fooo ,: ...
        lambda *args: ...
        ");
    lambda_kwargs: dedent("
        lambda **kwargs: ...
        lambda a=3, **kwargs: ...
        lambda a, **kwargs: ...
        lambda a, /, b, *, x, **kwargs: ...
        ");
    lambda_fails: dedent("
        lambda a, *, **kwargs: ...
        lambda a=3, b: ...
        lambda **a, b: ...
        lambda a=3, *,: ...
        lambda ,: ...
        ");
    lambda_fail_with_slash: dedent("
        lambda a=3, /, b: ...
        lambda a=3, /, b=3, c: ...
        lambda a, /, b=3, c: ...
        lambda z, a=3, d, /, b: ...
        ");
    with_items_simple: dedent("
        with foo as bar: ...
        with foo as bar, baz: ...
        ");
    with_items_parentheses: dedent("
        with (foo as bar): ...
        with (foo as bar, baz): ...
        with ((foo)): ...
        with (i for i in 42): ...
        with (yield y): ...
        ");
    string_literals_in_strings: dedent(r#"
        '"""'
        "'''"
        ""
        ''
        "#);
    bytes: dedent(r#"
        b'asdf\n\''
        br'\asdf'
        Br'asdf"""'
        bR''
        BR'\''
        "#);
    exception_group: dedent(r#"
        try:
            ...
        except* SpamError:
            ...
        except* FooError as e:
            ...
        except* (BarError, BazError) as e:
            ...
        "#);
    invalid_syntax: dedent(r#"
        def f():
            (x,) += 1
            z
        "#);
);
