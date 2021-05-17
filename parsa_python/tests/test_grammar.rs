extern crate insta;

use parsa_python::*;
use parsa::Node;

fn dedent(s: &'static str) -> String {
    let mut indent = usize::MAX;
    let lines: &Vec<_> = &s.split('\n').collect();
    for line in lines {
        if line.trim().len() > 0 {
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

fn tree_to_string(tree: PythonTree) -> String {
    fn recurse(code: &mut String, node: &PythonNode, depth: usize) {
        *code += &" ".repeat(depth);
        *code += &format!(
            "{}: {}-{}{}\n",
            node.type_str(),
            node.start(),
            node.end(),
            if node.is_leaf() {
                format!(" {:?}", node.get_code())
            } else {
                "".to_string()
            }
        );
        for c in node.iter_children() {
            assert_eq!(node.index, c.get_parent().unwrap().index);
            recurse(code, &c, depth + 1);
        }
    }

    let root = tree.get_root_node();
    assert!(root.get_parent().is_none());
    let mut code = String::new();
    recurse(&mut code, &root, 0);
    code
}

macro_rules! parametrize_snapshots {
    ($($name:ident : $input:expr;)*) => {$(
        #[test]
        fn $name() {
            let tree = PYTHON_GRAMMAR.parse($input);
            insta::assert_snapshot!(stringify!($name), tree_to_string(tree));
        }
    )*}
}

parametrize_snapshots!(
    json: "{foo: 1}\n".to_owned();
    simple: dedent("
        a(bar:=1, foo=1);
        if a:
         1
        else: 2
        ");
    cls: dedent("
        class Foo(object):
            def __init__(self, /, f, *, g):
                pass

            @property
            def prop(self):
                pass
        ");
    imports: dedent("
        import foo
        import foo.bar as baz
        from foo import bar
        from foo import bar as baz
        import foo, bar, baz
        from foo import *
        from . import (foo, bar)
        from . import (foo, bar,)
        ");
    calls: dedent("
        foo(bar)
        foo(bar_foo=3)
        foo(bar_baz:=2)
        foo(**kwargs)
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
);
