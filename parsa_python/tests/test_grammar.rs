extern crate insta;

use parsa_python::*;

#[test]
fn test_x() {
    let tree = PYTHON_GRAMMAR.parse("{foo: 1}\n");
    let root_node = tree.get_root_node();
    assert_eq!(root_node.node_type(), Some(PythonNodeType::file_input));
    assert_eq!(root_node.get_extra_data(), 0);
}


fn tree_to_string(tree: PythonTree) -> String {
    fn recurse(code: &mut String, node: &PythonNode, depth: usize) {
        *code += &" ".repeat(depth);
        *code += &format!(
            "{}: {}-{}{}\n", node.type_str(), node.start(), node.end(),
            if node.is_leaf() {format!(" {:?}", node.get_code())} else {"".to_string()}
        );
        dbg!(node);
        for c in node.get_children() {
            recurse(code, &c, depth + 1);
        }
    };

    let mut code = String::new();
    recurse(&mut code, &tree.get_root_node(), 0);
    code
}

macro_rules! parametrize_snapshots {
    ($($name:ident : $input:expr;)*) => {$(
        #[test]
        fn $name() {
            let tree = PYTHON_GRAMMAR.parse($input);
            insta::assert_snapshot!("expected", tree_to_string(tree));
        }
    )*}
}

parametrize_snapshots!(
    json: "{foo: 1}\n";
);
