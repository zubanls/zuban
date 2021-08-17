use parsa::Node;
use parsa_python::{NonterminalType, PyNode, PyNodeType::Nonterminal};

pub fn get_class_name(class_node: PyNode) -> &str {
    debug_assert_eq!(class_node.get_type(), Nonterminal(NonterminalType::class_def));
    class_node.get_nth_child(1).get_nth_child(0).get_code()
}
