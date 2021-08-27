use parsa::NodeIndex;
use parsa_python::PyNode;

enum ArgumentsDetailed<'a> {
    None,
    Comprehension(PyNode<'a>),
    Node(PyNode<'a>),
}

pub struct Arguments<'a> {
    // The node id of the grammar node called primary, which is defined like
    // primary "(" [arguments | comprehension] ")"
    pub primary_node_index: NodeIndex,
    details: ArgumentsDetailed<'a>,
}

impl<'a> Arguments<'a> {
    pub fn new_empty_arguments(primary_node_index: NodeIndex) -> Self {
        Self {primary_node_index, details: ArgumentsDetailed::None}
    }

    pub fn new_comprehension(primary_node_index: NodeIndex, comprehension: PyNode<'a>) -> Self {
        Self {primary_node_index, details: ArgumentsDetailed::Comprehension(comprehension)}
    }

    pub fn new_with_arguments(primary_node_index: NodeIndex, arguments: PyNode<'a>) -> Self {
        Self {primary_node_index, details: ArgumentsDetailed::Node(arguments)}
    }
}
