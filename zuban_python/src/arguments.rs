use parsa_python::PyNode;

pub enum Arguments<'a> {
    None,
    Comprehension(PyNode<'a>),
    Node(PyNode<'a>),
}
