use crate::file::PythonFile;
use parsa_python::PyNode;

enum ArgumentsDetailed<'a> {
    None,
    Comprehension(PyNode<'a>),
    Node(PyNode<'a>),
}

pub struct Arguments<'a> {
    // The node id of the grammar node called primary, which is defined like
    // primary "(" [arguments | comprehension] ")"
    pub file: &'a PythonFile,
    pub primary_node: PyNode<'a>,
    details: ArgumentsDetailed<'a>,
}

impl<'a> Arguments<'a> {
    pub fn new_empty_arguments(file: &'a PythonFile, primary_node: PyNode<'a>) -> Self {
        Self {
            file,
            primary_node,
            details: ArgumentsDetailed::None,
        }
    }

    pub fn new_comprehension(
        file: &'a PythonFile,
        primary_node: PyNode<'a>,
        comprehension: PyNode<'a>,
    ) -> Self {
        Self {
            file,
            primary_node,
            details: ArgumentsDetailed::Comprehension(comprehension),
        }
    }

    pub fn new_with_arguments(
        file: &'a PythonFile,
        primary_node: PyNode<'a>,
        arguments: PyNode<'a>,
    ) -> Self {
        Self {
            file,
            primary_node,
            details: ArgumentsDetailed::Node(arguments),
        }
    }
}
