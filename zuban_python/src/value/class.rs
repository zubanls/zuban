use parsa::NodeIndex;
use parsa::Node;

use super::{Value, ValueKind};
use crate::file::{PythonFile};

#[derive(Debug)]
pub struct Class {
    file: *const PythonFile,
    node_index: NodeIndex,
}

impl Class {
    pub fn new(file: *const PythonFile, node_index: NodeIndex) -> Self {
        Self {file, node_index}
    }
}

impl<'a> Value<'a> for Class {
    fn get_kind(&self) -> ValueKind {
        ValueKind::Class
    }

    fn get_name(&self) -> &'a str {
        let class_node = unsafe {&*self.file}.tree.get_node_by_index(self.node_index as usize);
        class_node.get_nth_child(1).get_nth_child(0).get_code()
    }
}
