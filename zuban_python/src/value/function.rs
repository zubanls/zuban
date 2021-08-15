use parsa::NodeIndex;
use parsa::Node;
use parsa_python::PyNode;
use parsa_python::{NonterminalType, PyNodeType::Nonterminal};

use super::{Value, ValueKind};
use crate::file::{PythonFile, Inferred};
use crate::database::Database;

#[derive(Debug)]
pub struct Function<'a> {
    file: &'a PythonFile,
    node_index: NodeIndex,
}

impl<'a> Function<'a> {
    pub fn new(file: &'a PythonFile, node_index: NodeIndex) -> Self {
        Self {file, node_index}
    }

    fn get_node(&self) -> PyNode {
        self.file.tree.get_node_by_index(self.node_index)
    }
}

impl<'a> Value<'a> for Function<'a> {
    fn get_kind(&self) -> ValueKind {
        ValueKind::Function
    }

    fn get_name(&self) -> &'a str {
        let func_node = self.file.tree.get_node_by_index(self.node_index);
        func_node.get_nth_child(1).get_nth_child(0).get_code()
    }

    fn lookup(&self, database: &'a Database, name: &str) -> Inferred<'a> {
        todo!()
    }

    fn execute(&self, database: &'a Database) -> Inferred<'a> {
        let expression = self.get_node().get_nth_child(4);
        // Is an annotation
        if expression.is_type(Nonterminal(NonterminalType::expression)) {
            self.file.infer_arbitrary_node(database, expression.index)
        } else {
            todo!()
        }
    }
}
