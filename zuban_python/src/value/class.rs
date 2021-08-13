use parsa::NodeIndex;
use parsa::Node;

use super::{Value, ValueKind};
use crate::file::{PythonFile, Inferred};
use crate::utils::SymbolTable;
use crate::database::Database;

#[derive(Debug)]
pub struct Class {
    file: *const PythonFile,
    symbol_table: SymbolTable,
    node_index: NodeIndex,
}

impl Class {
    pub fn new(file: *const PythonFile, node_index: NodeIndex, symbol_table: SymbolTable) -> Self {
        Self {file, node_index, symbol_table}
    }
}

impl<'a> Value<'a> for Class {
    fn get_kind(&self) -> ValueKind {
        ValueKind::Class
    }

    fn get_name(&self) -> &'a str {
        let class_node = unsafe {&*self.file}.tree.get_node_by_index(self.node_index);
        class_node.get_nth_child(1).get_nth_child(0).get_code()
    }

    fn lookup(&self, database: &'a Database, name: &str) -> Inferred<'a> {
        if let Some(node_index) = self.symbol_table.lookup_symbol(name) {
            unsafe {&*self.file}.infer_arbitrary_node(database, node_index)
        } else {
            todo!()
        }
    }
}
