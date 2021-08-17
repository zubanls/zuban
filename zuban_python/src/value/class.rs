use parsa::NodeIndex;
use parsa::Node;

use super::{Value, ValueKind};
use crate::file::{PythonFile, Inferred};
use crate::utils::SymbolTable;
use crate::database::Database;

#[derive(Debug)]
pub struct Class<'a> {
    file: &'a PythonFile,
    symbol_table: &'a SymbolTable,
    node_index: NodeIndex,
}

impl<'a> Class<'a> {
    pub fn new(file: &'a PythonFile, node_index: NodeIndex, symbol_table: &'a SymbolTable) -> Self {
        Self {file, node_index, symbol_table}
    }
}

impl<'a> Value<'a> for Class<'a> {
    fn get_kind(&self) -> ValueKind {
        ValueKind::Class
    }

    fn get_name(&self) -> &'a str {
        let class_node = self.file.tree.get_node_by_index(self.node_index);
        class_node.get_nth_child(1).get_nth_child(0).get_code()
    }

    fn lookup(&self, database: &'a Database, name: &str) -> Inferred<'a> {
        if let Some(node_index) = self.symbol_table.lookup_symbol(name) {
            self.file.infer_name_by_index(database, node_index)
        } else {
            todo!()
        }
    }

    fn execute(&self, database: &'a Database) -> Inferred<'a> {
        todo!()
    }
}
