use parsa::NodeIndex;

use super::{Value, ValueKind};
use crate::file::{PythonFile, Inferred};
use crate::utils::SymbolTable;
use crate::database::Database;
use crate::tree_utils::get_class_name;

#[derive(Debug)]
pub struct Instance<'a> {
    file: &'a PythonFile,
    symbol_table: &'a SymbolTable,
    node_index: NodeIndex,
}

impl<'a> Instance<'a> {
    pub fn new(file: &'a PythonFile, node_index: NodeIndex, symbol_table: &'a SymbolTable) -> Self {
        Self {file, node_index, symbol_table}
    }
}

impl<'a> Value<'a> for Instance<'a> {
    fn get_kind(&self) -> ValueKind {
        ValueKind::Object
    }

    fn get_name(&self) -> &'a str {
        get_class_name(self.file.tree.get_node_by_index(self.node_index))
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
