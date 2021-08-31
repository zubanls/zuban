use parsa::NodeIndex;

use super::{Value, ValueKind};
use crate::arguments::Arguments;
use crate::database::{Database, Locality, Point, Specific};
use crate::file::{Inferred, PythonFile};
use crate::tree_utils::get_class_name;
use crate::utils::SymbolTable;

#[derive(Debug)]
pub struct Class<'a> {
    file: &'a PythonFile,
    symbol_table: &'a SymbolTable,
    node_index: NodeIndex,
}

impl<'a> Class<'a> {
    pub fn new(file: &'a PythonFile, node_index: NodeIndex, symbol_table: &'a SymbolTable) -> Self {
        Self {
            file,
            node_index,
            symbol_table,
        }
    }
}

impl<'a> Value<'a> for Class<'a> {
    fn get_kind(&self) -> ValueKind {
        ValueKind::Class
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

    fn execute(&self, database: &'a Database, args: &Arguments<'a>) -> Inferred<'a> {
        // TODO locality!!!
        let point =
            Point::new_simple_language_specific(Specific::InstanceWithArguments, Locality::Stmt);
        Inferred::new_and_save(args.file, args.primary_node_index, point)
    }
}
