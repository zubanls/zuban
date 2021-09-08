use super::{Value, ValueKind};
use crate::arguments::Arguments;
use crate::database::Database;
use crate::file::PythonFile;
use crate::inferred::Inferred;
use crate::utils::SymbolTable;

#[derive(Debug)]
pub struct Module<'a> {
    file: &'a PythonFile,
    symbol_table: &'a SymbolTable,
}

impl<'a> Module<'a> {
    pub fn new(file: &'a PythonFile, symbol_table: &'a SymbolTable) -> Self {
        Self { file, symbol_table }
    }
}

impl<'a> Value<'a> for Module<'a> {
    fn get_kind(&self) -> ValueKind {
        ValueKind::Object
    }

    fn get_name(&self) -> &'a str {
        todo!()
    }

    fn lookup(&self, database: &'a Database, name: &str) -> Inferred<'a> {
        self.file.calculate_global_definitions_and_references();
        if let Some(node_index) = self.symbol_table.lookup_symbol(name) {
            self.file.infer_name_by_index(database, node_index)
        } else {
            todo!()
        }
    }

    fn execute(&self, database: &'a Database, args: &Arguments<'a>) -> Inferred<'a> {
        todo!()
    }
}
