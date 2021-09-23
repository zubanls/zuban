use super::{Value, ValueKind};
use crate::arguments::Arguments;
use crate::file::PythonFile;
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::utils::SymbolTable;

#[derive(Debug)]
pub struct Module<'db> {
    file: &'db PythonFile,
    symbol_table: &'db SymbolTable,
}

impl<'db> Module<'db> {
    pub fn new(file: &'db PythonFile, symbol_table: &'db SymbolTable) -> Self {
        Self { file, symbol_table }
    }
}

impl<'db> Value<'db> for Module<'db> {
    fn get_kind(&self) -> ValueKind {
        ValueKind::Object
    }

    fn get_name(&self) -> &'db str {
        todo!()
    }

    fn lookup(&self, i_s: &mut InferenceState<'db, '_>, name: &str) -> Inferred<'db> {
        self.file.calculate_global_definitions_and_references();
        if let Some(node_index) = self.symbol_table.lookup_symbol(name) {
            self.file
                .get_inference(i_s, None)
                .infer_name_by_index(node_index)
        } else {
            todo!()
        }
    }

    fn execute(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        args: &Arguments<'db, '_>,
    ) -> Inferred<'db> {
        todo!()
    }
}
