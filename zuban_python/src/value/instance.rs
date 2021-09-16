use parsa::NodeIndex;

use super::{Value, ValueKind};
use crate::arguments::Arguments;
use crate::file::PythonFile;
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::tree_utils::get_class_name;
use crate::utils::SymbolTable;

#[derive(Debug)]
pub struct Instance<'db> {
    file: &'db PythonFile,
    symbol_table: &'db SymbolTable,
    node_index: NodeIndex,
}

impl<'db> Instance<'db> {
    pub fn new(
        file: &'db PythonFile,
        node_index: NodeIndex,
        symbol_table: &'db SymbolTable,
    ) -> Self {
        Self {
            file,
            node_index,
            symbol_table,
        }
    }
}

impl<'db> Value<'db> for Instance<'db> {
    fn get_kind(&self) -> ValueKind {
        ValueKind::Object
    }

    fn get_name(&self) -> &'db str {
        get_class_name(self.file.tree.get_node_by_index(self.node_index))
    }

    fn lookup(&self, i_s: &mut InferenceState<'db, '_>, name: &str) -> Inferred<'db> {
        if let Some(node_index) = self.symbol_table.lookup_symbol(name) {
            self.file
                .get_inference(i_s, None)
                .infer_name_by_index(node_index)
        } else {
            todo!()
        }
    }

    fn execute(&self, i_s: &mut InferenceState<'db, '_>, args: &Arguments<'db>) -> Inferred<'db> {
        todo!()
    }
}
