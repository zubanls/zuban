use parsa::NodeIndex;

use super::{Value, ValueKind};
use crate::arguments::Arguments;
use crate::database::Execution;
use crate::file::PythonFile;
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::tree_utils::get_class_name;
use crate::utils::SymbolTable;

#[derive(Debug)]
pub struct Instance<'db, 'a> {
    file: &'db PythonFile,
    symbol_table: &'db SymbolTable,
    node_index: NodeIndex,
    execution: Option<&'a Execution>,
}

impl<'db, 'a> Instance<'db, 'a> {
    pub fn new(
        file: &'db PythonFile,
        node_index: NodeIndex,
        symbol_table: &'db SymbolTable,
        execution: Option<&'a Execution>,
    ) -> Self {
        Self {
            file,
            node_index,
            symbol_table,
            execution,
        }
    }
}

impl<'db, 'a> Value<'db> for Instance<'db, 'a> {
    fn get_kind(&self) -> ValueKind {
        ValueKind::Object
    }

    fn get_name(&self) -> &'db str {
        get_class_name(self.file.tree.get_node_by_index(self.node_index))
    }

    fn lookup(&self, i_s: &mut InferenceState<'db, '_>, name: &str) -> Inferred<'db> {
        if let Some(node_index) = self.symbol_table.lookup_symbol(name) {
            if let Some(execution) = self.execution {
                i_s.run_with_execution(execution, |instance_i_s| {
                    self.file
                        .get_inference(instance_i_s, None)
                        .infer_name_by_index(node_index)
                })
            } else {
                self.file
                    .get_inference(i_s, None)
                    .infer_name_by_index(node_index)
            }
        } else {
            todo!("{:?}", name)
        }
    }

    fn execute(&self, i_s: &mut InferenceState<'db, '_>, args: &Arguments<'db>) -> Inferred<'db> {
        todo!()
    }
}
