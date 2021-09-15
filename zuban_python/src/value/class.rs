use parsa::NodeIndex;

use super::{Value, ValueKind};
use crate::arguments::Arguments;
use crate::database::{Locality, Point, Specific};
use crate::file::PythonFile;
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::tree_utils::get_class_name;
use crate::utils::SymbolTable;

#[derive(Debug)]
pub struct Class<'a, 'b> {
    file: &'a PythonFile,
    symbol_table: &'b SymbolTable,
    node_index: NodeIndex,
}

impl<'a, 'b> Class<'a, 'b> {
    pub fn new(file: &'a PythonFile, node_index: NodeIndex, symbol_table: &'b SymbolTable) -> Self {
        Self {
            file,
            node_index,
            symbol_table,
        }
    }
}

impl<'a, 'b> Value<'a> for Class<'a, 'b> {
    fn get_kind(&self) -> ValueKind {
        ValueKind::Class
    }

    fn get_name(&self) -> &'a str {
        get_class_name(self.file.tree.get_node_by_index(self.node_index))
    }

    fn lookup(&self, i_s: &mut InferenceState<'a>, name: &str) -> Inferred<'a> {
        if let Some(node_index) = self.symbol_table.lookup_symbol(name) {
            self.file
                .get_inference(i_s, None)
                .infer_name_by_index(node_index)
        } else {
            todo!()
        }
    }

    fn execute(&self, database: &mut InferenceState<'a>, args: &Arguments<'a>) -> Inferred<'a> {
        // TODO locality!!!
        let point =
            Point::new_simple_language_specific(Specific::InstanceWithArguments, Locality::Stmt);
        Inferred::new_and_save(args.file, args.primary_node, point)
    }
}
