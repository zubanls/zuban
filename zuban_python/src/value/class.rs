use parsa::NodeIndex;

use super::{Function, Value, ValueKind};
use crate::arguments::Arguments;
use crate::database::{Locality, Point, Specific};
use crate::file::PythonFile;
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::tree_utils::get_class_name;
use crate::utils::SymbolTable;

#[derive(Debug)]
pub struct Class<'db> {
    file: &'db PythonFile,
    symbol_table: &'db SymbolTable,
    node_index: NodeIndex,
}

impl<'db> Class<'db> {
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

    pub fn get_init_func(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        args: &Arguments<'db, '_>,
    ) -> Function<'db> {
        let init = self.lookup(i_s, "__init__");
        init.find_function_alternative()
    }
}

impl<'db> Value<'db> for Class<'db> {
    fn get_kind(&self) -> ValueKind {
        ValueKind::Class
    }

    fn get_name(&self) -> &'db str {
        get_class_name(self.file.tree.get_node_by_index(self.node_index))
    }

    fn lookup(&self, i_s: &mut InferenceState<'db, '_>, name: &str) -> Inferred<'db> {
        if let Some(node_index) = self.symbol_table.lookup_symbol(name) {
            self.file.get_inference(i_s).infer_name_by_index(node_index)
        } else {
            todo!()
        }
    }

    fn execute(
        &self,
        database: &mut InferenceState<'db, '_>,
        args: &Arguments<'db, '_>,
    ) -> Inferred<'db> {
        // TODO locality!!!
        let point =
            Point::new_simple_language_specific(Specific::InstanceWithArguments, Locality::Stmt);
        Inferred::new_and_save(args.file, args.primary_node, point)
    }
}
