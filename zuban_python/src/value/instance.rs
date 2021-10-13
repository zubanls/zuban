use parsa_python_ast::{ClassDef, NodeIndex};

use super::{Value, ValueKind};
use crate::arguments::Arguments;
use crate::file::PythonFile;
use crate::getitem::SliceType;
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::utils::SymbolTable;

#[derive(Debug)]
pub struct Instance<'db, 'a> {
    file: &'db PythonFile,
    symbol_table: &'db SymbolTable,
    inferred: &'a Inferred<'db>,
    node_index: NodeIndex,
}

impl<'db, 'a> Instance<'db, 'a> {
    pub fn new(
        file: &'db PythonFile,
        node_index: NodeIndex,
        symbol_table: &'db SymbolTable,
        inferred: &'a Inferred<'db>,
    ) -> Self {
        Self {
            file,
            node_index,
            symbol_table,
            inferred,
        }
    }

    pub fn get_node(&self) -> ClassDef<'db> {
        ClassDef::by_index(&self.file.tree, self.node_index)
    }

    pub fn as_inferred(&self) -> &'a Inferred<'db> {
        self.inferred
    }
}

impl<'db, 'a> Value<'db> for Instance<'db, 'a> {
    fn get_kind(&self) -> ValueKind {
        ValueKind::Object
    }

    fn get_name(&self) -> &'db str {
        self.get_node().name().as_str()
    }

    fn lookup(&self, i_s: &mut InferenceState<'db, '_>, name: &str) -> Inferred<'db> {
        if let Some(node_index) = self.symbol_table.lookup_symbol(name) {
            self.file
                .get_inference(i_s)
                .infer_name_by_index(node_index)
                .resolve_function_return(i_s)
                .bind(i_s, self)
        } else {
            todo!("{:?}", name)
        }
    }

    fn execute(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
    ) -> Inferred<'db> {
        todo!()
    }

    fn get_item(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        slice_type: &SliceType<'db>,
    ) -> Inferred<'db> {
        self.lookup(i_s, "__getitem__")
            .run_on_value(i_s, &|i_s, v| v.execute(i_s, &slice_type.as_args()))
    }
}
