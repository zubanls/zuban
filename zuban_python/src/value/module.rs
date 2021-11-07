use super::{Value, ValueKind};
use crate::arguments::Arguments;
use crate::file::PythonFile;
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;

#[derive(Debug)]
pub struct Module<'db> {
    file: &'db PythonFile,
}

impl<'db> Module<'db> {
    pub fn new(file: &'db PythonFile) -> Self {
        Self { file }
    }
}

impl<'db> Value<'db> for Module<'db> {
    fn kind(&self) -> ValueKind {
        ValueKind::Object
    }

    fn name(&self) -> &'db str {
        todo!()
    }

    fn lookup(&self, i_s: &mut InferenceState<'db, '_>, name: &str) -> Inferred<'db> {
        self.file.calculate_global_definitions_and_references();
        if let Some(node_index) = self.file.symbol_table.lookup_symbol(name) {
            self.file.inference(i_s).infer_name_by_index(node_index)
        } else {
            todo!()
        }
    }

    fn execute(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
    ) -> Inferred<'db> {
        todo!()
    }
}
