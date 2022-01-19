use std::fmt;

use super::{Value, ValueKind};
use crate::arguments::Arguments;
use crate::database::Database;
use crate::file::PythonFile;
use crate::file_state::File;
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;

impl<'db> fmt::Debug for Module<'db> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        todo!()
        /*
        f.debug_struct("Function")
            .field("file", self.reference.file)
            .field("node", &self.node())
            .finish()
            */
    }
}

pub struct Module<'db> {
    database: &'db Database,
    file: &'db PythonFile,
}

impl<'db> Module<'db> {
    pub fn new(database: &'db Database, file: &'db PythonFile) -> Self {
        Self { database, file }
    }
}

impl<'db> Value<'db, '_> for Module<'db> {
    fn kind(&self) -> ValueKind {
        ValueKind::Object
    }

    fn name(&self) -> &'db str {
        // TODO this is not correct...
        self.file.file_path(self.database)
    }

    fn lookup(&self, i_s: &mut InferenceState<'db, '_>, name: &str) -> Inferred<'db> {
        self.file
            .inference(i_s)
            .infer_module_name(name)
            .unwrap_or_else(|| todo!())
    }

    fn execute(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
    ) -> Inferred<'db> {
        todo!()
    }
}
