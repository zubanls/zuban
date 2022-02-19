use std::fmt;

use super::{Value, ValueKind};
use crate::arguments::Arguments;
use crate::database::Database;
use crate::file::PythonFile;
use crate::file_state::File;
use crate::imports::python_import;
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

#[derive(Copy, Clone)]
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
        let path = self.file.file_path(self.database);
        path[path.rfind('/').unwrap() + 1..].trim_end_matches(".py")
    }

    fn module(&self, db: &'db Database) -> Module<'db> {
        *self
    }

    fn is_module(&self) -> bool {
        true
    }

    fn qualified_name(&self, db: &'db Database) -> String {
        self.name().to_owned()
    }

    fn lookup_internal(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        name: &str,
    ) -> Option<Inferred<'db>> {
        self.file
            .inference(i_s)
            .infer_module_name(name)
            .or_else(|| {
                self.file
                    .package_dir
                    .as_ref()
                    .and_then(|dir| {
                        let p = i_s
                            .database
                            .vfs
                            .dir_path(self.file.file_path(i_s.database))
                            .unwrap();
                        python_import(i_s.database, p, dir, name)
                    })
                    .and_then(|file_index| Some(Inferred::new_file_reference(file_index)))
            })
    }

    fn execute(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
    ) -> Inferred<'db> {
        todo!()
    }
}
