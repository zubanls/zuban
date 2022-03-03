use std::fmt;

use super::{Value, ValueKind};
use crate::arguments::Arguments;
use crate::database::{Database, FileIndex};
use crate::diagnostics::IssueType;
use crate::file::PythonFile;
use crate::file_state::File;
use crate::imports::python_import;
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;

impl<'db> fmt::Debug for Module<'db> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("Module")
            .field("file", &self.file.file_path(self.database))
            .finish()
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

    pub fn sub_module(&self, db: &'db Database, name: &str) -> Option<FileIndex> {
        self.file.package_dir.as_ref().and_then(|dir| {
            let p = db.vfs.dir_path(self.file.file_path(db)).unwrap();
            python_import(db, p, dir, name)
        })
    }
}

impl<'db> Value<'db, '_> for Module<'db> {
    fn kind(&self) -> ValueKind {
        ValueKind::Object
    }

    fn name(&self) -> &'db str {
        // TODO this is not correct...
        let path = self.file.file_path(self.database);
        path[path.rfind('/').unwrap() + 1..]
            .trim_end_matches(".py")
            .trim_end_matches(".pyi")
    }

    fn module(&self, db: &'db Database) -> Module<'db> {
        *self
    }

    fn as_module(&self) -> Option<&Self> {
        Some(self)
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
                self.sub_module(i_s.database, name).map(|file_index| {
                    i_s.database
                        .add_invalidates(file_index, self.file.file_index());
                    Inferred::new_file_reference(file_index)
                })
            })
    }

    fn execute(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
    ) -> Inferred<'db> {
        args.node_reference()
            .add_typing_issue(i_s.database, IssueType::NotCallable("Module".to_owned()));
        Inferred::new_unknown()
    }
}
