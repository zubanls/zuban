use std::fmt;

use super::{LookupResult, OnTypeError, Value, ValueKind};
use crate::arguments::Arguments;
use crate::database::{Database, FileIndex, PointLink};
use crate::diagnostics::IssueType;
use crate::file::PythonFile;
use crate::file_state::File;
use crate::imports::python_import;
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::matching::{ClassLike, ResultContext, Type};

impl<'db> fmt::Debug for Module<'db> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("Module")
            .field("file", &self.file.file_path(self.db))
            .finish()
    }
}

#[derive(Copy, Clone)]
pub struct Module<'db> {
    db: &'db Database,
    pub file: &'db PythonFile,
}

impl<'db> Module<'db> {
    pub fn new(db: &'db Database, file: &'db PythonFile) -> Self {
        Self { db, file }
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
        let (dir, mut name) = self.db.vfs.dir_and_name(self.file.file_path(self.db));
        if name.ends_with(".py") {
            name = name.trim_end_matches(".py");
        } else {
            name = name.trim_end_matches(".pyi");
        }
        if name == "__init__" {
            self.db.vfs.dir_and_name(dir.unwrap()).1
        } else {
            name
        }
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

    fn lookup_internal(&self, i_s: &mut InferenceState<'db, '_>, name: &str) -> LookupResult<'db> {
        self.file
            .symbol_table
            .lookup_symbol(name)
            .map(|i| {
                LookupResult::GotoName(
                    PointLink::new(self.file.file_index(), i),
                    self.file.inference(i_s).infer_name_by_index(i),
                )
            })
            .unwrap_or_else(|| {
                self.sub_module(i_s.db, name)
                    .map(|file_index| {
                        // TODO this should probably move to the sub_module
                        i_s.db.add_invalidates(file_index, self.file.file_index());
                        LookupResult::FileReference(file_index)
                    })
                    .unwrap_or_else(|| LookupResult::None)
            })
    }

    fn execute(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
        result_context: ResultContext<'db, '_>,
        on_type_error: OnTypeError<'db, '_>,
    ) -> Inferred<'db> {
        args.as_node_ref().add_typing_issue(
            i_s.db,
            IssueType::NotCallable {
                type_: Box::from("Module"),
            },
        );
        Inferred::new_unknown()
    }

    fn as_type(&self, i_s: &mut InferenceState<'db, '_>) -> Type<'db, 'db> {
        Type::ClassLike(ClassLike::Class(i_s.db.python_state.module_type()))
    }
}
