use std::fmt;

use super::{LookupResult, Value};

use crate::database::{Database, DbType, FileIndex, PointLink};

use crate::file::File;
use crate::file::PythonFile;
use crate::imports::python_import;
use crate::inference_state::InferenceState;

use crate::matching::Type;
use crate::node_ref::NodeRef;

impl<'a> fmt::Debug for Module<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("Module")
            .field("file", &self.file.file_path(self.db))
            .finish()
    }
}

#[derive(Copy, Clone)]
pub struct Module<'a> {
    db: &'a Database,
    pub file: &'a PythonFile,
}

impl<'a> Module<'a> {
    pub fn new(db: &'a Database, file: &'a PythonFile) -> Self {
        Self { db, file }
    }

    pub fn sub_module(&self, db: &'a Database, name: &str) -> Option<FileIndex> {
        self.file.package_dir.as_ref().and_then(|dir| {
            let p = db.vfs.dir_path(self.file.file_path(db)).unwrap();
            python_import(db, p, dir, name)
        })
    }

    pub fn name(&self) -> &'a str {
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

    pub fn qualified_name(&self, db: &Database) -> String {
        self.name().to_owned()
    }

    pub fn lookup(
        &self,
        i_s: &InferenceState,
        node_ref: Option<NodeRef>,
        name: &str,
    ) -> LookupResult {
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
}

impl<'db: 'a, 'a> Value<'db, 'a> for Module<'a> {
    fn as_type(&self, i_s: &InferenceState<'db, '_>) -> Type<'a> {
        Type::owned(DbType::Module(self.file.file_index()))
    }
}
