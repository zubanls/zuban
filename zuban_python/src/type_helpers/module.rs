use crate::database::{Database, FileIndex, PointLink};
use crate::type_::{Namespace, Type};

use crate::debug;
use crate::file::File;
use crate::file::PythonFile;
use crate::imports::{python_import, ImportResult};
use crate::inference_state::InferenceState;
use crate::node_ref::NodeRef;

use crate::inferred::Inferred;
use crate::matching::LookupResult;
use crate::workspaces::{Directory, Parent};

#[derive(Copy, Clone)]
pub struct Module<'a> {
    pub file: &'a PythonFile,
}

impl<'a> Module<'a> {
    pub fn new(file: &'a PythonFile) -> Self {
        Self { file }
    }

    pub fn from_file_index(db: &'a Database, file_index: FileIndex) -> Self {
        Self::new(db.loaded_python_file(file_index))
    }

    pub fn sub_module(&self, db: &'a Database, name: &str) -> Option<ImportResult> {
        let entry = self.file.file_entry(db);
        match &entry.parent {
            Parent::Directory(dir) => {
                if &*entry.name != "__init__.py" && &*entry.name != "__init__.pyi" {
                    return None;
                }
                let p = db.vfs.dir_path(self.file.file_path(db)).unwrap();
                python_import(db, self.file.file_index(), p, &dir.upgrade().unwrap(), name)
            }
            Parent::Workspace(_) => None,
        }
    }

    pub fn qualified_name(&self, db: &Database) -> String {
        let entry = self.file.file_entry(db);
        let name = &entry.name;
        let name = if let Some(n) = name.strip_suffix(".py") {
            n
        } else {
            name.trim_end_matches(".pyi")
        };
        if name == "__init__" {
            if let Ok(dir) = entry.parent.maybe_dir() {
                return dir.name.to_string();
            }
        }
        if let Ok(parent_dir) = entry.parent.maybe_dir() {
            dotted_path_from_dir(&parent_dir) + "." + name
        } else {
            name.to_string()
        }
    }

    pub fn lookup(&self, i_s: &InferenceState, from: NodeRef, name: &str) -> LookupResult {
        if let Some(link) = self.file.symbol_table.lookup_symbol(name) {
            LookupResult::GotoName(
                PointLink::new(self.file.file_index(), link),
                self.file.inference(i_s).infer_name_by_index(link),
            )
        } else if let Some(sub_module) = self.sub_module(i_s.db, name) {
            match sub_module {
                ImportResult::File(file_index) => LookupResult::FileReference(file_index),
                ImportResult::Namespace { .. } => todo!(),
            }
        } else if let Some(link) = self
            .file
            .inference(i_s)
            .lookup_from_star_import(name, false)
        {
            let inf = i_s
                .db
                .loaded_python_file(link.file)
                .inference(i_s)
                .infer_name_by_index(link.node_index);
            LookupResult::GotoName(link, inf)
        } else {
            i_s.db
                .python_state
                .module_instance()
                .type_lookup(i_s, from, name)
        }
    }
}

pub fn lookup_in_namespace(
    db: &Database,
    from_file: FileIndex,
    namespace: &Namespace,
    name: &str,
) -> LookupResult {
    match python_import(db, from_file, &namespace.path, &namespace.content, name) {
        Some(ImportResult::File(file_index)) => LookupResult::FileReference(file_index),
        Some(ImportResult::Namespace(namespace)) => {
            LookupResult::UnknownName(Inferred::from_type(Type::Namespace(namespace)))
        }
        None => {
            debug!("TODO namespace basic lookups");
            LookupResult::None
        }
    }
}

pub fn dotted_path_from_dir(dir: &Directory) -> String {
    if let Ok(parent_dir) = dir.parent.maybe_dir() {
        dotted_path_from_dir(&parent_dir) + "." + &dir.name
    } else {
        dir.name.to_string()
    }
}
