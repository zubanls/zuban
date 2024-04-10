use crate::{
    arguments::KnownArgsWithCustomAddIssue,
    database::{Database, FileIndex, PointLink},
    debug,
    diagnostics::IssueType,
    file::{File, PythonFile},
    imports::{python_import, ImportResult},
    inference_state::InferenceState,
    inferred::Inferred,
    matching::LookupResult,
    type_::{Namespace, Type},
    workspaces::{Directory, Parent},
};

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
                return dotted_path_from_dir(&dir);
            }
        }
        if let Ok(parent_dir) = entry.parent.maybe_dir() {
            dotted_path_from_dir(&parent_dir) + "." + name
        } else {
            name.to_string()
        }
    }

    pub(crate) fn lookup(
        &self,
        i_s: &InferenceState,
        add_issue: impl Fn(IssueType),
        name: &str,
    ) -> LookupResult {
        self.lookup_with_is_import(i_s, add_issue, name, false)
    }

    pub(crate) fn lookup_with_is_import(
        &self,
        i_s: &InferenceState,
        add_issue: impl Fn(IssueType),
        name: &str,
        is_import: bool,
    ) -> LookupResult {
        if let Some(index) = self.file.symbol_table.lookup_symbol(name) {
            let link = PointLink::new(self.file.file_index(), index);
            LookupResult::GotoName {
                name: link,
                inf: if is_import {
                    Inferred::from_saved_link(link)
                } else {
                    self.file
                        .inference(i_s)
                        .infer_name_of_definition_by_index(index)
                },
            }
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
            let inf = if is_import {
                Inferred::from_saved_link(link)
            } else {
                i_s.db
                    .loaded_python_file(link.file)
                    .inference(i_s)
                    .infer_name_of_definition_by_index(link.node_index)
            };
            LookupResult::GotoName { name: link, inf }
        } else if let Some(inf) = self.maybe_execute_getattr(i_s, &add_issue) {
            LookupResult::UnknownName(inf)
        } else if name == "__getattr__" {
            // There is a weird (and wrong) definition in typeshed that defines __getattr__ on
            // ModuleType:
            // https://github.com/python/typeshed/blob/516f6655051b061652f086445ea54e8e82232349/stdlib/types.pyi#L352
            LookupResult::None
        } else {
            i_s.db
                .python_state
                .module_instance()
                .type_lookup(i_s, |issue| add_issue(issue), name)
        }
    }

    pub(crate) fn maybe_execute_getattr(
        &self,
        i_s: &InferenceState,
        add_issue: &'a dyn Fn(IssueType),
    ) -> Option<Inferred> {
        self.file.lookup_global("__getattr__").map(|link| {
            let inf = i_s
                .db
                .loaded_python_file(link.file)
                .inference(i_s)
                .infer_name_of_definition_by_index(link.node_index);
            inf.execute(
                i_s,
                &KnownArgsWithCustomAddIssue::new(
                    &Inferred::from_type(i_s.db.python_state.str_type()),
                    add_issue,
                ),
            )
        })
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
