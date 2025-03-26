use parsa_python_cst::{DottedAsNameContent, DottedNameContent, NameImportParent};
use vfs::{FileIndex, Parent};

use crate::{
    database::Database,
    debug,
    file::PythonFile,
    imports::{namespace_import, python_import_with_needs_exact_case, ImportResult},
    inference_state::InferenceState,
    inferred::Inferred,
    node_ref::NodeRef,
    type_::{AnyCause, LookupResult, Namespace, Type},
};

#[derive(Copy, Clone)]
pub(crate) struct Module<'a> {
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
        let (entry, is_package) = self.file.file_entry_and_is_package(db);
        if !is_package {
            return None;
        }
        match &entry.parent {
            Parent::Directory(dir) => python_import_with_needs_exact_case(
                db,
                self.file,
                std::iter::once((dir.upgrade().unwrap(), false)),
                name,
                true,
            )
            .or_else(|| {
                if self.file.in_partial_stubs(db) {
                    Module::new(self.file.normal_file_of_stub_file(db)?).sub_module(db, name)
                } else {
                    None
                }
            }),
            Parent::Workspace(_) => None,
        }
    }

    pub fn sub_module_lookup(&self, db: &'a Database, name: &str) -> Option<LookupResult> {
        Some(match self.sub_module(db, name)? {
            ImportResult::File(file_index) => LookupResult::FileReference(file_index),
            ImportResult::Namespace(ns) => {
                LookupResult::UnknownName(Inferred::from_type(Type::Namespace(ns)))
            }
            ImportResult::PyTypedMissing => unreachable!(),
        })
    }

    pub fn maybe_submodule_reexport(
        &self,
        i_s: &InferenceState,
        name_ref: NodeRef,
        name: &str,
    ) -> Option<LookupResult> {
        let Some(import) = name_ref.maybe_import_of_name_in_symbol_table() else {
            return None;
        };
        let submodule_reexport = |import_result| {
            if let Some(ImportResult::File(f)) = import_result {
                if f == self.file.file_index {
                    return Some(
                        self.sub_module_lookup(i_s.db, name)
                            .unwrap_or(LookupResult::None),
                    );
                }
            }
            None
        };
        match import {
            NameImportParent::ImportFromAsName(imp) => {
                let import_from = imp.import_from();
                // from . import x simply imports the module that exists in the same
                // directory anyway and should not be considered a reexport.
                submodule_reexport(
                    self.file
                        .name_resolution_for_types(i_s)
                        .import_from_first_part(import_from),
                )
            }
            NameImportParent::DottedAsName(dotted) => {
                if let DottedAsNameContent::WithAs(dotted, _) = dotted.unpack() {
                    // Only import `foo.bar as bar` can be a submodule.
                    // `import foo.bar` just exports the name foo.
                    if let DottedNameContent::DottedName(super_, _) = dotted.unpack() {
                        submodule_reexport(
                            self.file
                                .name_resolution_for_types(i_s)
                                .cache_import_dotted_name(super_, None),
                        )
                    } else {
                        None
                    }
                } else {
                    None
                }
            }
        }
    }
}

pub fn lookup_in_namespace(
    db: &Database,
    from_file: &PythonFile,
    namespace: &Namespace,
    name: &str,
) -> LookupResult {
    match namespace_import(db, from_file, namespace, name) {
        Some(ImportResult::File(file_index)) => LookupResult::FileReference(file_index),
        Some(ImportResult::Namespace(namespace)) => {
            LookupResult::UnknownName(Inferred::from_type(Type::Namespace(namespace)))
        }
        Some(ImportResult::PyTypedMissing) => LookupResult::any(AnyCause::FromError),
        None => {
            debug!("TODO namespace basic lookups");
            LookupResult::None
        }
    }
}

pub fn is_reexport_issue(db: &Database, name_ref: NodeRef) -> bool {
    if !name_ref.file.is_stub() && !name_ref.file.flags(db).no_implicit_reexport {
        return false;
    }
    if let Some(dunder_all) = name_ref.file.maybe_dunder_all(db) {
        debug_assert!(name_ref.maybe_name().is_some());
        let name = name_ref.as_code();
        if dunder_all.iter().any(|d| d.as_str(db) == name) || name == "__all__" {
            // Name was exported in __all__
            return false;
        }
    }
    is_private_import(name_ref)
}

pub fn is_private_import(name_ref: NodeRef) -> bool {
    name_ref
        .maybe_import_of_name_in_symbol_table()
        .is_some_and(|i| !i.is_stub_reexport())
}
