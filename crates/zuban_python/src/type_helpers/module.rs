use std::rc::Rc;

use parsa_python_cst::{DottedAsNameContent, DottedNameContent, NameImportParent};
use vfs::{FileEntry, FileIndex, Parent};

use crate::{
    arguments::KnownArgsWithCustomAddIssue,
    database::Database,
    debug,
    diagnostics::IssueKind,
    file::{process_unfinished_partials, PythonFile, FLOW_ANALYSIS},
    imports::{namespace_import, python_import_with_needs_exact_case, ImportResult},
    inference_state::InferenceState,
    inferred::Inferred,
    node_ref::NodeRef,
    type_::{AnyCause, LookupResult, Namespace, Type},
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

    fn file_entry_and_is_package(&self, db: &'a Database) -> (&'a Rc<FileEntry>, bool) {
        let entry = self.file.file_entry(db);
        (
            entry,
            &*entry.name == "__init__.py" || &*entry.name == "__init__.pyi",
        )
    }

    pub fn sub_module(&self, db: &'a Database, name: &str) -> Option<ImportResult> {
        let (entry, is_package) = self.file_entry_and_is_package(db);
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

    pub(crate) fn lookup(
        &self,
        db: &Database,
        add_issue: impl Fn(IssueKind),
        name: &str,
    ) -> LookupResult {
        let i_s = &InferenceState::new(db);
        if let Some(name_ref) = self.file.lookup_global(name) {
            let ensure_flow_analysis = || {
                if self.file.inference(i_s).calculate_diagnostics().is_err() {
                    add_issue(IssueKind::CannotDetermineType { for_: name.into() });
                    return Some(LookupResult::any(AnyCause::FromError));
                }
                None
            };
            let p = name_ref.point();
            if p.calculated() && p.needs_flow_analysis() {
                if let Some(result) = ensure_flow_analysis() {
                    return result;
                }
            }
            if let Some(r) = self.maybe_submodule_reexport(i_s, name_ref, name) {
                return r;
            }
            if is_reexport_issue(db, name_ref) {
                add_issue(IssueKind::ImportStubNoExplicitReexport {
                    module_name: self.file.qualified_name(db).into(),
                    attribute: name.into(),
                })
            }
            let r = FLOW_ANALYSIS.with(|fa| {
                fa.with_new_empty_without_unfinished_partial_checking(|| {
                    name_ref.infer_name_of_definition_by_index(i_s)
                })
            });
            if !r.unfinished_partials.is_empty() {
                if let Some(result) = ensure_flow_analysis() {
                    return result;
                }
                process_unfinished_partials(i_s, r.unfinished_partials);
                // In case where the partial is overwritten, we can just return the old Inferred,
                // because it points to the correct place.
            }
            LookupResult::GotoName {
                name: name_ref.as_link(),
                inf: r.result,
            }
        } else if let Some(result) = self.sub_module_lookup(db, name) {
            result
        } else if let Some(star_imp) = self
            .file
            .name_resolution(i_s)
            .lookup_from_star_import(name, false)
        {
            star_imp.into_lookup_result(i_s)
        } else if let Some(inf) = self.maybe_execute_getattr(i_s, &add_issue) {
            LookupResult::UnknownName(inf)
        } else if name == "__getattr__" {
            // There is a weird (and wrong) definition in typeshed that defines __getattr__ on
            // ModuleType:
            // https://github.com/python/typeshed/blob/516f6655051b061652f086445ea54e8e82232349/stdlib/types.pyi#L352
            LookupResult::None
        } else {
            if name == "__path__" && !self.file_entry_and_is_package(db).1 {
                return LookupResult::None;
            }
            let mut result = db
                .python_state
                .module_instance()
                .type_lookup(i_s, add_issue, name);
            if matches!(name, "__spec__" | "__file__" | "__package__") {
                // __spec__ is special, because it always has a ModuleSpec and only if the module
                // is __main__ it sometimes doesn't. But since __main__ is only ever known to Mypy
                // as a static file it will also have a ModuleSpec and never be None, therefore we
                // simply remove the None here.
                // Also do the same for __file__ / __package__
                // https://docs.python.org/3/reference/import.html#main-spec
                result = result.and_then(|inf| Some(inf.remove_none(i_s))).unwrap()
            }
            result
        }
    }

    fn maybe_submodule_reexport(
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
                        .name_resolution(i_s)
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
                                .name_resolution(i_s)
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

    pub(crate) fn maybe_execute_getattr(
        &self,
        i_s: &InferenceState,
        add_issue: &'a dyn Fn(IssueKind),
    ) -> Option<Inferred> {
        self.file.lookup_global("__getattr__").map(|name_ref| {
            let inf = name_ref.infer_name_of_definition_by_index(i_s);
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
