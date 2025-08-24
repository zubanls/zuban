use parsa_python_cst::{
    DottedAsName, DottedAsNameContent, DottedImportName, DottedImportNameContent, Name,
    NameImportParent,
};
use vfs::{Directory, Parent};

use crate::{
    database::{Database, Locality, Point, PointKind, Specific},
    debug,
    diagnostics::IssueKind,
    imports::{global_import, namespace_import, python_import_with_needs_exact_case, ImportResult},
    inference_state::InferenceState,
    inferred::Inferred,
    node_ref::NodeRef,
    type_::{LookupResult, Type},
};

use super::PythonFile;

impl PythonFile {
    pub(super) fn global_import(&self, db: &Database, name: Name) -> Option<ImportResult> {
        let result = global_import(db, self, name.as_str());
        if let Some(result) = &result {
            debug!(
                "Global import '{}': {:?}",
                name.as_code(),
                result.debug_info(db),
            );
        }
        result
    }

    pub fn cache_import_dotted_name(
        &self,
        db: &Database,
        dotted: DottedImportName,
        base: Option<ImportResult>,
    ) -> Option<ImportResult> {
        let node_ref = NodeRef::new(self, dotted.index());
        let p = node_ref.point();
        if p.calculated() {
            return load_saved_results(node_ref, p);
        }
        let infer_name = |base, name: Name| {
            let mut in_stub_and_has_getattr = false;
            let result = match &base {
                ImportResult::File(file_index) => {
                    let module = db.loaded_python_file(*file_index);
                    let r = module.sub_module(db, name.as_str());

                    // This is such weird logic. I don't understand at all why Mypy is doing this.
                    // It seems to come from here:
                    // https://github.com/python/mypy/blob/bc591c756a453bb6a78a31e734b1f0aa475e90e0/mypy/semanal_pass1.py#L87-L96
                    if r.is_none()
                        && module.is_stub()
                        && module.lookup_symbol("__getattr__").is_some()
                    {
                        in_stub_and_has_getattr = true
                    }
                    r
                }
                ImportResult::Namespace(namespace) => {
                    namespace_import(db, self, namespace, name.as_str())
                }
                ImportResult::PyTypedMissing => Some(ImportResult::PyTypedMissing),
            };
            if let Some(imported) = &result {
                debug!(
                    "Imported {:?} for {:?}",
                    imported.debug_info(db),
                    dotted.as_code(),
                );
            } else if in_stub_and_has_getattr {
                debug!(
                    "Ignored import of {}, because of a __getattr__ in a stub file",
                    name.as_str()
                );
            } else {
                let module_name = format!("{}.{}", base.qualified_name(db), name.as_str()).into();
                if !self.flags(db).ignore_missing_imports {
                    NodeRef::new(self, name.index())
                        .add_type_issue(db, IssueKind::ModuleNotFound { module_name });
                }
            }
            result
        };
        let result = match dotted.unpack() {
            DottedImportNameContent::Name(name) => {
                if let Some(base) = base {
                    infer_name(base, name)
                } else {
                    let result = self.global_import(db, name);
                    if result.is_none() {
                        self.add_module_not_found(db, name)
                    }
                    result
                }
            }
            DottedImportNameContent::DottedName(dotted_name, name) => {
                let result = self.cache_import_dotted_name(db, dotted_name, base)?;
                infer_name(result, name)
            }
        };
        cache_import_results(node_ref, &result);
        result
    }

    pub(super) fn infer_dotted_as_name_import(
        &self,
        db: &Database,
        dotted_as_name: DottedAsName,
    ) -> Inferred {
        match self.cache_dotted_as_name_import(db, dotted_as_name) {
            Some(import_result) => import_result.as_inferred(),
            None => Inferred::new_module_not_found(),
        }
    }

    pub(super) fn cache_dotted_as_name_import(
        &self,
        db: &Database,
        dotted_as_name: DottedAsName,
    ) -> Option<ImportResult> {
        let saved_at = NodeRef::new(self, dotted_as_name.index());
        let point = saved_at.point();
        if point.calculated() {
            return load_saved_results(saved_at, point);
        }
        let result = match dotted_as_name.unpack() {
            DottedAsNameContent::Simple(name_def, rest) => {
                let result = self.global_import(db, name_def.name());
                if result.is_none() {
                    self.add_module_not_found(db, name_def.name())
                }
                if let Some(rest) = rest {
                    if result.is_some() {
                        self.cache_import_dotted_name(db, rest, result.clone());
                    }
                }
                result
            }
            DottedAsNameContent::WithAs(dotted_name, _) => {
                self.cache_import_dotted_name(db, dotted_name, None)
            }
        };
        cache_import_results(saved_at, &result);
        result
    }

    pub(super) fn add_module_not_found(&self, db: &Database, name: Name) {
        if !self.flags(db).ignore_missing_imports {
            NodeRef::new(self, name.index()).add_type_issue(
                db,
                IssueKind::ModuleNotFound {
                    module_name: Box::from(name.as_str()),
                },
            );
        }
    }

    pub fn sub_module(&self, db: &Database, name: &str) -> Option<ImportResult> {
        let (entry, is_package) = self.file_entry_and_is_package(db);
        if !is_package {
            return None;
        }
        match &entry.parent {
            Parent::Directory(dir) => python_import_with_needs_exact_case(
                db,
                self,
                std::iter::once((
                    Directory::entries(&*db.vfs.handler, &dir.upgrade().unwrap()),
                    false,
                )),
                name,
                true,
                true,
            )
            .or_else(|| {
                if self.in_partial_stubs(db) {
                    self.normal_file_of_stub_file(db)?.sub_module(db, name)
                } else {
                    None
                }
            }),
            Parent::Workspace(_) => None,
        }
    }

    pub fn sub_module_lookup(&self, db: &Database, name: &str) -> Option<LookupResult> {
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
                if f == self.file_index {
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
                let import_from = imp.import_from()?;
                // from . import x simply imports the module that exists in the same
                // directory anyway and should not be considered a reexport.
                submodule_reexport(
                    self.name_resolution_for_types(i_s)
                        .import_from_first_part(import_from),
                )
            }
            NameImportParent::DottedAsName(dotted) => {
                if let DottedAsNameContent::WithAs(dotted, _) = dotted.unpack() {
                    // Only import `foo.bar as bar` can be a submodule.
                    // `import foo.bar` just exports the name foo.
                    if let DottedImportNameContent::DottedName(super_, _) = dotted.unpack() {
                        submodule_reexport(self.cache_import_dotted_name(i_s.db, super_, None))
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

fn cache_import_results(node_ref: NodeRef, result: &Option<ImportResult>) {
    match result {
        Some(ImportResult::File(f)) => {
            node_ref.set_point(Point::new_file_reference(*f, Locality::Complex))
        }
        Some(ImportResult::Namespace(n)) => node_ref.insert_type(Type::Namespace(n.clone())),
        Some(ImportResult::PyTypedMissing) => node_ref.set_point(Point::new_specific(
            Specific::AnyDueToError,
            Locality::Complex,
        )),
        None => node_ref.set_point(Point::new_specific(
            Specific::ModuleNotFound,
            Locality::Complex,
        )),
    }
}

fn load_saved_results(node_ref: NodeRef, p: Point) -> Option<ImportResult> {
    match p.kind() {
        PointKind::FileReference => Some(ImportResult::File(p.file_index())),
        PointKind::Specific => {
            debug_assert!(matches!(
                p.specific(),
                Specific::AnyDueToError | Specific::ModuleNotFound
            ));
            None
        }
        PointKind::Complex => match node_ref.maybe_type().unwrap() {
            Type::Namespace(ns) => Some(ImportResult::Namespace(ns.clone())),
            _ => unreachable!(),
        },
        _ => unreachable!(),
    }
}
