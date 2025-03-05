use config::TypeCheckerFlags;
use parsa_python_cst::{
    DottedAsNameContent, DottedName, DottedNameContent, ImportFrom, ImportFromAsName,
    ImportFromTargets, ImportName, Name, NameDef, NodeIndex,
};

use crate::{
    database::{ComplexPoint, Locality, Point, PointKind, PointLink, Specific},
    debug,
    diagnostics::IssueKind,
    imports::{find_ancestor, global_import, namespace_import, ImportResult},
    inference_state::InferenceState,
    inferred::Inferred,
    node_ref::NodeRef,
    type_::{AnyCause, LookupResult, Type},
    type_helpers::{is_reexport_issue, lookup_in_namespace, Module},
    utils::AlreadySeen,
};

use super::{
    inference::{AssignKind, StarImportResult},
    python_file::StarImport,
    File as _, PythonFile,
};

pub struct NameResolution<'db: 'file, 'file, 'i_s> {
    pub(super) file: &'file PythonFile,
    pub(super) i_s: &'i_s InferenceState<'db, 'i_s>,
}

impl<'db, 'file> NameResolution<'db, 'file, '_> {
    pub(super) fn cache_import_name(&self, imp: ImportName) {
        if self.file.points.get(imp.index()).calculated() {
            return;
        }

        for dotted_as_name in imp.iter_dotted_as_names() {
            match dotted_as_name.unpack() {
                DottedAsNameContent::Simple(name_def, rest) => {
                    let result = self.global_import(name_def.name(), Some(name_def));
                    if let Some(rest) = rest {
                        if result.is_some() {
                            self.infer_import_dotted_name(rest, result);
                        }
                    }
                }
                DottedAsNameContent::WithAs(dotted_name, as_name_def) => {
                    let result = self.infer_import_dotted_name(dotted_name, None);
                    debug_assert!(!self.file.points.get(as_name_def.index()).calculated());
                    let inf = match result {
                        Some(import_result) => import_result.as_inferred(),
                        None => Inferred::new_module_not_found(),
                    };
                    self.assign_to_name_def_simple(
                        as_name_def,
                        NodeRef::new(self.file, as_name_def.index()),
                        &inf,
                        AssignKind::Import,
                    );
                }
            }
        }

        self.file.points.set(
            imp.index(),
            Point::new_specific(Specific::Analyzed, Locality::Todo),
        );
    }

    pub(super) fn cache_import_from(&self, imp: ImportFrom) {
        if self.file.points.get(imp.index()).calculated() {
            return;
        }

        let from_first_part = self.import_from_first_part(imp);

        match imp.unpack_targets() {
            ImportFromTargets::Star(keyword) => {
                // Nothing to do here, was calculated earlier
                let point = match from_first_part {
                    Some(ImportResult::File(file_index)) => {
                        Point::new_file_reference(file_index, Locality::Todo)
                    }
                    // Currently we don't support namespace star imports
                    Some(ImportResult::Namespace { .. }) => {
                        Point::new_specific(Specific::ModuleNotFound, Locality::Todo)
                    }
                    Some(ImportResult::PyTypedMissing) => {
                        Point::new_specific(Specific::ModuleNotFound, Locality::Todo)
                    }
                    None => Point::new_specific(Specific::ModuleNotFound, Locality::Todo),
                };
                self.file.points.set(keyword.index(), point);
            }
            ImportFromTargets::Iterator(as_names) => {
                for as_name in as_names {
                    self.cache_import_from_part(&from_first_part, as_name)
                }
            }
        }
        self.file.points.set(
            imp.index(),
            Point::new_specific(Specific::Analyzed, Locality::Todo),
        );
    }

    pub fn import_from_first_part(&self, import_from: ImportFrom) -> Option<ImportResult> {
        let (level, dotted_name) = import_from.level_with_dotted_name();
        let maybe_level_file = (level > 0)
            .then(|| {
                find_ancestor(self.i_s.db, self.file, level).or_else(|| {
                    self.add_issue(import_from.index(), IssueKind::NoParentModule);
                    None
                })
            })
            .flatten();
        match dotted_name {
            Some(dotted_name) => self.infer_import_dotted_name(dotted_name, maybe_level_file),
            None => maybe_level_file,
        }
    }

    pub(super) fn cache_import_from_only_particular_name_def(&self, as_name: ImportFromAsName) {
        let import_from = as_name.import_from();
        let from_first_part = self.import_from_first_part(import_from);
        self.cache_import_from_part(&from_first_part, as_name)
    }

    pub fn infer_import_dotted_name(
        &self,
        dotted: DottedName,
        base: Option<ImportResult>,
    ) -> Option<ImportResult> {
        let node_ref = NodeRef::new(self.file, dotted.index());
        let p = node_ref.point();
        if p.calculated() {
            return match p.kind() {
                PointKind::FileReference => Some(ImportResult::File(p.file_index())),
                PointKind::Specific => None,
                PointKind::Complex => match node_ref.complex().unwrap() {
                    ComplexPoint::TypeInstance(Type::Namespace(ns)) => {
                        Some(ImportResult::Namespace(ns.clone()))
                    }
                    _ => unreachable!(),
                },
                _ => unreachable!(),
            };
        }
        let infer_name = |self_: &Self, import_result, name: Name| {
            let i_s = self_.i_s;
            let mut in_stub_and_has_getattr = false;
            let result = match &import_result {
                ImportResult::File(file_index) => {
                    let module = Module::from_file_index(i_s.db, *file_index);
                    let r = module.sub_module(i_s.db, name.as_str());

                    // This is such weird logic. I don't understand at all why Mypy is doing this.
                    // It seems to come from here:
                    // https://github.com/python/mypy/blob/bc591c756a453bb6a78a31e734b1f0aa475e90e0/mypy/semanal_pass1.py#L87-L96
                    if r.is_none()
                        && module.file.is_stub()
                        && module
                            .lookup(
                                i_s.db,
                                |issue| self.add_issue(name.index(), issue),
                                "__getattr__",
                            )
                            .is_some()
                    {
                        in_stub_and_has_getattr = true
                    }
                    r
                }
                ImportResult::Namespace(namespace) => {
                    namespace_import(i_s.db, self.file, namespace, name.as_str())
                }
                ImportResult::PyTypedMissing => Some(ImportResult::PyTypedMissing),
            };
            if let Some(imported) = &result {
                debug!(
                    "Imported {:?} for {:?}",
                    imported.debug_info(i_s.db),
                    dotted.as_code(),
                );
            } else if in_stub_and_has_getattr {
                debug!(
                    "Ignored import of {}, because of a __getattr__ in a stub file",
                    name.as_str()
                );
            } else {
                let module_name =
                    format!("{}.{}", import_result.qualified_name(i_s.db), name.as_str()).into();
                if !self.flags().ignore_missing_imports {
                    self_.add_issue(name.index(), IssueKind::ModuleNotFound { module_name });
                }
            }
            result
        };
        let result = match dotted.unpack() {
            DottedNameContent::Name(name) => {
                if let Some(base) = base {
                    infer_name(self, base, name)
                } else {
                    self.global_import(name, None)
                }
            }
            DottedNameContent::DottedName(dotted_name, name) => {
                let result = self.infer_import_dotted_name(dotted_name, base)?;
                infer_name(self, result, name)
            }
        };
        // Cache
        match &result {
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
        result
    }

    pub(super) fn cache_import_from_part(
        &self,
        from_first_part: &Option<ImportResult>,
        as_name: ImportFromAsName,
    ) {
        let (import_name, name_def) = as_name.unpack();

        let n_index = name_def.index();
        if self.file.points.get(n_index).calculated() {
            return;
        }
        // Set calculating here, so that the logic that follows the names can set a
        // cycle if it needs to.
        self.file.points.set(n_index, Point::new_calculating());
        let mut redirect_to_link = None;
        let inf = match from_first_part {
            Some(imp) => {
                let maybe_add_issue = || {
                    if !self.flags().ignore_missing_imports {
                        self.add_issue(
                            import_name.index(),
                            IssueKind::ImportAttributeError {
                                module_name: Box::from(imp.qualified_name(self.i_s.db)),
                                name: Box::from(import_name.as_str()),
                            },
                        );
                    }
                };
                match self.lookup_import_from_target(imp, import_name) {
                    LookupResult::GotoName { name: link, inf } => {
                        if self
                            .file
                            .points
                            .get(n_index)
                            .maybe_calculated_and_specific()
                            == Some(Specific::Cycle)
                        {
                            maybe_add_issue();
                            return;
                        }
                        redirect_to_link = Some(link);
                        inf
                    }
                    LookupResult::FileReference(file_index) => {
                        Inferred::new_file_reference(file_index)
                    }
                    LookupResult::UnknownName(inf) => inf,
                    LookupResult::None => {
                        maybe_add_issue();
                        Inferred::new_module_not_found()
                    }
                }
            }
            // Means one of the imports before failed.
            None => Inferred::new_module_not_found(),
        };

        self.assign_to_name_def(
            name_def,
            NodeRef::new(self.file, name_def.index()),
            &inf,
            AssignKind::Import,
            |_, inf| match redirect_to_link {
                Some(link) => {
                    self.file
                        .points
                        .set(n_index, link.into_redirect_point(Locality::Todo));
                }
                None => {
                    inf.clone().save_redirect(self.i_s, self.file, n_index);
                }
            },
        );
    }

    fn lookup_import_from_target(
        &self,
        from_first_part: &ImportResult,
        import_name: Name,
    ) -> LookupResult {
        let name = import_name.as_str();
        match from_first_part {
            ImportResult::File(file_index) => {
                let import_file = self.i_s.db.loaded_python_file(*file_index);
                Module::new(import_file).lookup_with_is_import(
                    self.i_s.db,
                    |issue| self.add_issue(import_name.index(), issue),
                    import_name.as_str(),
                    Some(self.file.file_index),
                )
            }
            ImportResult::Namespace(namespace) => {
                lookup_in_namespace(self.i_s.db, self.file, namespace, name)
            }
            ImportResult::PyTypedMissing => LookupResult::any(AnyCause::FromError),
        }
    }

    fn global_import(&self, name: Name, name_def: Option<NameDef>) -> Option<ImportResult> {
        let result = global_import(self.i_s.db, self.file, name.as_str());
        if let Some(result) = &result {
            debug!(
                "Global import '{}': {:?}",
                name.as_code(),
                result.debug_info(self.i_s.db),
            );
        }
        let inf = match &result {
            Some(import_result) => import_result.as_inferred(),
            None => {
                if !self.flags().ignore_missing_imports {
                    self.add_issue(
                        name.index(),
                        IssueKind::ModuleNotFound {
                            module_name: Box::from(name.as_str()),
                        },
                    );
                }
                Inferred::new_module_not_found()
            }
        };
        if let Some(name_def) = name_def {
            self.assign_to_name_def_simple(
                name_def,
                NodeRef::new(self.file, name_def.index()),
                &inf,
                AssignKind::Import,
            );
        }
        result
    }

    pub fn lookup_from_star_import(
        &self,
        name: &str,
        check_local: bool,
    ) -> Option<StarImportResult> {
        self.lookup_from_star_import_with_node_index(name, check_local, None, None)
    }

    pub fn lookup_from_star_import_with_node_index(
        &self,
        name: &str,
        check_local: bool,
        node_index: Option<NodeIndex>,
        star_imports_seen: Option<AlreadySeen<PointLink>>,
    ) -> Option<StarImportResult> {
        for star_import in self.file.star_imports.iter() {
            // TODO these feel a bit weird and do not include parent functions (when in a
            // closure)
            let mut is_class_star_import = false;
            if !(star_import.scope == 0
                || check_local
                    && self
                        .i_s
                        .current_function()
                        .map(|f| f.node_ref.node_index == star_import.scope)
                        .unwrap_or_else(|| {
                            self.i_s.current_class().is_some_and(|c| {
                                is_class_star_import = true;
                                c.node_ref.node_index == star_import.scope
                            })
                        }))
            {
                continue;
            }
            let in_mod = self.i_s.in_module_context();
            let in_same_scope = star_import.scope == 0 && in_mod || !in_mod;
            if in_same_scope && node_index.is_some_and(|n| n < star_import.star_node) {
                continue;
            }
            if let Some(result) = self.lookup_name_in_star_import(
                star_import,
                name,
                is_class_star_import,
                star_imports_seen,
            ) {
                return Some(result);
            }
        }
        if let Some(super_file) = &self.file.super_file {
            // This sub file currently means we're in a type definition.
            if let Some(_func) = self.i_s.current_function() {
                debug!("TODO lookup in func of sub file")
            } else if let Some(class) = self.i_s.current_class() {
                if let Some(index) = class.class_storage.class_symbol_table.lookup_symbol(name) {
                    return Some(StarImportResult::Link(PointLink::new(
                        class.node_ref.file_index(),
                        index,
                    )));
                }
            }

            let super_file = self.i_s.db.loaded_python_file(*super_file);
            if let Some(link) = super_file.lookup_global(name) {
                return Some(StarImportResult::Link(link.into()));
            }
            super_file
                .name_resolution(self.i_s)
                .lookup_from_star_import_with_node_index(name, false, None, star_imports_seen)
        } else {
            None
        }
    }

    pub fn lookup_name_in_star_import(
        &self,
        star_import: &StarImport,
        name: &str,
        is_class_star_import: bool,
        star_imports_seen: Option<AlreadySeen<PointLink>>,
    ) -> Option<StarImportResult> {
        let link = PointLink::new(self.file.file_index, star_import.star_node);
        let new_seen = if let Some(seen) = star_imports_seen.as_ref() {
            seen.append(link)
        } else {
            AlreadySeen::new(link)
        };
        if new_seen.is_cycle() {
            // TODO we might want to add an issue in the future (not high-prio however)
            return None;
        }
        let other_file = star_import.to_file(self)?;
        if let Some(dunder) = other_file.maybe_dunder_all(self.i_s.db) {
            // Name not in __all__
            if !dunder.iter().any(|x| x.as_str(self.i_s.db) == name) {
                return None;
            }
        } else if name.starts_with('_') {
            return None;
        }

        if let Some(link) = other_file.lookup_global(name) {
            if !is_reexport_issue(self.i_s.db, other_file, link.into()) {
                let mut result = StarImportResult::Link(link.into());
                if is_class_star_import
                    && result
                        .as_inferred(self.i_s)
                        .as_cow_type(self.i_s)
                        .is_func_or_overload()
                {
                    result = StarImportResult::AnyDueToError;
                }
                return Some(result);
            }
        }
        if let Some(l) = other_file
            .name_resolution(self.i_s)
            .lookup_from_star_import_with_node_index(name, false, None, Some(new_seen))
        {
            Some(l)
        } else {
            debug!(
                "Name {name} not found in star import {}",
                other_file.qualified_name(self.i_s.db)
            );
            None
        }
    }

    pub(crate) fn add_issue(&self, node_index: NodeIndex, issue: IssueKind) {
        let from = NodeRef::new(self.file, node_index);
        from.add_issue(self.i_s, issue);
    }

    pub fn flags(&self) -> &TypeCheckerFlags {
        self.file.flags(self.i_s.db)
    }

    pub fn file_path(&self) -> &str {
        self.file.file_path(self.i_s.db)
    }
}
