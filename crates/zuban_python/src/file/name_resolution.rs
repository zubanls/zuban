use config::TypeCheckerFlags;
use parsa_python_cst::{
    DefiningStmt, DottedAsName, DottedAsNameContent, DottedName, DottedNameContent, ImportFrom,
    ImportFromAsName, ImportFromTargets, Name, NameDef, NodeIndex, NAME_DEF_TO_NAME_DIFFERENCE,
};

use crate::{
    database::{ComplexPoint, Locality, Point, PointKind, PointLink, Specific},
    debug,
    diagnostics::IssueKind,
    file::File,
    imports::{find_ancestor, global_import, namespace_import, ImportResult},
    inference_state::InferenceState,
    inferred::Inferred,
    node_ref::NodeRef,
    type_::{LookupResult, Type},
    type_helpers::{is_private_import, is_reexport_issue, Module},
    utils::AlreadySeen,
};

use super::{inference::StarImportResult, python_file::StarImport, PythonFile};

pub struct NameResolution<'db: 'file, 'file, 'i_s> {
    pub(super) file: &'file PythonFile,
    pub(super) i_s: &'i_s InferenceState<'db, 'i_s>,
    // Type computation uses alias calculation, which works in a different way than normal
    // inference. Therefore we want to stop and return the assignment.
    pub(super) stop_on_assignments: bool,
}

#[derive(Debug)]
pub enum PointResolution<'file> {
    NameDef {
        node_ref: NodeRef<'file>,
        global_redirect: bool,
    },
    Inferred(Inferred),
    Param(NodeRef<'file>),
    GlobalOrNonlocalName(NodeRef<'file>),
}

impl<'db, 'file, 'i_s> NameResolution<'db, 'file, 'i_s> {
    pub(super) fn with_new_file<'new_file>(
        &self,
        file: &'new_file PythonFile,
    ) -> NameResolution<'db, 'new_file, 'i_s> {
        NameResolution {
            file,
            i_s: self.i_s,
            stop_on_assignments: self.stop_on_assignments,
        }
    }

    pub(super) fn assign_dotted_as_name(
        &self,
        dotted_as_name: DottedAsName,
        assign_to_name_def: impl FnOnce(NameDef, Inferred),
    ) {
        match dotted_as_name.unpack() {
            DottedAsNameContent::Simple(name_def, rest) => {
                let result = self.global_import(name_def.name());
                let inf = match &result {
                    Some(import_result) => import_result.as_inferred(),
                    None => Inferred::new_module_not_found(),
                };
                assign_to_name_def(name_def, inf);
                if let Some(rest) = rest {
                    if result.is_some() {
                        self.cache_import_dotted_name(rest, result);
                    }
                }
            }
            DottedAsNameContent::WithAs(dotted_name, as_name_def) => {
                let result = self.cache_import_dotted_name(dotted_name, None);
                debug_assert!(!self.file.points.get(as_name_def.index()).calculated());
                let inf = match result {
                    Some(import_result) => import_result.as_inferred(),
                    None => Inferred::new_module_not_found(),
                };
                assign_to_name_def(as_name_def, inf);
            }
        }
    }

    pub(super) fn assign_import_from_names(
        &self,
        imp: ImportFrom,
        assign_to_name_def: impl Fn(NameDef, PointResolution<'file>, Option<PointLink>),
    ) {
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
                    self.cache_import_from_part(&from_first_part, as_name, &assign_to_name_def)
                }
            }
        }
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
            Some(dotted_name) => self.cache_import_dotted_name(dotted_name, maybe_level_file),
            None => maybe_level_file,
        }
    }

    pub(super) fn assign_import_from_only_particular_name_def(
        &self,
        as_name: ImportFromAsName,
        assign_to_name_def: impl FnOnce(NameDef, PointResolution<'file>, Option<PointLink>),
    ) {
        let import_from = as_name.import_from();
        let from_first_part = self.import_from_first_part(import_from);
        self.cache_import_from_part(&from_first_part, as_name, assign_to_name_def)
    }

    pub(super) fn resolve_import_from_name_def_without_narrowing(
        &self,
        as_name: ImportFromAsName,
    ) -> PointResolution<'file> {
        // For type resolution, we don't want to infer names in the normal way, because it leads to
        // weird narrowing recursions. We have to make sure we do not assign the names, because
        // they might be different later.
        let mut found_inf = None;
        self.assign_import_from_only_particular_name_def(as_name, |name_def, inf, _| {
            debug_assert!(self.file.points.get(name_def.index()).calculating());
            self.file
                .points
                .set(name_def.index(), Point::new_uncalculated());
            found_inf = Some(inf);
        });
        match found_inf {
            Some(pr) => pr,
            None => self
                .resolve_point_without_narrowing(as_name.name_def().index())
                .expect("Resolving import"),
        }
    }

    pub(super) fn resolve_import_name_name_def_without_narrowing(
        &self,
        dotted_as_name: DottedAsName,
    ) -> PointResolution<'file> {
        // See comment in resolve_import_from_name_def_without_narrowing
        let mut found_inf = None;
        self.assign_dotted_as_name(dotted_as_name, |name_def, inf| {
            if cfg!(debug_assertions) {
                let p = self.file.points.get(name_def.index());
                debug_assert!(!p.calculated(), "{p:?}");
                debug_assert!(!p.calculating(), "{p:?}");
            }
            self.file
                .points
                .set(name_def.index(), Point::new_uncalculated());
            found_inf = Some(inf);
        });
        match found_inf {
            Some(inf) => PointResolution::Inferred(inf),
            None => self
                .resolve_point_without_narrowing(dotted_as_name.name_def().index())
                .expect("Resolving import"),
        }
    }

    pub fn cache_import_dotted_name(
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
                    self.global_import(name)
                }
            }
            DottedNameContent::DottedName(dotted_name, name) => {
                let result = self.cache_import_dotted_name(dotted_name, base)?;
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

    fn cache_import_from_part(
        &self,
        from_first_part: &Option<ImportResult>,
        as_name: ImportFromAsName,
        assign_to_name_def: impl FnOnce(NameDef, PointResolution<'file>, Option<PointLink>),
    ) {
        let (import_name, name_def) = as_name.unpack();

        let n_index = name_def.index();
        if self.file.points.get(n_index).calculated() {
            return;
        }
        // Set calculating here, so that the logic that follows the names can set a
        // cycle if it needs to.
        self.file.points.set(n_index, Point::new_calculating());
        let inf = match from_first_part {
            Some(imp) => {
                let add_issue_if_not_ignored = || {
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
                    Some((pr, redirect_to)) => {
                        if self
                            .file
                            .points
                            .get(n_index)
                            .maybe_calculated_and_specific()
                            == Some(Specific::Cycle)
                        {
                            add_issue_if_not_ignored();
                            return;
                        }
                        assign_to_name_def(name_def, pr, redirect_to);
                        return;
                    }
                    None => {
                        add_issue_if_not_ignored();
                        Inferred::new_module_not_found()
                    }
                }
            }
            // Means one of the imports before failed.
            None => Inferred::new_module_not_found(),
        };
        assign_to_name_def(name_def, PointResolution::Inferred(inf), None)
    }

    fn lookup_import_from_target(
        &self,
        from_first_part: &ImportResult,
        import_name: Name,
    ) -> Option<(PointResolution<'file>, Option<PointLink>)> {
        let name = import_name.as_str();
        let convert_imp_result = |imp_result| match imp_result {
            ImportResult::File(file_index) => Inferred::new_file_reference(file_index),
            ImportResult::Namespace(ns) => Inferred::from_type(Type::Namespace(ns)),
            ImportResult::PyTypedMissing => Inferred::new_any_from_error(),
        };
        Some(match from_first_part {
            ImportResult::File(file_index) => {
                let import_file = self.i_s.db.loaded_python_file(*file_index);
                // Coming from an import we need to make sure that we do not create loops for imports
                if self.file.file_index == import_file.file_index {
                    let module = Module::new(import_file);
                    let inf = convert_imp_result(module.sub_module(self.i_s.db, name)?);
                    (PointResolution::Inferred(inf), None)
                } else {
                    if self.stop_on_assignments {
                        return self
                            .with_new_file(import_file)
                            .resolve_module_access(name, |kind| {
                                self.add_issue(import_name.index(), kind)
                            });
                    } else {
                        // TODO Shouldn't we use the normal resolving?
                        let module = Module::new(import_file);
                        let mut redirect_to_link = None;
                        let inf = match module.lookup(
                            self.i_s.db,
                            |issue| self.add_issue(import_name.index(), issue),
                            import_name.as_str(),
                        ) {
                            LookupResult::GotoName { name: link, inf } => {
                                redirect_to_link = Some(link);
                                inf
                            }
                            LookupResult::FileReference(file_index) => {
                                Inferred::new_file_reference(file_index)
                            }
                            LookupResult::UnknownName(inf) => inf,
                            LookupResult::None => {
                                return None;
                            }
                        };
                        return Some((PointResolution::Inferred(inf), redirect_to_link));
                    }
                }
            }
            ImportResult::Namespace(namespace) => (
                PointResolution::Inferred(convert_imp_result(namespace_import(
                    self.i_s.db,
                    self.file,
                    namespace,
                    name,
                )?)),
                None,
            ),
            ImportResult::PyTypedMissing => (
                PointResolution::Inferred(Inferred::new_any_from_error()),
                None,
            ),
        })
    }

    fn global_import(&self, name: Name) -> Option<ImportResult> {
        let result = global_import(self.i_s.db, self.file, name.as_str());
        if let Some(result) = &result {
            debug!(
                "Global import '{}': {:?}",
                name.as_code(),
                result.debug_info(self.i_s.db),
            );
        }
        if result.is_none() && !self.flags().ignore_missing_imports {
            self.add_issue(
                name.index(),
                IssueKind::ModuleNotFound {
                    module_name: Box::from(name.as_str()),
                },
            );
        }
        result
    }

    pub(super) fn resolve_name_without_narrowing(&self, name: Name) -> PointResolution<'file> {
        self.resolve_name(name, |_, _, _| None)
    }

    pub(super) fn resolve_name(
        &self,
        name: Name,
        narrow_name: impl Fn(&InferenceState, NodeRef, PointLink) -> Option<Inferred>,
    ) -> PointResolution<'file> {
        self.resolve_point(name.index(), &narrow_name)
            .unwrap_or_else(|| self.resolve_name_by_str(name.as_code(), name.index(), narrow_name))
    }

    pub(super) fn resolve_name_by_str(
        &self,
        name_str: &str,
        save_to_index: NodeIndex,
        narrow_name: impl Fn(&InferenceState, NodeRef, PointLink) -> Option<Inferred>,
    ) -> PointResolution<'file> {
        // If it's not inferred already through the name binder, it's either a star import, a
        // builtin or really missing.
        let i_s = self.i_s;
        if let Some(r) = self.resolve_star_import_name(name_str, Some(save_to_index), &narrow_name)
        {
            return r;
        }
        let builtins = i_s.db.python_state.builtins();
        let point = match name_str {
            "reveal_type" => {
                if self
                    .flags()
                    .enabled_error_codes
                    .iter()
                    .any(|code| code == "unimported-reveal")
                {
                    self.add_issue(save_to_index, IssueKind::UnimportedRevealType);
                }
                Point::new_specific(Specific::RevealTypeFunction, Locality::Todo)
            }
            "__builtins__" => Point::new_file_reference(builtins.file_index, Locality::Todo),
            "__debug__" => {
                return PointResolution::Inferred(
                    Inferred::from_type(i_s.db.python_state.bool_type()).save_redirect(
                        i_s,
                        self.file,
                        save_to_index,
                    ),
                )
            }
            _ => {
                if let Some(name_ref) = builtins.lookup_global(name_str).filter(|name_ref| {
                    (is_valid_builtins_export(name_str)) && !is_private_import(*name_ref)
                }) {
                    debug_assert!(
                        name_ref.file_index() != self.file.file_index
                            || name_ref.node_index != save_to_index
                    );
                    Point::new_redirect(name_ref.file_index(), name_ref.node_index, Locality::Todo)
                } else {
                    // The builtin module should really not have any issues.
                    debug_assert!(
                        self.file.file_index != builtins.file_index,
                        "{name_str}; {save_to_index}"
                    );
                    if i_s.in_class_scope().is_some()
                        && matches!(name_str, "__name__" | "__module__" | "__qualname__")
                    {
                        return PointResolution::Inferred(
                            Inferred::from_type(i_s.db.python_state.str_type()).save_redirect(
                                i_s,
                                self.file,
                                save_to_index,
                            ),
                        );
                    }
                    // It feels somewhat arbitrary what is exposed from the ModuleType and what's
                    // not, so just filter here.
                    if matches!(
                        name_str,
                        "__name__"
                            | "__file__"
                            | "__package__"
                            | "__spec__"
                            | "__doc__"
                            | "__annotations__"
                    ) {
                        if let Some(mut inf) = i_s
                            .db
                            .python_state
                            .module_instance()
                            .type_lookup(
                                i_s,
                                |issue| self.add_issue(save_to_index, issue),
                                name_str,
                            )
                            .into_maybe_inferred()
                        {
                            if matches!(name_str, "__package__" | "__file__") {
                                inf = inf.remove_none(i_s);
                            }
                            return PointResolution::Inferred(inf.save_redirect(
                                i_s,
                                self.file,
                                save_to_index,
                            ));
                        }
                    }
                    self.add_issue(
                        save_to_index,
                        IssueKind::NameError {
                            name: Box::from(name_str),
                        },
                    );
                    if !name_str.starts_with('_')
                        && i_s
                            .db
                            .python_state
                            .typing()
                            .lookup_global(name_str)
                            .is_some()
                    {
                        // TODO what about underscore or other vars?
                        self.add_issue(
                            save_to_index,
                            IssueKind::Note(
                                format!(
                                    "Did you forget to import it from \"typing\"? \
                             (Suggestion: \"from typing import {name_str}\")",
                                )
                                .into(),
                            ),
                        );
                    }
                    Point::new_specific(Specific::AnyDueToError, Locality::Todo)
                }
            }
        };
        self.file.points.set(save_to_index, point);
        debug_assert!(self.file.points.get(save_to_index).calculated());
        self.resolve_point(save_to_index, narrow_name).unwrap()
    }

    pub fn resolve_point_without_narrowing(
        &self,
        node_index: NodeIndex,
    ) -> Option<PointResolution<'file>> {
        self.resolve_point(node_index, |_, _, _| None)
    }

    pub fn resolve_point(
        &self,
        node_index: NodeIndex,
        narrow_name: impl Fn(&InferenceState, NodeRef, PointLink) -> Option<Inferred>,
    ) -> Option<PointResolution<'file>> {
        let point = self.file.points.get(node_index);
        self.resolve_point_internal(node_index, point, false, narrow_name)
    }

    fn resolve_point_internal(
        &self,
        node_index: NodeIndex,
        point: Point,
        global_redirect: bool,
        narrow_name: impl Fn(&InferenceState, NodeRef, PointLink) -> Option<Inferred>,
    ) -> Option<PointResolution<'file>> {
        point
            .calculated()
            .then(|| self.find_point_resolution(node_index, point, global_redirect, narrow_name))
            .or_else(|| {
                if point.calculating() {
                    let node_ref = NodeRef::new(self.file, node_index);
                    debug!(
                        "Found a cycle at #{}, {}:{node_index}: {:?}",
                        node_ref.line(),
                        self.file.file_index,
                        node_ref.as_code()
                    );
                    node_ref.set_point(Point::new_specific(Specific::Cycle, Locality::Todo));
                    Some(PointResolution::Inferred(Inferred::new_cycle()))
                } else {
                    None
                }
            })
    }

    #[inline]
    fn find_point_resolution(
        &self,
        node_index: NodeIndex,
        point: Point,
        global_redirect: bool,
        narrow_name: impl Fn(&InferenceState, NodeRef, PointLink) -> Option<Inferred>,
    ) -> PointResolution<'file> {
        match point.kind() {
            PointKind::Redirect => {
                let file_index = point.file_index();
                let next_node_index = point.node_index();
                if point.needs_flow_analysis() {
                    debug_assert!(Name::maybe_by_index(&self.file.tree, node_index).is_some());
                    if let Some(inf) = narrow_name(
                        self.i_s,
                        NodeRef::new(self.file, node_index),
                        PointLink::new(file_index, next_node_index),
                    ) {
                        return PointResolution::Inferred(inf);
                    }
                }
                debug_assert!(
                    file_index != self.file.file_index || next_node_index != node_index,
                    "{file_index}:{node_index}"
                );
                let resolve = |r: &NameResolution<'db, 'file, '_>| {
                    let new_p = r.file.points.get(next_node_index);
                    r.resolve_point_internal(
                        next_node_index,
                        new_p,
                        global_redirect || !point.in_global_scope() && new_p.in_global_scope(),
                        narrow_name,
                    )
                    .unwrap_or_else(|| {
                        unreachable!(
                            "This should never happen {}",
                            NodeRef::new(r.file, next_node_index).debug_info(self.i_s.db)
                        )
                    })
                };
                if file_index == self.file.file_index {
                    resolve(self)
                } else {
                    resolve(&mut self.with_new_file(self.i_s.db.loaded_python_file(file_index)))
                }
            }
            PointKind::Specific => match point.specific() {
                Specific::Param | Specific::MaybeSelfParam => {
                    PointResolution::Param(NodeRef::new(self.file, node_index))
                }
                Specific::GlobalVariable | Specific::NonlocalVariable => {
                    PointResolution::GlobalOrNonlocalName(NodeRef::new(self.file, node_index))
                }
                Specific::NameOfNameDef | Specific::FirstNameOfNameDef => {
                    // MultiDefinition means we are on a Name that has a NameDef as a
                    // parent.
                    let node_index = node_index - NAME_DEF_TO_NAME_DIFFERENCE;
                    let p = self.file.points.get(node_index);

                    let node_ref = NodeRef::new(self.file, node_index);
                    if self.stop_on_assignments {
                        let defining = node_ref.as_name_def().expect_defining_stmt();
                        if matches!(defining, DefiningStmt::Assignment(_)) {
                            return PointResolution::NameDef {
                                node_ref,
                                global_redirect,
                            };
                        }
                    }
                    self.resolve_point_internal(node_index, p, global_redirect, narrow_name)
                        .unwrap_or_else(|| PointResolution::NameDef {
                            node_ref,
                            global_redirect,
                        })
                }
                _ => PointResolution::Inferred(Inferred::new_saved(self.file, node_index)),
            },
            PointKind::Complex | PointKind::FileReference => {
                PointResolution::Inferred(Inferred::new_saved(self.file, node_index))
            }
        }
    }

    pub(super) fn resolve_module_access(
        &self,
        name: &str,
        add_issue: impl Fn(IssueKind),
    ) -> Option<(PointResolution<'file>, Option<PointLink>)> {
        let db = self.i_s.db;
        Some(if let Some(name_ref) = self.file.lookup_global(name) {
            if let Some(r) =
                Module::new(self.file).maybe_submodule_reexport(self.i_s, name_ref, name)
            {
                return Some((
                    PointResolution::Inferred(r.into_inferred()),
                    Some(name_ref.as_link()),
                ));
            }
            if is_reexport_issue(db, name_ref) {
                add_issue(IssueKind::ImportStubNoExplicitReexport {
                    module_name: self.file.qualified_name(db).into(),
                    attribute: name.into(),
                })
            }
            (
                self.resolve_name_without_narrowing(name_ref.as_name()),
                Some(name_ref.as_link()),
            )
        } else if let Some(r) = Module::new(self.file).sub_module_lookup(db, name) {
            (PointResolution::Inferred(r.into_inferred()), None)
        } else if let Some(r) = self.resolve_star_import_name(name, None, &|_, _, _| None) {
            (r, None)
        } else {
            return None;
        })
    }

    #[inline]
    fn resolve_star_import_name(
        &self,
        name: &str,
        save_to_index: Option<NodeIndex>,
        narrow_name: &dyn Fn(&InferenceState, NodeRef, PointLink) -> Option<Inferred>,
    ) -> Option<PointResolution<'file>> {
        let star_imp = self.lookup_from_star_import(name, true)?;
        Some(match star_imp {
            StarImportResult::Link(link) => match save_to_index {
                Some(save_to_index) => {
                    self.file.points.set(
                        save_to_index,
                        Point::new_redirect(link.file, link.node_index, Locality::Todo),
                    );
                    self.resolve_point(save_to_index, narrow_name).unwrap()
                }
                None => {
                    let node_ref = NodeRef::from_link(self.i_s.db, link);
                    self.with_new_file(node_ref.file)
                        .resolve_name(node_ref.as_name(), narrow_name)
                }
            },
            StarImportResult::AnyDueToError => PointResolution::Inferred(match save_to_index {
                Some(save_to_index) => {
                    star_imp
                        .as_inferred(self.i_s)
                        .save_redirect(self.i_s, self.file, save_to_index)
                }
                None => star_imp.as_inferred(self.i_s),
            }),
        })
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
            if let Some(name_ref) = super_file.lookup_global(name) {
                return Some(StarImportResult::Link(name_ref.as_link()));
            }
            self.with_new_file(super_file)
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

        if let Some(name_ref) = other_file.lookup_global(name) {
            if !is_reexport_issue(self.i_s.db, name_ref) {
                let mut result = StarImportResult::Link(name_ref.as_link());
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
        if let Some(l) = self
            .with_new_file(other_file)
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

fn is_valid_builtins_export(name: &str) -> bool {
    !name.starts_with('_') || name.starts_with("__") && name.ends_with("__")
}
