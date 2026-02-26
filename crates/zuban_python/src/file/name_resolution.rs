use config::FinalizedTypeCheckerFlags;
use parsa_python_cst::{
    DefiningStmt, DottedAsName, ImportFrom, ImportFromAsName, NAME_DEF_TO_NAME_DIFFERENCE, Name,
    NameDef, NameImportParent, NodeIndex,
};
use utils::AlreadySeen;
use vfs::FileIndex;

use crate::{
    database::{Database, Locality, Point, PointKind, PointLink, Specific},
    debug,
    diagnostics::IssueKind,
    file::File,
    imports::{ImportResult, LoadedImportResult, namespace_import},
    inference_state::InferenceState,
    inferred::Inferred,
    node_ref::NodeRef,
    recoverable_error,
    type_::{LookupResult, Type},
    utils::is_magic_method,
};

use super::{ClassInitializer, PythonFile, inference::StarImportResult, python_file::StarImport};

#[derive(Copy, Clone)]
pub(crate) struct NameResolution<'db: 'file, 'file, 'i_s> {
    pub(super) file: &'file PythonFile,
    pub(super) i_s: &'i_s InferenceState<'db, 'i_s>,
    // Type computation uses alias calculation, which works in a different way than normal
    // inference. Therefore we want to stop and return the assignment.
    pub(super) stop_on_assignments: bool,
}

#[derive(Debug)]
pub(crate) enum PointResolution<'file> {
    NameDef {
        node_ref: NodeRef<'file>,
        global_redirect: bool,
    },
    Inferred(Inferred),
    Param {
        node_ref: NodeRef<'file>,
        maybe_self: bool,
    },
    GlobalOrNonlocalName(NodeRef<'file>),
    ModuleGetattrName(NodeRef<'file>),
}

impl PointResolution<'_> {
    pub(super) fn debug_info(&self, db: &Database) -> String {
        match self {
            Self::NameDef {
                node_ref,
                global_redirect,
            } => format!(
                "NameDef: {}, {}",
                node_ref.debug_info(db),
                match global_redirect {
                    true => "global-redirect",
                    false => "no-global-redirect",
                }
            ),
            Self::Inferred(inferred) => format!("Inferred: {}", inferred.debug_info(db)),
            Self::Param { node_ref, .. } => format!("Param: {}", node_ref.debug_info(db)),
            Self::GlobalOrNonlocalName(node_ref) => {
                format!("GlobalOrNonlocal: {}", node_ref.debug_info(db))
            }
            Self::ModuleGetattrName(node_ref) => {
                format!("ModuleGetattrName: {}", node_ref.debug_info(db))
            }
        }
    }
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

    pub(super) fn assign_import_from_only_particular_name_def(
        &self,
        as_name: ImportFromAsName,
        assign_to_name_def: impl FnOnce(NameDef, PointResolution<'file>, Option<ModuleAccessDetail>),
    ) {
        if let Some(import_from) = as_name.import_from() {
            let from_first_part = self.file.import_from_first_part(self.i_s.db, import_from);
            self.cache_import_from_part(import_from, &from_first_part, as_name, assign_to_name_def)
        } else {
            assign_to_name_def(
                as_name.name_def(),
                PointResolution::Inferred(Inferred::new_any_from_error()),
                None,
            )
        }
    }

    pub(super) fn resolve_import_from_name_def_without_narrowing(
        &self,
        as_name: ImportFromAsName,
    ) -> PointResolution<'file> {
        // For type resolution, we don't want to infer names in the normal way, because it leads to
        // weird narrowing recursions. We have to make sure we do not assign the names, because
        // they might be different later.
        let mut found_pr = None;
        self.assign_import_from_only_particular_name_def(
            as_name,
            |name_def, pr, redirect_to_link| {
                if cfg!(debug_assertions) {
                    let p = self.point(name_def.index());
                    assert!(p.calculating() || !p.calculated(), "{p:?}",);
                }
                if self.is_allowed_to_assign_on_import_without_narrowing(name_def) {
                    match redirect_to_link {
                        Some(link) => {
                            self.set_point(name_def.index(), link.into_point(Locality::Todo));
                        }
                        None => {
                            // We can not assign in all cases here, for example in the presence of
                            // a module __getattr__, we don't know the assignment type, yet.
                            if let PointResolution::Inferred(inf) = pr {
                                found_pr = Some(PointResolution::Inferred(inf.save_redirect(
                                    self.i_s,
                                    self.file,
                                    name_def.index(),
                                )));
                                return;
                            }
                            self.set_point(name_def.index(), Point::new_uncalculated());
                        }
                    }
                } else {
                    // Since the point was calculating, we have to reset it here.
                    // See also comments in cache_import_from_part
                    self.set_point(name_def.index(), Point::new_uncalculated());
                }
                found_pr = Some(pr);
            },
        );
        match found_pr {
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
        PointResolution::Inferred(
            self.file
                .infer_dotted_as_name_import(self.i_s.db, dotted_as_name),
        )
    }

    #[inline]
    fn is_allowed_to_assign_on_import_without_narrowing(&self, name_def: NameDef) -> bool {
        !self.point(name_def.name_index()).can_be_redefined()
    }

    pub(super) fn cache_import_from_part(
        &self,
        import_from: ImportFrom,
        from_first_part: &Option<LoadedImportResult>,
        as_name: ImportFromAsName,
        assign_to_name_def: impl FnOnce(NameDef, PointResolution<'file>, Option<ModuleAccessDetail>),
    ) {
        let (import_name, name_def) = as_name.unpack();

        let n_index = name_def.index();
        if self.point(n_index).calculated() {
            return;
        }
        // Set calculating here, so that the logic that follows the names can set a cycle if it
        // needs to.  The point has to be set or unset again in assign_to_name_def (e.g. in type
        // computation when the type can still be wrong because of star imports).
        self.set_point(n_index, Point::new_calculating());
        let inf = match from_first_part {
            Some(imp) => {
                let add_issue_if_not_ignored = || {
                    if !self.flags().ignore_missing_imports {
                        // If we don't assign we don't have to add an error
                        if !self.stop_on_assignments
                            || self.is_allowed_to_assign_on_import_without_narrowing(name_def)
                        {
                            let index = if self.i_s.db.mypy_compatible() {
                                import_from.index()
                            } else {
                                import_name.index()
                            };
                            self.add_issue(
                                index,
                                IssueKind::ImportAttributeError {
                                    module_name: Box::from(imp.qualified_name(self.i_s.db)),
                                    name: Box::from(import_name.as_str()),
                                },
                            );
                        }
                    }
                };

                match self.lookup_import_from_target(imp, import_name) {
                    Some((pr, redirect_to)) => {
                        if self.point(n_index).maybe_calculated_and_specific()
                            == Some(Specific::Cycle)
                        {
                            add_issue_if_not_ignored();
                            return;
                        }
                        /*
                        if let Some(redirect_to) = &redirect_to {
                            self.set_point(as_name.index(), redirect_to.into_point(Locality::Todo));
                        }
                        */
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
    ) -> Option<(PointResolution<'file>, Option<ModuleAccessDetail>)> {
        let name = import_name.as_str();
        let convert_imp_result =
            |imp_result: LoadedImportResult| match imp_result.into_import_result() {
                ImportResult::File(file_index) => Inferred::new_file_reference(file_index),
                ImportResult::Namespace(ns) => Inferred::from_type(Type::Namespace(ns)),
                ImportResult::PyTypedMissing => Inferred::new_any_from_error(),
            };
        Some(match from_first_part {
            ImportResult::File(file_index) => {
                // Coming from an import we need to make sure that we do not create loops for imports
                if self.file.file_index == *file_index {
                    let inf = convert_imp_result(self.file.sub_module(self.i_s.db, name)?);
                    (PointResolution::Inferred(inf), None)
                } else {
                    let import_file = self.i_s.db.loaded_python_file(*file_index);
                    return self
                        .with_new_file(import_file)
                        .resolve_module_access(name, |kind| {
                            self.add_issue(import_name.index(), kind)
                        });
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
        if let Some((r, _)) =
            self.resolve_star_import_name(name_str, Some(save_to_index), &narrow_name)
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
                );
            }
            _ => {
                if let Some(name_ref) = builtins.lookup_symbol(name_str).filter(|name_ref| {
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
                    ) && let Some(mut inf) = i_s
                        .db
                        .python_state
                        .module_instance()
                        .type_lookup(i_s, |issue| self.add_issue(save_to_index, issue), name_str)
                        .into_maybe_inferred()
                    {
                        if matches!(name_str, "__package__" | "__file__")
                            || name_str == "__doc__" && self.file.tree.root().docstring().is_some()
                        {
                            inf = inf.remove_none(i_s);
                        }
                        return PointResolution::Inferred(inf.save_redirect(
                            i_s,
                            self.file,
                            save_to_index,
                        ));
                    }
                    let mut note = None;
                    if !name_str.starts_with('_')
                        && i_s
                            .db
                            .python_state
                            .typing()
                            .lookup_symbol(name_str)
                            .is_some()
                    {
                        // TODO what about underscore or other vars?
                        note = Some(
                            format!(
                                "Did you forget to import it from \"typing\"? \
                             (Suggestion: \"from typing import {name_str}\")",
                            )
                            .into(),
                        );
                    }
                    self.add_issue(
                        save_to_index,
                        IssueKind::NameError {
                            name: Box::from(name_str),
                            note,
                        },
                    );
                    Point::new_specific(Specific::AnyDueToError, Locality::Todo)
                }
            }
        };
        self.set_point(save_to_index, point);
        debug_assert!(self.point(save_to_index).calculated());
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
        let point = self.point(node_index);
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
                        "Found a cycle at {}:#{} on name {:?}",
                        self.file.qualified_name(self.i_s.db),
                        node_ref.line_one_based(self.i_s.db),
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
                    "{:#?}",
                    NodeRef::new(self.file, node_index)
                );
                let resolve = |r: &NameResolution<'db, 'file, '_>| {
                    let new_p = r.point(next_node_index);
                    if new_p.calculating() {
                        // I'm not sure if this is the best return here, and if it should be
                        // handled here, but it seems to work.
                        return PointResolution::Inferred(Inferred::new_any_from_error());
                    }
                    r.resolve_point_internal(
                        next_node_index,
                        new_p,
                        global_redirect || !point.in_global_scope() && new_p.in_global_scope(),
                        narrow_name,
                    )
                    .unwrap_or_else(|| {
                        recoverable_error!(
                            "This should never happen {}",
                            NodeRef::new(r.file, next_node_index).debug_info(self.i_s.db)
                        );
                        PointResolution::Inferred(Inferred::new_any_from_error())
                    })
                };
                if file_index == self.file.file_index {
                    resolve(self)
                } else {
                    resolve(&mut self.with_new_file(self.i_s.db.loaded_python_file(file_index)))
                }
            }
            PointKind::Specific => match point.specific() {
                Specific::Param => PointResolution::Param {
                    node_ref: NodeRef::new(self.file, node_index),
                    maybe_self: false,
                },
                Specific::MaybeSelfParam => PointResolution::Param {
                    node_ref: NodeRef::new(self.file, node_index),
                    maybe_self: true,
                },
                Specific::GlobalVariable | Specific::NonlocalVariable => {
                    PointResolution::GlobalOrNonlocalName(NodeRef::new(self.file, node_index))
                }
                Specific::NameOfNameDef | Specific::FirstNameOfNameDef => {
                    // MultiDefinition means we are on a Name that has a NameDef as a
                    // parent.
                    let name_def_node_index = node_index - NAME_DEF_TO_NAME_DIFFERENCE;
                    let node_ref = NodeRef::new(self.file, name_def_node_index);
                    if self.stop_on_assignments {
                        let defining = node_ref.expect_name_def().expect_defining_stmt();
                        if matches!(
                            defining,
                            DefiningStmt::Assignment(_)
                                | DefiningStmt::FunctionDef(_)
                                | DefiningStmt::TypeAlias(_)
                        ) {
                            return PointResolution::NameDef {
                                node_ref,
                                global_redirect: global_redirect
                                    || node_ref.name_ref_of_name_def().point().in_global_scope(),
                            };
                        }
                    }
                    self.resolve_point_internal(
                        name_def_node_index,
                        node_ref.point(),
                        global_redirect,
                        narrow_name,
                    )
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
        add_issue: impl Fn(IssueKind) -> bool,
    ) -> Option<(PointResolution<'file>, Option<ModuleAccessDetail>)> {
        let result = self.resolve_module_access_internal(name, add_issue);
        if cfg!(feature = "zuban_debug") {
            if let Some((pr, _)) = &result {
                debug!(
                    "Module lookup {}.{name}: {}",
                    self.file.qualified_name(self.i_s.db),
                    pr.debug_info(self.i_s.db)
                );
            } else {
                debug!(
                    "Attribute lookup {name} on module {} failed",
                    self.file.qualified_name(self.i_s.db),
                );
            }
        }
        result
    }

    fn resolve_module_access_internal(
        &self,
        name: &str,
        add_issue: impl Fn(IssueKind) -> bool,
    ) -> Option<(PointResolution<'file>, Option<ModuleAccessDetail>)> {
        let db = self.i_s.db;
        Some(if let Some(name_ref) = self.file.lookup_symbol(name) {
            if let Some(r) = self.file.maybe_submodule_reexport(self.i_s, name_ref, name) {
                return Some((
                    PointResolution::Inferred(r.into_inferred()),
                    Some(ModuleAccessDetail::OnName(name_ref.as_link())),
                ));
            }
            if is_reexport_issue(db, name_ref) {
                if self.stop_on_assignments {
                    // Apparently types are resolved like this.
                    debug!(
                        "Found a type {name} in {} that was not reexported -> aborting",
                        self.file.qualified_name(self.i_s.db)
                    );
                    return None;
                }
                add_issue(IssueKind::ImportStubNoExplicitReexport {
                    module_name: self.file.qualified_name(db).into(),
                    attribute: name.into(),
                });
            }
            if self.stop_on_assignments
                && name_ref.point().maybe_specific() == Some(Specific::FirstNameOfNameDef)
            {
                let name_def_ref = name_ref.name_def_ref_of_name();
                let defining = name_def_ref.expect_name_def().expect_defining_stmt();
                if matches!(
                    defining,
                    DefiningStmt::Assignment(_) | DefiningStmt::FunctionDef(_)
                ) {
                    return Some((
                        PointResolution::NameDef {
                            node_ref: name_def_ref,
                            global_redirect: true,
                        },
                        Some(ModuleAccessDetail::OnName(name_ref.as_link())),
                    ));
                }
            }
            let mut resolved = self.resolve_name_without_narrowing(name_ref.expect_name());
            if let PointResolution::NameDef { node_ref, .. } = resolved {
                resolved = PointResolution::NameDef {
                    node_ref,
                    global_redirect: true,
                }
            }
            (
                resolved,
                Some(ModuleAccessDetail::OnName(name_ref.as_link())),
            )
        } else if let Some(r) = self.file.sub_module_lookup(db, name) {
            let to = match r {
                LookupResult::FileReference(file_index) => {
                    Some(ModuleAccessDetail::OnFile(file_index))
                }
                _ => None,
            };
            (PointResolution::Inferred(r.into_inferred()), to)
        } else if let Some((r, points_to)) =
            self.resolve_star_import_name(name, None, &|_, _, _| None)
        {
            (r, points_to.map(ModuleAccessDetail::OnName))
        } else if let Some(r) = self.file.lookup_symbol("__getattr__") {
            (PointResolution::ModuleGetattrName(r), None)
        } else {
            if name == "__path__" && !self.file.file_entry_and_is_package(db).1 {
                return None;
            }
            let mut result = LookupResult::None;
            // TODO it's a bit weird that we only do it on assignments.
            if !self.stop_on_assignments {
                result = db
                    .python_state
                    .module_instance()
                    .type_lookup(self.i_s, add_issue, name);
                if matches!(name, "__spec__" | "__file__" | "__package__") {
                    // __spec__ is special, because it always has a ModuleSpec and only if the module
                    // is __main__ it sometimes doesn't. But since __main__ is only ever known to Mypy
                    // as a static file it will also have a ModuleSpec and never be None, therefore we
                    // simply remove the None here.
                    // Also do the same for __file__ / __package__
                    // https://docs.python.org/3/reference/import.html#main-spec
                    result = result
                        .and_then(|inf| Some(inf.remove_none(self.i_s)))
                        .unwrap()
                }
            }
            if !result.is_some() {
                debug!(
                    "Did not find name {name} in {}",
                    self.file.qualified_name(db)
                );
            }
            (
                PointResolution::Inferred(result.into_maybe_inferred()?),
                None,
            )
        })
    }

    #[inline]
    fn resolve_star_import_name(
        &self,
        name: &str,
        save_to_index: Option<NodeIndex>,
        narrow_name: &dyn Fn(&InferenceState, NodeRef, PointLink) -> Option<Inferred>,
    ) -> Option<(PointResolution<'file>, Option<PointLink>)> {
        let star_imp = self.lookup_from_star_import(name, true)?;
        Some(match star_imp {
            StarImportResult::Link(link) => match save_to_index {
                Some(save_to_index) => {
                    self.set_point(
                        save_to_index,
                        Point::new_redirect(link.file, link.node_index, Locality::Todo),
                    );
                    (
                        self.resolve_point(save_to_index, narrow_name).unwrap(),
                        Some(link),
                    )
                }
                None => {
                    let node_ref = NodeRef::from_link(self.i_s.db, link);
                    (
                        self.with_new_file(node_ref.file)
                            .resolve_name(node_ref.expect_name(), narrow_name),
                        Some(link),
                    )
                }
            },
            StarImportResult::AnyDueToError => (
                PointResolution::Inferred(match save_to_index {
                    Some(save_to_index) => star_imp.as_inferred(self.i_s).save_redirect(
                        self.i_s,
                        self.file,
                        save_to_index,
                    ),
                    None => star_imp.as_inferred(self.i_s),
                }),
                None,
            ),
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
            let in_same_scope = star_import.scope == 0 || !in_mod;
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
            // Here we prefer modules, which is a debatable choice.
            let super_file = super_file.file(self.i_s.db);
            super_file
                .file_entry(self.i_s.db)
                .add_invalidation(self.file.file_index());
            if let Some(name_ref) = super_file.lookup_symbol(name) {
                return Some(StarImportResult::Link(name_ref.as_link()));
            }
            if let Some(_func) = self.i_s.current_function() {
                debug!("TODO lookup in func of sub file")
            } else if let Some(class) = self.i_s.current_class()
                && let Some(index) = class.class_storage.class_symbol_table.lookup_symbol(name)
            {
                return Some(StarImportResult::Link(PointLink::new(
                    class.node_ref.file_index(),
                    index,
                )));
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
            debug!("Aborting name import, because of a star import cycle");
            // TODO we might want to add an issue in the future (not high-prio however)
            return None;
        }
        let other_file = self.file.star_import_file(self.i_s.db, star_import)?;

        if let Some(name_ref) = other_file.lookup_symbol(name) {
            if !other_file.is_name_exported_for_star_import(self.i_s.db, name) {
                return None;
            }
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
            if !other_file.is_name_exported_for_star_import(self.i_s.db, name) {
                return None;
            }
            Some(l)
        } else {
            debug!(
                "Name {name} not found in star import {}",
                other_file.qualified_name(self.i_s.db)
            );
            None
        }
    }

    pub(super) fn lookup_type_name_on_class(
        &self,
        cls: ClassInitializer,
        name: Name,
    ) -> Option<PointResolution<'_>> {
        // This is needed to lookup names on a class and set the redirect there. It does not modify the
        // class at all.
        let name_node_ref = NodeRef::new(self.file, name.index());
        let point = name_node_ref.point();
        if point.calculated() {
            return if point.kind() == PointKind::Redirect {
                Some(self.resolve_name_without_narrowing(name))
            } else {
                debug_assert_eq!(point.specific(), Specific::AnyDueToError);
                None
            };
        }
        name_node_ref.set_point(
            if let Some(index) = cls
                .class_storage
                .class_symbol_table
                .lookup_symbol(name.as_str())
            {
                Point::new_redirect(cls.node_ref.file.file_index, index, Locality::Todo)
            } else {
                debug!("Type lookup: Attribute on class not found");
                Point::new_specific(Specific::AnyDueToError, Locality::Todo)
            },
        );
        self.lookup_type_name_on_class(cls, name)
    }

    pub fn add_issue(&self, node_index: NodeIndex, issue: IssueKind) -> bool {
        let from = NodeRef::new(self.file, node_index);
        from.maybe_add_issue(self.i_s, issue)
    }

    pub fn maybe_add_issue(&self, node_index: NodeIndex, issue: IssueKind) -> bool {
        let from = NodeRef::new(self.file, node_index);
        from.maybe_add_issue(self.i_s, issue)
    }

    pub fn flags(&self) -> &FinalizedTypeCheckerFlags {
        self.file.flags(self.i_s.db)
    }

    pub fn file_path(&self) -> &str {
        self.file.file_path(self.i_s.db)
    }

    pub fn point(&self, node_index: NodeIndex) -> Point {
        self.file.points.get(node_index)
    }

    pub fn set_point(&self, node_index: NodeIndex, p: Point) {
        self.file.points.set(node_index, p)
    }
}

#[derive(Debug, Copy, Clone)]
pub(crate) enum ModuleAccessDetail {
    OnName(PointLink),
    OnFile(FileIndex),
}

impl ModuleAccessDetail {
    pub fn into_point(self, locality: Locality) -> Point {
        match self {
            ModuleAccessDetail::OnName(link) => link.into_redirect_point(locality),
            ModuleAccessDetail::OnFile(file_index) => {
                Point::new_file_reference(file_index, locality)
            }
        }
    }
}

fn is_valid_builtins_export(name: &str) -> bool {
    !name.starts_with('_') || is_magic_method(name)
}

pub(crate) fn is_reexport_issue(db: &Database, name_ref: NodeRef) -> bool {
    if !name_ref.file.is_stub() && !name_ref.file.flags(db).no_implicit_reexport {
        return false;
    }
    is_private_import_and_not_in_dunder_all(db, name_ref, |_| true)
}

pub(crate) fn is_private_import_and_not_in_dunder_all(
    db: &Database,
    name_ref: NodeRef,
    ensure_private: impl FnOnce(NameImportParent) -> bool,
) -> bool {
    if let Some(dunder_all) = name_ref.file.maybe_dunder_all(db) {
        debug_assert!(name_ref.maybe_name().is_some());
        let name = name_ref.as_code();
        if dunder_all.iter().any(|d| d.as_str(db) == name) || name == "__all__" {
            // Name was exported in __all__
            return false;
        }
    }
    is_private_import_with_ensurance(name_ref, ensure_private)
}

fn is_private_import(name_ref: NodeRef) -> bool {
    is_private_import_with_ensurance(name_ref, |_| true)
}
fn is_private_import_with_ensurance(
    name_ref: NodeRef,
    ensure_private: impl FnOnce(NameImportParent) -> bool,
) -> bool {
    name_ref
        .maybe_import_of_name_in_symbol_table()
        .is_some_and(|i| !i.is_stub_reexport() && ensure_private(i))
}
