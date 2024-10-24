use std::{borrow::Cow, cell::Cell, rc::Rc};

use parsa_python_cst::*;

use super::{
    diagnostics::{await_aiter_and_next, check_override},
    flow_analysis::has_custom_special_method,
    name_binder::GLOBAL_NONLOCAL_TO_NAME_DIFFERENCE,
    on_argument_type_error,
    python_file::StarImport,
    type_computation::ANNOTATION_TO_EXPR_DIFFERENCE,
    utils::{func_of_self_symbol, infer_dict_like},
    File, PythonFile, FLOW_ANALYSIS,
};
use crate::{
    arguments::{Args, KnownArgs, NoArgs, SimpleArgs},
    database::{ComplexPoint, Database, Locality, Point, PointKind, PointLink, Specific},
    debug,
    diagnostics::{Issue, IssueKind},
    file::type_computation::TypeCommentState,
    format_data::FormatData,
    getitem::SliceType,
    imports::{find_ancestor, global_import, python_import, ImportResult},
    inference_state::InferenceState,
    inferred::{
        add_attribute_error, specific_to_type, AttributeKind, Inferred, MroIndex, UnionValue,
    },
    matching::{
        format_got_expected, CouldBeALiteral, ErrorStrs, ErrorTypes, IteratorContent, LookupKind,
        Matcher, OnTypeError, ResultContext, TupleLenInfos,
    },
    new_class,
    node_ref::NodeRef,
    params::matches_simple_params,
    type_::{
        AnyCause, CallableContent, CallableParam, CallableParams, IterInfos, Literal, LiteralKind,
        LookupResult, NeverCause, ParamType, StarParamType, StarStarParamType, StringSlice, Tuple,
        TupleArgs, TupleUnpack, Type, UnionEntry, UnionType, Variance, WithUnpack,
    },
    type_helpers::{
        cache_class_name, is_private, is_private_import, is_reexport_issue_if_check_needed,
        lookup_in_namespace, Class, ClassLookupOptions, FirstParamKind, Function, GeneratorType,
        Instance, InstanceLookupOptions, LookupDetails, Module, TypeOrClass,
    },
    utils::debug_indent,
    TypeCheckerFlags,
};

const ENUM_NAMES_OVERRIDABLE: [&str; 2] = ["value", "name"];
const NAME_DEF_TO_DEFAULTDICT_DIFF: i64 = -1;

pub struct Inference<'db: 'file, 'file, 'i_s> {
    pub(super) file: &'file PythonFile,
    pub(super) i_s: &'i_s InferenceState<'db, 'i_s>,
}

macro_rules! check_point_cache_with {
    ($vis:vis $name:ident, $func:path, $ast:ident $(, $result_context:ident )?) => {
        $vis fn $name(&self, node: $ast $(, $result_context : &mut ResultContext)?) -> $crate::inferred::Inferred {
            if let Some(inferred) = self.check_point_cache(node.index()) {
                debug!(
                    "{} {:?} (#{}, {}:{}) from cache: {}",
                    stringify!($name),
                    node.short_debug(),
                    self.file.byte_to_line_column(node.start()).0,
                    self.file.file_index,
                    node.index(),
                    {
                        let point = self.file.points.get(node.index());
                        match point.kind() {
                            PointKind::Specific => format!("Specific::{:?}", point.specific()),
                            PointKind::Redirect => format!("Redirect {}:{}", point.file_index(), point.node_index()),
                            _ => format!("PointKind::{:?}", point.kind()),
                        }
                    },
                );
                inferred
            } else {
                debug!(
                    "{} {:?} (#{}, {}:{})",
                    stringify!($name),
                    node.short_debug(),
                    self.file.byte_to_line_column(node.start()).0,
                    self.file.file_index,
                    node.index(),
                );
                debug_indent(|| {
                    $func(self, node $(, $result_context)?)
                })
            }
        }
    }
}

impl<'db, 'file, 'i_s> Inference<'db, 'file, 'i_s> {
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

        self.file
            .points
            .set(imp.index(), Point::new_node_analysis(Locality::Todo));
    }

    fn cache_import_from_only_particular_name_def(&self, as_name: ImportFromAsName) {
        let import_from = as_name.import_from();
        let from_first_part = self.import_from_first_part(import_from);
        self.cache_import_from_part(&from_first_part, as_name)
    }

    fn cache_import_from_part(
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
                match self.lookup_import_from_target(imp, import_name, name_def) {
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
                    Some(ImportResult::Namespace { .. }) => todo!("Star import on namespace"),
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
        self.file
            .points
            .set(imp.index(), Point::new_node_analysis(Locality::Todo));
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

    fn lookup_import_from_target(
        &self,
        from_first_part: &ImportResult,
        import_name: Name,
        import_name_def: NameDef,
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
                lookup_in_namespace(self.i_s.db, self.file.file_index, namespace, name)
            }
        }
    }

    fn global_import(&self, name: Name, name_def: Option<NameDef>) -> Option<ImportResult> {
        let result = global_import(self.i_s.db, self.file.file_index, name.as_str());
        if let Some(result) = &result {
            debug!(
                "Global import '{}': {:?}",
                name.as_code(),
                result.debug_path(self.i_s.db),
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
        let file_index = self.file.file_index;
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
                ImportResult::Namespace(namespace) => python_import(
                    i_s.db,
                    file_index,
                    namespace.directories.iter().cloned(),
                    name.as_str(),
                ),
            };
            if let Some(imported) = &result {
                debug!(
                    "Imported {:?} for {:?}",
                    imported.debug_path(i_s.db),
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
            None => node_ref.set_point(Point::new_specific(
                Specific::ModuleNotFound,
                Locality::Complex,
            )),
        }
        result
    }

    fn inferred_context_for_simple_assignment(
        &self,
        targets: AssignmentTargetIterator,
    ) -> Option<Inferred> {
        for target in targets {
            match target {
                Target::IndexExpression(t) => {
                    let base = self.infer_primary_target_or_atom(t.first());
                    let PrimaryContent::GetItem(slice) = t.second() else {
                        unreachable!();
                    };
                    if base.is_saved_partial(self.i_s.db) {
                        return None;
                    }
                    return Some(
                        base.as_cow_type(self.i_s).setitem_context(
                            self.i_s,
                            &SliceType::new(self.file, t.index(), slice),
                        ),
                    );
                }
                Target::NameExpression(primary_target, name_def) => {
                    let base = self.infer_primary_target_or_atom(primary_target.first());
                    let lookup = if let Some(c) =
                        base.as_cow_type(self.i_s).maybe_type_of_class(self.i_s.db)
                    {
                        // We need to handle class descriptors separately, because
                        // there the __get__ descriptor should not be applied.
                        c.lookup(
                            self.i_s,
                            name_def.as_code(),
                            ClassLookupOptions::new(&|_| ()).without_descriptors(),
                        )
                        .lookup
                    } else {
                        let t = base.as_cow_type(self.i_s);
                        if matches!(t.as_ref(), Type::Self_) {
                            // For now giving Self a context is hard, because if we do that we have
                            // a lot of problems with non-finished partial lists for example.
                            let Some(cls) = self.i_s.current_class() else {
                                continue; // TODO this should always be defined.
                            };
                            cls.instance()
                                .lookup(
                                    self.i_s,
                                    name_def.as_code(),
                                    InstanceLookupOptions::new(&|_| ())
                                        .without_object()
                                        .with_no_check_dunder_getattr()
                                        .with_disallowed_lazy_bound_method(),
                                )
                                .lookup
                        } else {
                            t.lookup(
                                self.i_s,
                                self.file.file_index,
                                name_def.as_code(),
                                LookupKind::Normal,
                                &mut ResultContext::Unknown,
                                // Errors don't matter, we just want a potential context.
                                &|_| (),
                                &|_| (),
                            )
                        }
                    };
                    if let Some(result) = lookup.into_maybe_inferred() {
                        if result
                            .maybe_saved_specific(self.i_s.db)
                            .is_some_and(|s| s.is_partial_container())
                        {
                            continue;
                        }
                        return Some(result);
                    }
                }
                _ => {
                    if let Some(inferred) = self.infer_target(target, false) {
                        return Some(inferred);
                    }
                }
            }
        }
        None
    }

    fn set_calculating_on_target(&self, target: Target) {
        match target {
            Target::Name(name_def) | Target::NameExpression(_, name_def) => {
                self.file
                    .points
                    .set(name_def.index(), Point::new_calculating());
            }
            Target::IndexExpression(t) => (),
            Target::Tuple(targets) => {
                for target in targets {
                    self.set_calculating_on_target(target);
                }
            }
            Target::Starred(s) => self.set_calculating_on_target(s.as_target()),
        }
    }

    fn check_right_side_against_expected(
        &self,
        expected: &Type,
        right: Inferred,
        right_side: AssignmentRightSide,
    ) {
        let on_type_error = |error_types: &ErrorTypes| {
            // In cases of stubs when an ellipsis is given, it's not an error.
            if self.file.is_stub() {
                // Right side always exists, because it was compared and there was an error because
                // of it.
                if let AssignmentRightSide::StarExpressions(star_exprs) = right_side {
                    if let StarExpressionContent::Expression(expr) = star_exprs.unpack() {
                        if expr.is_ellipsis_literal() {
                            return None;
                        }
                    }
                }
            }
            let ErrorStrs { expected, got } = error_types.as_boxed_strs(self.i_s.db);
            Some(IssueKind::IncompatibleAssignment { got, expected })
        };
        expected.error_if_not_matches(
            self.i_s,
            &right,
            |issue| self.add_issue(right_side.index(), issue),
            on_type_error,
        );
    }

    pub fn check_right_side_against_annotation(
        &self,
        expected: &Type,
        right_side: AssignmentRightSide,
    ) {
        let right = self.infer_assignment_right_side(
            right_side,
            &mut ResultContext::Known {
                type_: expected,
                from_annotation: true,
            },
        );
        self.check_right_side_against_expected(expected, right, right_side)
    }

    pub fn assign_for_annotation(&self, annotation: Annotation, target: Target, node_ref: NodeRef) {
        let inf_annot = self.use_cached_annotation(annotation);
        self.assign_single_target(
            target,
            node_ref,
            &inf_annot,
            AssignKind::Annotation {
                specific: inf_annot.maybe_saved_specific(self.i_s.db),
            },
            |index, value| {
                if matches!(
                    value.maybe_complex_point(self.i_s.db),
                    Some(ComplexPoint::IndirectFinal(_))
                ) {
                    value.clone().save_redirect(self.i_s, self.file, index);
                } else {
                    self.file.points.set(
                        index,
                        Point::new_redirect(
                            self.file.file_index,
                            annotation.index(),
                            Locality::Todo,
                        ),
                    );
                }
            },
        )
    }

    pub fn cache_assignment(&self, assignment: Assignment) {
        let node_ref = NodeRef::new(self.file, assignment.index());
        if node_ref.point().calculated() {
            return;
        }
        debug!("Cache assignment {}", assignment.as_code());
        match assignment.unpack() {
            AssignmentContent::Normal(targets, right_side) => {
                for target in targets {
                    self.set_calculating_on_target(target);
                }
            }
            AssignmentContent::WithAnnotation(target, _, right_side) => {
                self.set_calculating_on_target(target);
            }
            AssignmentContent::AugAssign(target, aug_assign, right_side) => (),
        };
        match assignment.unpack() {
            AssignmentContent::Normal(targets, right_side) => {
                let type_comment_result = self.check_for_type_comment(assignment);

                let assign_kind = match type_comment_result.as_ref() {
                    Some(r) => AssignKind::Annotation {
                        specific: r.inferred.maybe_saved_specific(self.i_s.db),
                    },
                    None => AssignKind::Normal,
                };
                let right = if let Some(type_comment) = type_comment_result {
                    match type_comment.type_ {
                        TypeCommentState::Type(t) => {
                            let right = self.infer_assignment_right_side(
                                right_side,
                                &mut ResultContext::Known {
                                    type_: &t,
                                    from_annotation: true,
                                },
                            );
                            // It is very weird, but somehow type comments in Mypy are allowed to
                            // have the form of `x = None  # type: int` in classes, even with
                            // strict-optional. It's even weirder that the form `x: int = None` is
                            // not allowed.
                            // The reason for this is apparently that with type comments there is
                            // no way to write x: int without a value. So they allowed None on type
                            // comments.
                            if !(self.i_s.in_class_scope().is_some()
                                && matches!(right.as_cow_type(self.i_s).as_ref(), Type::None))
                            {
                                self.check_right_side_against_expected(&t, right, right_side)
                            }
                        }
                        TypeCommentState::UnfinishedFinalOrClassVar(node_ref) => {
                            self.fill_potentially_unfinished_final_or_class_var(
                                node_ref,
                                Some(right_side),
                            );
                        }
                    }
                    type_comment.inferred
                } else {
                    let inf = self.inferred_context_for_simple_assignment(targets.clone());
                    let return_type = inf.as_ref().map(|inf| inf.as_cow_type(self.i_s));
                    let mut result_context = match &return_type {
                        Some(t) => ResultContext::new_known(&t),
                        None => ResultContext::AssignmentNewDefinition,
                    };
                    self.infer_assignment_right_side(right_side, &mut result_context)
                        .avoid_implicit_literal(self.i_s)
                };
                let n = NodeRef::new(self.file, right_side.index());
                for target in targets {
                    self.assign_targets(target, right.clone(), n, assign_kind)
                }
            }
            AssignmentContent::WithAnnotation(target, annotation, right_side) => {
                self.ensure_cached_annotation(annotation, right_side.is_some());
                let specific = self.file.points.get(annotation.index()).maybe_specific();
                let assign_kind = AssignKind::Annotation { specific };
                match specific {
                    Some(Specific::AnnotationTypeAlias) => {
                        let inf = self.compute_explicit_type_assignment(assignment);
                        self.assign_single_target(
                            target,
                            node_ref,
                            &inf,
                            assign_kind,
                            |index, inf| {
                                inf.clone().save_redirect(self.i_s, self.file, index);
                            },
                        );
                    }
                    _ => {
                        let mut checked = false;
                        if matches!(
                            specific,
                            Some(
                                Specific::AnnotationOrTypeCommentFinal
                                    | Specific::AnnotationOrTypeCommentClassVar
                            )
                        ) {
                            checked = self.fill_potentially_unfinished_final_or_class_var(
                                NodeRef::new(self.file, annotation.index()),
                                right_side,
                            )
                        }
                        if let Some(right_side) = right_side {
                            if !checked {
                                let t = self.use_cached_annotation_type(annotation);
                                self.check_right_side_against_annotation(&t, right_side);
                            }
                        }
                        self.assign_for_annotation(annotation, target, node_ref)
                    }
                }
            }
            AssignmentContent::AugAssign(target, aug_assign, right_side) => {
                let (inplace_method, op_infos) = aug_assign.magic_methods();
                let right =
                    self.infer_assignment_right_side(right_side, &mut ResultContext::Unknown);
                if let Some(left) = self.infer_target(target.clone(), true) {
                    let had_lookup_error = Cell::new(false);
                    let mut result = left.type_lookup_and_execute(
                        self.i_s,
                        node_ref.file,
                        inplace_method,
                        &KnownArgs::new(&right, node_ref),
                        &|type_| had_lookup_error.set(true),
                    );
                    let had_error = Cell::new(false);
                    if had_lookup_error.get() {
                        result = self.infer_detailed_operation(
                            right_side.index(),
                            op_infos,
                            left,
                            &right,
                        )
                    }

                    let n = NodeRef::new(self.file, right_side.index());
                    self.assign_single_target(
                        target,
                        n,
                        &result,
                        AssignKind::AugAssign,
                        |index, _| {
                            // There is no need to save this, because it's never used
                        },
                    )
                } else if self
                    .maybe_partial_aug_assignment(&target, aug_assign, right)
                    .is_none()
                {
                    // This is essentially a bare `foo += 1` that does not have any definition and
                    // leads to a NameError within Python.
                    match target.clone() {
                        Target::Name(name_def) => self.add_issue(
                            name_def.index(),
                            IssueKind::NameError {
                                name: name_def.as_code().into(),
                            },
                        ),
                        Target::NameExpression(t, n) => self.add_issue(
                            assignment.index(),
                            IssueKind::AttributeError {
                                name: n.as_code().into(),
                                object: format!(
                                    "\"{}\"",
                                    self.infer_primary_target(t)
                                        .unwrap_or_else(|| Inferred::from_type(Type::Self_))
                                        .format_short(self.i_s)
                                )
                                .into(),
                            },
                        ),
                        // Should probably never happen, because the target should always be
                        // inferrable
                        Target::IndexExpression(_) => unreachable!(),
                        // Invalid syntax
                        Target::Tuple(_) | Target::Starred(_) => unreachable!(),
                    }
                    self.assign_any_to_target(target, node_ref)
                }
            }
        }
        self.file
            .points
            .set(assignment.index(), Point::new_node_analysis(Locality::Todo));
    }

    fn maybe_partial_aug_assignment(
        &self,
        target: &Target,
        aug_assign: AugAssign,
        right: Inferred,
    ) -> Option<()> {
        let name_index = match target {
            Target::Name(name_def) => name_def.name_index(),
            Target::NameExpression(_, name_def) => {
                let name_index = name_def.name_index();
                let specific = NodeRef::new(self.file, name_index)
                    .point()
                    .maybe_calculated_and_specific()?;
                debug_assert_eq!(specific, Specific::NameOfNameDef);
                name_index
            }
            _ => return None,
        };
        let first = first_defined_name_of_multi_def(self.file, name_index)?;
        let maybe_partial_node_ref = NodeRef::new(self.file, first - NAME_DEF_TO_NAME_DIFFERENCE);
        let point = maybe_partial_node_ref.point();
        let specific = point.maybe_calculated_and_specific()?;
        let wanted = if specific == Specific::PartialList && aug_assign.as_code() == "+=" {
            self.i_s.db.python_state.list_node_ref()
        } else if specific == Specific::PartialSet && aug_assign.as_code() == "|=" {
            self.i_s.db.python_state.set_node_ref()
        } else {
            return None;
        };
        let mut right_t = right.as_type(self.i_s);
        if right_t.is_any() {
            right_t = self.i_s.db.python_state.list_of_any.clone()
        }
        let class = right_t.maybe_class(self.i_s.db)?;
        if class.node_ref != wanted {
            return None;
        }
        if class.nth_type_argument(self.i_s.db, 0).is_never() {
            // This adds an empty list again, which should be fine.
            return Some(());
        }
        maybe_partial_node_ref.insert_type(right_t.clone());
        Some(())
    }

    fn infer_assignment_right_side(
        &self,
        right: AssignmentRightSide,
        result_context: &mut ResultContext,
    ) -> Inferred {
        match right {
            AssignmentRightSide::StarExpressions(star_exprs) => {
                self.infer_star_expressions(star_exprs, result_context)
            }
            AssignmentRightSide::YieldExpr(yield_expr) => {
                self.infer_yield_expr(yield_expr, result_context)
            }
        }
    }

    pub fn fill_potentially_unfinished_final_or_class_var(
        &self,
        annotation_ref: NodeRef,
        right_side: Option<AssignmentRightSide>,
    ) -> bool {
        let to_annot_expr = annotation_ref.add_to_node_index(ANNOTATION_TO_EXPR_DIFFERENCE as i64);
        let needed_recalculation = !to_annot_expr.point().calculated();
        if needed_recalculation {
            let mut t = if let Some(right_side) = right_side {
                self.infer_assignment_right_side(right_side, &mut ResultContext::Unknown)
                    .as_type(self.i_s)
            } else {
                annotation_ref.add_issue(self.i_s, IssueKind::FinalWithoutInitializerAndType);
                Type::Any(AnyCause::FromError)
            };
            if annotation_ref.point().specific() == Specific::AnnotationOrTypeCommentClassVar {
                t = t.avoid_implicit_literal(self.i_s.db);
            }
            to_annot_expr.insert_type(t);
        }
        needed_recalculation
    }

    pub fn infer_yield_expr(
        &self,
        yield_expr: YieldExpr,
        result_context: &mut ResultContext,
    ) -> Inferred {
        let i_s = self.i_s;
        let from = NodeRef::new(self.file, yield_expr.index());
        let Some(current_function) = self.i_s.current_function() else {
            // The name binder already added an issue here.
            return Inferred::new_any_from_error();
        };
        let generator = current_function
            .generator_return(i_s)
            // In case we do not know the generator return, just return an Any version of it. The
            // function type will be checked in a different place.
            .unwrap_or(GeneratorType {
                yield_type: Type::Any(AnyCause::FromError),
                send_type: Some(Type::Any(AnyCause::FromError)),
                return_type: Some(Type::Any(AnyCause::FromError)),
            });

        match yield_expr.unpack() {
            YieldExprContent::StarExpressions(s) => {
                let inf = self.infer_star_expressions(
                    s,
                    &mut ResultContext::new_known(&generator.yield_type),
                );
                Inferred::from_type(generator.yield_type)
                    .as_cow_type(i_s)
                    .error_if_not_matches(
                        i_s,
                        &inf,
                        |issue| from.add_issue(i_s, issue),
                        |error_types| {
                            let ErrorStrs { expected, got } = error_types.as_boxed_strs(i_s.db);
                            Some(IssueKind::IncompatibleTypes {
                                cause: "\"yield\"",
                                got,
                                expected,
                            })
                        },
                    );
            }
            YieldExprContent::YieldFrom(yield_from) => {
                if current_function.is_async() {
                    // The name binder already added an issue here.
                    return Inferred::new_any_from_error();
                }
                let expr_result = self.infer_expression(yield_from.expression());
                let added_iter_issue = Cell::new(false);
                let iter_result = expr_result.type_lookup_and_execute(
                    i_s,
                    from.file,
                    "__iter__",
                    &NoArgs::new(from),
                    &|_| {
                        if !added_iter_issue.get() {
                            added_iter_issue.set(true);
                            from.add_issue(
                                i_s,
                                IssueKind::YieldFromCannotBeApplied {
                                    to: expr_result.format_short(i_s),
                                },
                            )
                        }
                    },
                );
                let yields = iter_result.type_lookup_and_execute(
                    i_s,
                    from.file,
                    "__next__",
                    &NoArgs::new(from),
                    &|_| todo!(),
                );
                generator.yield_type.error_if_not_matches(
                    i_s,
                    &yields,
                    |issue| from.add_issue(i_s, issue),
                    |error_types| {
                        let ErrorStrs { expected, got } = error_types.as_boxed_strs(self.i_s.db);
                        Some(IssueKind::IncompatibleTypes {
                            cause: "\"yield from\"",
                            got,
                            expected,
                        })
                    },
                );
                return if let Some(other) =
                    GeneratorType::from_type(i_s.db, iter_result.as_cow_type(i_s))
                {
                    if let Some(return_type) = other.return_type {
                        Inferred::from_type(return_type)
                    } else if result_context.expect_not_none(i_s) {
                        from.add_issue(i_s, IssueKind::DoesNotReturnAValue("Function".into()));
                        Inferred::new_any_from_error()
                    } else {
                        Inferred::new_none()
                    }
                } else {
                    // An invalid type, error should have been added by checking the function
                    Inferred::new_any_from_error()
                };
            }
            YieldExprContent::None => {
                if !generator
                    .yield_type
                    .is_simple_super_type_of(i_s, &Type::None)
                    .bool()
                {
                    from.add_issue(i_s, IssueKind::YieldValueExpected);
                }
            }
        }
        if let Some(send_type) = generator.send_type {
            Inferred::from_type(send_type)
        } else {
            Inferred::new_none()
        }
    }

    fn infer_target(&self, target: Target, from_aug_assign: bool) -> Option<Inferred> {
        match target {
            Target::Name(name_def) => self.infer_name_target(name_def, from_aug_assign),
            Target::NameExpression(primary_target, _) => self.infer_primary_target(primary_target),
            Target::IndexExpression(t) if from_aug_assign => self.infer_primary_target(t),
            Target::Tuple(targets) => {
                let out: Option<Rc<[Type]>> = targets
                    .map(|target| {
                        self.infer_target(target, from_aug_assign)
                            .map(|i| i.as_type(self.i_s))
                    })
                    .collect();
                Some(Inferred::from_type(Type::Tuple(Tuple::new_fixed_length(
                    out?,
                ))))
            }
            _ => None,
        }
    }

    pub fn infer_name_target(&self, name_def: NameDef, narrow: bool) -> Option<Inferred> {
        if name_def.as_code() == "__slots__" {
            return None;
        }
        let check_fallback = |name_def: NameDef| {
            self.i_s
                .in_class_scope()
                .and_then(|cls| {
                    if cls.is_calculating_class_infos() {
                        return None;
                    }
                    cls.instance()
                        .lookup(
                            self.i_s,
                            name_def.as_code(),
                            InstanceLookupOptions::new(&|_| ())
                                .with_skip_first_of_mro(self.i_s.db, &cls),
                        )
                        .lookup
                        .into_maybe_inferred()
                })
                .or_else(|| {
                    Some(
                        self.lookup_from_star_import(name_def.as_code(), true)?
                            .as_inferred(self.i_s),
                    )
                })
        };
        let name_index = name_def.name_index();
        first_defined_name_of_multi_def(self.file, name_index)
            .and_then(|first_index| {
                // The first definition is always responsible for how a name is defined.
                // So we try to look up active narrowings first or we try to lookup the first
                // name.
                let name_def_ref =
                    NodeRef::new(self.file, first_index - NAME_DEF_TO_NAME_DIFFERENCE);
                let point = name_def_ref.point();
                if point.calculated() && point.maybe_specific().is_some_and(|s| s.is_partial())
                    || point.calculating()
                {
                    return None;
                }
                if narrow {
                    if let Some(result) = self.maybe_lookup_narrowed_name(
                        name_index,
                        PointLink::new(self.file.file_index, first_index),
                    ) {
                        return Some(result);
                    }
                }
                // TODO check base class!
                Some(self.infer_name_of_definition_by_index(first_index))
            })
            .or_else(|| check_fallback(name_def))
    }

    #[inline]
    fn assign_and_override_in_subclass(
        &self,
        name_def: NameDef,
        from: NodeRef,
        assign_kind: AssignKind,
        override_class: &Class,
        value: &Inferred,
        ancestor_lookup: &LookupDetails,
        ancestor_inf: &Inferred,
        save: impl FnOnce(NodeIndex, &Inferred),
    ) {
        let i_s = self.i_s;
        let declaration_t = ancestor_inf.as_cow_type(self.i_s);
        let first_name_link = PointLink::new(
            self.file.file_index,
            first_defined_name(self.file, name_def.name_index()),
        );
        let name_str = name_def.as_code();
        if ancestor_lookup.attr_kind.is_final() {
            from.add_issue(
                i_s,
                if matches!(
                    assign_kind,
                    AssignKind::Annotation {
                        specific: Some(Specific::AnnotationOrTypeCommentFinal)
                    }
                ) || !matches!(ancestor_lookup.attr_kind, AttributeKind::Final)
                {
                    IssueKind::CannotOverrideFinalAttribute {
                        name: name_str.into(),
                        base_class: ancestor_lookup.class.name(i_s.db).into(),
                    }
                } else {
                    IssueKind::CannotAssignToFinal {
                        name: name_str.into(),
                        is_attribute: false,
                    }
                },
            );
            save(
                name_def.index(),
                &Inferred::new_unsaved_complex(ComplexPoint::IndirectFinal(Rc::new(
                    ancestor_inf.as_type(i_s),
                ))),
            );
            return;
        }
        let attr_kind = match assign_kind {
            AssignKind::Annotation {
                specific: Some(Specific::AnnotationOrTypeCommentClassVar),
            } => AttributeKind::ClassVar,
            AssignKind::Annotation {
                specific: Some(Specific::AnnotationOrTypeCommentFinal),
            } => AttributeKind::Final,
            AssignKind::Annotation { .. } => AttributeKind::AnnotatedAttribute,
            _ => AttributeKind::Attribute,
        };
        let mut had_error = false;
        self.narrow_or_widen_name_target(
            first_name_link,
            &declaration_t,
            &value.as_cow_type(i_s),
            || {
                // TODO all these clones feel weird.
                let bound_inf = if let Some((new, _)) = value.clone().bind_instance_descriptors(
                    i_s,
                    name_str,
                    override_class.as_type(i_s.db),
                    *override_class,
                    |issue| from.add_issue(i_s, issue),
                    MroIndex(0),
                    false,
                ) {
                    new
                } else {
                    value.clone()
                };
                let override_class_infos = override_class.use_cached_class_infos(i_s.db);
                if let Some(t) = override_class_infos.undefined_generics_type.get() {
                    if let Type::Enum(e) = t.as_ref() {
                        if e.members
                            .iter()
                            .any(|member| member.name(i_s.db) == name_str)
                            && !ENUM_NAMES_OVERRIDABLE.contains(&name_str)
                        {
                            from.add_issue(
                                i_s,
                                IssueKind::CannotOverrideWritableWithFinalAttribute {
                                    name: name_str.into(),
                                },
                            )
                        }
                    }
                }
                let matched = check_override(
                    i_s,
                    from,
                    ancestor_lookup.clone(),
                    &LookupDetails {
                        class: TypeOrClass::Class(*override_class),
                        lookup: LookupResult::UnknownName(bound_inf),
                        attr_kind,
                        mro_index: None,
                    },
                    name_str,
                    |db, c| c.name(db),
                    None,
                );
                had_error = !matched;
                matched
            },
        );
        if had_error && assign_kind == AssignKind::Normal {
            save(name_def.index(), ancestor_inf);
        } else {
            save(name_def.index(), value);
        }
    }
    fn assign_to_name_def_simple(
        &self,
        name_def: NameDef,
        from: NodeRef,
        value: &Inferred,
        assign_kind: AssignKind,
    ) {
        self.assign_to_name_def(name_def, from, &value, assign_kind, |index, value| {
            value.clone().save_redirect(self.i_s, self.file, index);
        });
    }

    fn assign_to_name_def(
        &self,
        name_def: NameDef,
        from: NodeRef,
        value: &Inferred,
        assign_kind: AssignKind,
        save: impl FnOnce(NodeIndex, &Inferred),
    ) {
        debug!(
            "Assign to name def {} (#{}, {}:{})",
            name_def.as_code(),
            self.file.byte_to_line_column(name_def.start()).0,
            self.file.file_index,
            name_def.index(),
        );
        debug_indent(|| self.assign_to_name_def_internal(name_def, from, value, assign_kind, save))
    }

    fn assign_to_name_def_internal(
        &self,
        name_def: NameDef,
        from: NodeRef,
        value: &Inferred,
        assign_kind: AssignKind,
        save: impl FnOnce(NodeIndex, &Inferred),
    ) {
        let i_s = self.i_s;
        if let Some(class) = i_s.in_class_scope() {
            let name_str = name_def.as_code();
            if class.node_ref != i_s.db.python_state.bare_type_node_ref()
                && name_str != "__slots__"
                && !is_private(name_str)
                // This happens for NamedTuples and should probably not be here, but otherwise we
                // cannot do lookups.
                && !class.is_calculating_class_infos()
            {
                // Handle assignments in classes where the variable exists in a super class.
                let ancestor_lookup = class.instance().lookup(
                    i_s,
                    name_str,
                    InstanceLookupOptions::new(&|issue| ()).with_skip_first_of_mro(i_s.db, class),
                );
                // __hash__ is allowed to be rewritten to None
                if let Some(ancestor_inf) = ancestor_lookup.lookup.maybe_inferred().filter(|_| {
                    !(name_str == "__hash__" && ancestor_lookup.class.is_object(i_s.db))
                }) {
                    self.assign_and_override_in_subclass(
                        name_def,
                        from,
                        assign_kind,
                        class,
                        value,
                        &ancestor_lookup,
                        &ancestor_inf,
                        save,
                    );
                    return;
                }
            }
        }
        self.assign_to_name_def_or_self_name_def(
            name_def,
            from,
            value,
            assign_kind,
            save,
            None,
            |first_name_link, declaration_t| {
                let current_t = value.as_cow_type(i_s);
                self.narrow_or_widen_name_target(first_name_link, declaration_t, &current_t, || {
                    self.check_assignment_type(value, declaration_t, from, None, assign_kind)
                })
            },
        )
    }

    fn check_assignment_type(
        &self,
        value: &Inferred,
        declaration_t: &Type,
        from: NodeRef,
        base_class: Option<TypeOrClass>,
        assign_kind: AssignKind,
    ) -> bool {
        let mut had_error = false;
        declaration_t.error_if_not_matches(
            self.i_s,
            value,
            |issue| from.add_issue(self.i_s, issue),
            |error_types| {
                had_error = true;
                let ErrorStrs { expected, got } = error_types.as_boxed_strs(self.i_s.db);
                if let Some(base_class) = base_class.as_ref() {
                    Some(IssueKind::IncompatibleAssignmentInSubclass {
                        base_class: base_class.name(self.i_s.db).into(),
                        got,
                        expected,
                    })
                } else if matches!(assign_kind, AssignKind::Import) {
                    Some(IssueKind::IncompatibleImportAssignment {
                        name: from.as_code().into(),
                        got,
                        expected,
                    })
                } else {
                    Some(IssueKind::IncompatibleAssignment { got, expected })
                }
            },
        );
        had_error
    }

    fn assign_to_name_def_or_self_name_def<'x>(
        &self,
        name_def: NameDef,
        from: NodeRef,
        value: &Inferred,
        assign_kind: AssignKind,
        save: impl FnOnce(NodeIndex, &Inferred),
        lookup_self_attribute_in_bases: Option<&dyn Fn() -> LookupDetails<'x>>,
        narrow: impl Fn(PointLink, &Type),
    ) {
        let current_index = name_def.name_index();
        let i_s = self.i_s;

        let check_assign_to_known_definition =
            |first_name_link, original: &Inferred, base_class| {
                let declaration_t = original.as_cow_type(i_s);
                if original.add_issue_if_final_assignment(
                    i_s,
                    from,
                    name_def.as_code(),
                    lookup_self_attribute_in_bases.is_some(),
                ) {
                    self.check_assignment_type(
                        value,
                        &declaration_t.into_owned().avoid_implicit_literal(i_s.db),
                        from,
                        None,
                        assign_kind,
                    );
                    return;
                }

                if matches!(assign_kind, AssignKind::Annotation { .. }) {
                    self.check_assignment_type(
                        value,
                        &declaration_t,
                        from,
                        base_class,
                        assign_kind,
                    );
                } else {
                    narrow(first_name_link, &declaration_t)
                }
            };
        let set_defaultdict_type = |name_node_ref: NodeRef, t| {
            // It feels very weird that we're saving on the index before the defaultdict
            // definition, but it seems to be fine since this should either be a `,` for tuple
            // assignments or a `.` for self assignments or a star_targets / single_target that is
            // not used.
            let save_to = name_node_ref.add_to_node_index(NAME_DEF_TO_DEFAULTDICT_DIFF);
            assert!(!save_to.point().calculated());
            save_to.insert_type(t)
        };
        let check_assign_including_partials = |first_index, original: &Inferred, base_class| {
            if let Some(saved_node_ref) = original.maybe_saved_node_ref(i_s.db) {
                let point = saved_node_ref.point();
                let maybe_overwrite_partial = |class_node_ref, type_when_any: &Type| {
                    let mut partial_flags = point.partial_flags();
                    if partial_flags.finished {
                        return false;
                    }
                    let t = value.as_cow_type(i_s);
                    if t.maybe_class(i_s.db)
                        .is_some_and(|c| c.node_ref == class_node_ref)
                    {
                        if t.has_never_from_inference(i_s.db) {
                            saved_node_ref.finish_partial_with_annotation_needed(i_s)
                        } else {
                            saved_node_ref.insert_type(value.as_type(i_s))
                        }
                        return true;
                    }
                    if t.is_any() {
                        partial_flags.finished = true;
                        // There should never be an error, because we assigned Any.
                        partial_flags.reported_error = true;
                        saved_node_ref.set_point(point.set_partial_flags(partial_flags));
                        return true;
                    }
                    false
                };
                let is_done = match point.maybe_specific() {
                    Some(Specific::PartialNone) => {
                        if let Some(p) = value.maybe_new_nullable_partial_point(i_s, |t| todo!()) {
                            saved_node_ref.set_point(p);
                            return;
                        }
                        let value_t = value.as_cow_type(i_s);
                        if !matches!(value_t.as_ref(), Type::None) {
                            if point.partial_flags().finished {
                                // For --local-partial-types an error was already added
                                if !self.flags().local_partial_types {
                                    self.check_assignment_type(
                                        value,
                                        &Type::None,
                                        from,
                                        None,
                                        assign_kind,
                                    );
                                }
                                return;
                            }
                            saved_node_ref.insert_type(value_t.simplified_union(i_s, &Type::None));
                            narrow(PointLink::new(self.file.file_index, first_index), &value_t);
                        }
                        return;
                    }
                    Some(Specific::PartialList) => maybe_overwrite_partial(
                        i_s.db.python_state.list_node_ref(),
                        &i_s.db.python_state.list_of_any,
                    ),
                    Some(Specific::PartialDict) => maybe_overwrite_partial(
                        i_s.db.python_state.dict_node_ref(),
                        &i_s.db.python_state.dict_of_any,
                    ),
                    Some(Specific::PartialSet) => maybe_overwrite_partial(
                        i_s.db.python_state.set_node_ref(),
                        &i_s.db.python_state.set_of_any,
                    ),
                    _ => false,
                };
                if is_done {
                    return;
                }
            }
            check_assign_to_known_definition(
                PointLink::new(self.file.file_index, first_index),
                original,
                base_class,
            )
        };
        if let Some(first_index) = first_defined_name_of_multi_def(self.file, current_index) {
            let add_redefinition_issue = || {
                let name_def_ref = NodeRef::new(self.file, current_index);
                if matches!(
                    assign_kind,
                    AssignKind::Annotation {
                        specific: Some(Specific::AnnotationOrTypeCommentFinal)
                    }
                ) {
                    name_def_ref.add_issue(self.i_s, IssueKind::CannotRedefineAsFinal);
                } else {
                    self.add_redefinition_issue(
                        first_index,
                        name_def.as_code(),
                        lookup_self_attribute_in_bases.is_some(),
                        |issue| name_def_ref.add_issue(self.i_s, issue),
                    );
                }
            };

            if let Some(node_ref) = value.maybe_saved_node_ref(i_s.db) {
                let name_def_ref = NodeRef::new(self.file, current_index);
                let cannot_redefine = |as_| {
                    name_def_ref.add_issue(
                        self.i_s,
                        IssueKind::CannotRedefineAs {
                            name: name_def.as_code().into(),
                            as_,
                        },
                    );
                };
                match node_ref.complex() {
                    Some(ComplexPoint::NewTypeDefinition(_)) => {
                        cannot_redefine("a NewType");
                        add_redefinition_issue();
                        return;
                    }
                    Some(ComplexPoint::TypeVarLike(_)) => {
                        cannot_redefine("a type variable");
                        return;
                    }
                    _ => (),
                }
            }

            let maybe_saved = self.follow_and_maybe_saved(first_index);
            let maybe_complex_def = maybe_saved.and_then(|n| n.complex());
            // This is mostly to make it clear that things like NewType/TypeVars are special
            // and cannot be redefined
            let is_special_def = !matches!(
                maybe_complex_def,
                None | Some(ComplexPoint::TypeInstance(_) | ComplexPoint::IndirectFinal(_))
            );
            let assign_as_new_definition = match assign_kind {
                AssignKind::Annotation { .. } => true,
                AssignKind::Import => {
                    // Imports are a bit special since most of the time they are allowed and not
                    // considered a redefinition in Mypy and then there's unresolved imports and
                    // imports of files that are considered to be redefinitions.
                    if value.is_unsaved_module_not_found() {
                        true
                    } else {
                        maybe_saved.is_some_and(|n| {
                            if let Some(complex) = maybe_complex_def {
                                return is_special_def && !matches!(complex, ComplexPoint::Class(_) | ComplexPoint::FunctionOverload(_) | ComplexPoint::TypeAlias(_))
                            }
                            let p = n.point();
                            p.kind() == PointKind::FileReference && matches!(value.as_cow_type(i_s).as_ref(), Type::Module(f) if *f != p.file_index())
                        })
                    }
                }
                _ => is_special_def,
            };
            if assign_as_new_definition {
                add_redefinition_issue();
                // Nothing needed to assign anymore, the original definition was already assigned.
                return;
            }
            if let Some(lookup_in_bases) = lookup_self_attribute_in_bases {
                let lookup_details = lookup_in_bases();
                if let Some(inf) = lookup_details.lookup.into_maybe_inferred() {
                    if lookup_details.attr_kind == AttributeKind::Final {
                        from.add_issue(
                            i_s,
                            IssueKind::CannotAssignToFinal {
                                name: name_def.as_code().into(),
                                is_attribute: true,
                            },
                        );
                    } else {
                        check_assign_including_partials(first_index, &inf, None);
                    }
                    return;
                }
            }
            let original_inf = self.infer_name_of_definition_by_index(first_index);
            check_assign_including_partials(first_index, &original_inf, None)
        } else {
            if let Some(lookup_in_bases) = lookup_self_attribute_in_bases {
                let lookup_details = lookup_in_bases();
                if let Some(inf) = lookup_details.lookup.into_maybe_inferred() {
                    match assign_kind {
                        AssignKind::Annotation { specific: reason }
                            if matches!(
                                lookup_details.class,
                                TypeOrClass::Class(c)
                                if c.node_ref == i_s.current_class().unwrap().node_ref
                            ) =>
                        {
                            if reason == Some(Specific::AnnotationOrTypeCommentFinal) {
                                from.add_issue(self.i_s, IssueKind::CannotRedefineAsFinal);
                            } else {
                                if let Some(link) = inf
                                    .maybe_saved_node_ref(i_s.db)
                                    .filter(|node_ref| node_ref.maybe_name_def().is_some())
                                {
                                    debug_assert_eq!(link.file_index(), self.file.file_index);
                                    self.add_redefinition_issue(
                                        link.node_index + NAME_DEF_TO_NAME_DIFFERENCE,
                                        name_def.as_code(),
                                        true,
                                        |issue| from.add_issue(i_s, issue),
                                    )
                                }
                            }
                        }
                        _ => (),
                    }
                    if lookup_details.attr_kind.is_final() {
                        if let TypeOrClass::Class(c) = lookup_details.class {
                            let name_str = name_def.as_code();
                            // We cannot assign to final only in the case where the original
                            // definition in the parent class was not an assignment like:
                            //
                            //     class Foo:
                            //         x: Final[int]  # Not missing assignment, which is allowed
                            //         y: Final[int]
                            //         def __init__(self) -> None:
                            //             self.x = 1
                            //         def foo(self) -> None:
                            //             self.y = 1  # This is disallowed
                            if !c.lookup_assignment(name_str).is_some_and(|a| {
                                matches!(a.unpack(), AssignmentContent::WithAnnotation(_, _, None),)
                            }) || func_of_self_symbol(self.file, name_def.name_index())
                                .name_def()
                                .as_code()
                                != "__init__"
                            {
                                from.add_issue(
                                    i_s,
                                    match assign_kind {
                                        AssignKind::Annotation {
                                            specific: Some(Specific::AnnotationOrTypeCommentFinal),
                                        } => IssueKind::CannotOverrideFinalAttribute {
                                            name: name_str.into(),
                                            base_class: c.name().into(),
                                        },
                                        _ => IssueKind::CannotAssignToFinal {
                                            name: name_str.into(),
                                            is_attribute: true,
                                        },
                                    },
                                );
                            }
                        }
                        save(
                            name_def.index(),
                            &Inferred::new_unsaved_complex(ComplexPoint::IndirectFinal(Rc::new(
                                inf.as_type(i_s),
                            ))),
                        );
                    } else {
                        if !lookup_details.attr_kind.is_overwritable() {
                            from.add_issue(
                                i_s,
                                IssueKind::PropertyIsReadOnly {
                                    class_name: lookup_details.class.name(i_s.db).into(),
                                    property_name: name_def.as_code().into(),
                                },
                            );
                        }
                        check_assign_including_partials(
                            current_index,
                            &inf,
                            Some(lookup_details.class),
                        );
                        // TODO maybe this is needed?
                        //if matches!(assign_kind, AssignKind::Annotation { .. }) {
                        //save(name_def.index(), value);
                        //} else {
                        save(name_def.index(), &inf);
                        //}
                    }
                    return;
                }
            } else if let Some(star_imp) = self.lookup_from_star_import(name_def.as_code(), true) {
                let original = star_imp.as_inferred(self.i_s);
                match star_imp {
                    StarImportResult::Link(star_link) => {
                        let node_ref = NodeRef::from_link(self.i_s.db, star_link);
                        check_assign_to_known_definition(star_link, &original, None);
                    }
                    StarImportResult::AnyDueToError => (),
                };
                save(name_def.index(), &original);
                return;
            }
            if assign_kind == AssignKind::Normal {
                if let Some(partial) = value.maybe_new_partial(i_s, |t| {
                    set_defaultdict_type(NodeRef::new(self.file, name_def.index()), t)
                }) {
                    let name_def_index = name_def.index();
                    FLOW_ANALYSIS.with(|fa| {
                        fa.add_partial(PointLink::new(self.file.file_index, name_def_index))
                    });
                    save(name_def_index, &partial);

                    // Mypy does not flag partials in non-classes with "Need type annotation".
                    // However in class scopes (where we don't override a union of a superclass)
                    // and module scopes it can still lead to errors.
                    let point = self.file.points.get(name_def_index);
                    if point.maybe_specific() == Some(Specific::PartialNone) {
                        let suppresses_partial_none_error = || {
                            if !self.flags().local_partial_types {
                                return true;
                            }

                            if let Some(class) = i_s.in_class_scope() {
                                // TODO this case should not suppress, but behave entirely
                                // differently: Use the super class definition and then narrow?!
                                return class
                                    .lookup(
                                        self.i_s,
                                        name_def.as_code(),
                                        ClassLookupOptions::new(&|_| ()).with_ignore_self(),
                                    )
                                    .lookup
                                    .is_some();
                            }
                            i_s.current_function().is_some()
                        };
                        if suppresses_partial_none_error() {
                            let mut flags = point.partial_flags();
                            flags.reported_error = true;
                            self.file
                                .points
                                .set(name_def_index, point.set_partial_flags(flags))
                        }
                    }

                    return;
                } else if let Some(inf) =
                    value.maybe_never_from_inference(i_s, NodeRef::new(self.file, current_index))
                {
                    save(name_def.index(), &inf);
                    return;
                } else if lookup_self_attribute_in_bases.is_none()
                    && name_def.as_code() == "_"
                    && self.i_s.current_function().is_some()
                    && name_def.maybe_import().is_none()
                {
                    save(name_def.index(), &Inferred::new_any(AnyCause::Todo));
                    return;
                }
            }
            if let Some(value_without_final) = value.remove_final(i_s) {
                save(name_def.index(), &value_without_final);
            } else {
                save(name_def.index(), value);
            }
        }
    }

    fn check_assign_arbitrary_named_expr(
        &self,
        base: Inferred,
        primary_target: PrimaryTarget,
        name_def: NameDef,
        from: NodeRef,
        value: &Inferred,
        assign_kind: AssignKind,
    ) {
        let i_s = self.i_s;
        if matches!(assign_kind, AssignKind::Annotation { .. }) {
            self.add_issue(primary_target.index(), IssueKind::InvalidTypeDeclaration);
        }
        let base = base.as_cow_type(i_s);
        let node_ref = NodeRef::new(self.file, primary_target.index());
        let name_str = name_def.as_code();
        let mut had_error = false;
        for t in base.iter_with_unpacked_unions(i_s.db) {
            let property_is_read_only = |class_name| {
                from.add_issue(
                    i_s,
                    IssueKind::PropertyIsReadOnly {
                        class_name,
                        property_name: name_def.as_code().into(),
                    },
                )
            };
            match t {
                Type::Class(c) => {
                    had_error |= c
                        .class(i_s.db)
                        .instance()
                        .check_set_descriptor(i_s, node_ref, name_def.name(), value)
                        .is_err();
                    continue;
                }
                Type::Dataclass(d) => {
                    if d.options.frozen {
                        had_error = true;
                        property_is_read_only(d.class(i_s.db).name().into())
                    }
                    had_error |= Instance::new(d.class(i_s.db), None)
                        .check_set_descriptor(i_s, node_ref, name_def.name(), value)
                        .is_err();
                    continue;
                }
                Type::NamedTuple(nt) => {
                    if nt.search_param(i_s.db, name_def.as_code()).is_some() {
                        had_error = true;
                        property_is_read_only(nt.name(i_s.db).into());
                        continue;
                    }
                }
                Type::Type(type_) => match type_.as_ref() {
                    Type::Enum(enum_)
                        if enum_
                            .members
                            .iter()
                            .any(|member| member.name(i_s.db) == name_str) =>
                    {
                        had_error = true;
                        from.add_issue(
                            i_s,
                            IssueKind::CannotAssignToFinal {
                                is_attribute: true,
                                name: name_str.into(),
                            },
                        );
                        continue;
                    }
                    _ => (),
                },
                Type::Super { .. } => {
                    had_error = true;
                    from.add_issue(i_s, IssueKind::InvalidAssignmentTarget);
                    continue;
                }
                _ => (),
            }

            let mut lookup = LookupResult::None;
            let mut attr_kind = AttributeKind::Attribute;
            if let Some(c) = t.maybe_type_of_class(i_s.db) {
                // We need to handle class descriptors separately, because
                // there the __get__ descriptor should not be applied.
                let lookup_details = c.lookup(
                    i_s,
                    name_str,
                    ClassLookupOptions::new(&|issue| node_ref.add_issue(i_s, issue))
                        .without_descriptors(),
                );
                if let Some(inf) = lookup_details.lookup.maybe_inferred() {
                    if inf.as_cow_type(i_s).is_func_or_overload_not_any_callable() {
                        from.add_issue(i_s, IssueKind::CannotAssignToAMethod);
                    }
                }
                lookup = lookup_details.lookup;
                attr_kind = lookup_details.attr_kind;
            }
            lookup = lookup.or_else(|| {
                let result = t.lookup_with_first_attr_kind(
                    i_s,
                    node_ref.file_index(),
                    name_str,
                    LookupKind::Normal,
                    &mut ResultContext::Unknown,
                    &|issue| node_ref.add_issue(i_s, issue),
                    &|t| add_attribute_error(i_s, node_ref, &base, t, name_str),
                );
                attr_kind = result.1;
                result.0
            });
            let inf = lookup.into_inferred();
            let mut declaration_t = inf.as_cow_type(i_s);
            if attr_kind == AttributeKind::Final {
                from.add_issue(
                    i_s,
                    IssueKind::CannotAssignToFinal {
                        is_attribute: !matches!(t, Type::Module(_)),
                        name: name_str.into(),
                    },
                );
                declaration_t =
                    Cow::Owned(declaration_t.into_owned().avoid_implicit_literal(i_s.db));
                had_error = true;
            }
            declaration_t.error_if_not_matches(
                i_s,
                value,
                |issue| from.add_issue(i_s, issue),
                |error_types| {
                    had_error = true;
                    let ErrorStrs { expected, got } = error_types.as_boxed_strs(i_s.db);
                    Some(IssueKind::IncompatibleAssignment { got, expected })
                },
            );
        }
        if matches!(assign_kind, AssignKind::Normal) && !had_error {
            self.save_narrowed_primary_target(primary_target, &value.as_cow_type(self.i_s));
        }
    }

    fn assign_single_target(
        &self,
        target: Target,
        from: NodeRef,
        value: &Inferred,
        assign_kind: AssignKind,
        save: impl FnOnce(NodeIndex, &Inferred),
    ) {
        let i_s = self.i_s;
        match target {
            Target::Name(name_def) => {
                self.assign_to_name_def(name_def, from, value, assign_kind, save)
            }
            Target::NameExpression(primary_target, name_def) => {
                let base = self.infer_primary_target_or_atom(primary_target.first());
                if base.maybe_saved_specific(i_s.db) == Some(Specific::MaybeSelfParam) {
                    self.assign_to_name_def_or_self_name_def(
                        name_def,
                        from,
                        value,
                        assign_kind,
                        save,
                        Some(&|| {
                            // TODO this should never be None
                            let Some(c) = i_s.current_class() else {
                                return LookupDetails::any(AnyCause::Internal);
                            };
                            let ancestor_lookup = c.instance().lookup(
                                self.i_s,
                                name_def.as_code(),
                                InstanceLookupOptions::new(&|_| todo!())
                                    .with_skip_first_self_variables(),
                            );
                            ancestor_lookup
                        }),
                        |first_name_link, declaration_t| {
                            let current_t = value.as_cow_type(self.i_s);
                            self.narrow_or_widen_self_target(
                                primary_target,
                                declaration_t,
                                &current_t,
                                || {
                                    self.check_assignment_type(
                                        value,
                                        declaration_t,
                                        from,
                                        None,
                                        assign_kind,
                                    )
                                },
                            )
                        },
                    );
                    // TODO we should probably check if we are in a staticmethod/classmethod
                    // TODO The class should ALWAYS exist, this is just a bug at the moment.
                    if let Some(class) = i_s.current_class() {
                        class.check_self_definition(
                            i_s,
                            |issue| from.add_issue(i_s, issue),
                            name_def.as_code(),
                        );
                    }
                } else {
                    self.check_assign_arbitrary_named_expr(
                        base,
                        primary_target,
                        name_def,
                        from,
                        value,
                        assign_kind,
                    );
                    save(name_def.index(), value);
                }
            }
            Target::IndexExpression(primary_target) => {
                let base = self.infer_primary_target_or_atom(primary_target.first());
                if matches!(assign_kind, AssignKind::Annotation { .. }) {
                    self.add_issue(primary_target.index(), IssueKind::UnexpectedTypeDeclaration);
                }
                let PrimaryContent::GetItem(slice_type) = primary_target.second() else {
                    unreachable!();
                };
                let s_t = SliceType::new(self.file, primary_target.index(), slice_type);
                if let Some(from) = base.maybe_saved_node_ref(i_s.db) {
                    let point = from.point();
                    if let Some(
                        specific @ (Specific::PartialDict
                        | Specific::PartialDefaultDict
                        | Specific::PartialDefaultDictWithList
                        | Specific::PartialDefaultDictWithSet),
                    ) = point.maybe_specific()
                    {
                        if !point.partial_flags().finished {
                            let value_t = value.as_type(i_s);
                            if specific == Specific::PartialDefaultDict {
                                let Some(ComplexPoint::TypeInstance(original_value)) = from
                                    .add_to_node_index(NAME_DEF_TO_DEFAULTDICT_DIFF)
                                    .complex()
                                else {
                                    unreachable!(
                                        "The defaultdict value type should always be defined"
                                    )
                                };
                                if !original_value
                                    .is_simple_same_type(self.i_s, &value_t)
                                    .bool()
                                {
                                    from.add_need_type_annotation_issue(i_s, specific);
                                    return;
                                }
                            }
                            let new_dict = new_class!(
                                match specific {
                                    Specific::PartialDict =>
                                        i_s.db.python_state.dict_node_ref().as_link(),
                                    _ => i_s.db.python_state.defaultdict_link(),
                                },
                                s_t.infer(i_s).as_type(i_s).avoid_implicit_literal(i_s.db),
                                value_t,
                            );
                            if new_dict.has_never_from_inference(self.i_s.db) {
                                from.finish_partial_with_annotation_needed(i_s);
                                return;
                            }
                            debug!(
                                r#"Infer dict assignment partial for "{}" as "{}""#,
                                primary_target.as_code(),
                                new_dict.format_short(i_s.db)
                            );
                            from.insert_type(new_dict);
                            return;
                        }
                    }
                }
                base.type_check_set_item(i_s, s_t, value);
                //self.narrow_primary_target_from_assignment(primary_target, &value.as_cow_type(self.i_s))
            }
            Target::Tuple(_) | Target::Starred(_) => unreachable!(),
        }
    }

    pub fn assign_any_to_target(&self, target: Target, n: NodeRef) {
        // Just assign targets in normal mode, so that we have at least assigned
        // something to these names.
        self.assign_targets(
            target,
            Inferred::new_any_from_error(),
            n,
            AssignKind::Normal,
        )
    }

    pub(super) fn assign_targets(
        &self,
        target: Target,
        value: Inferred,
        value_node_ref: NodeRef,
        assign_kind: AssignKind,
    ) {
        match target {
            Target::Tuple(targets) => FLOW_ANALYSIS.with(|fa| {
                let mut first_iter = true;
                for union_part in value
                    .as_cow_type(self.i_s)
                    .iter_with_unpacked_unions_and_maybe_include_never(self.i_s.db, true)
                {
                    if union_part == &self.i_s.db.python_state.str_type() {
                        value_node_ref.add_issue(self.i_s, IssueKind::UnpackingAStringIsDisallowed)
                    }
                    let value_iterator = union_part.iter(
                        self.i_s,
                        IterInfos::new(value_node_ref, &|issue| {
                            value_node_ref.add_issue(self.i_s, issue)
                        }),
                    );
                    match value_iterator {
                        IteratorContent::Union(iterators) => {
                            for it in iterators {
                                self.assign_tuple_target(
                                    targets.clone(),
                                    it,
                                    value_node_ref,
                                    assign_kind,
                                );
                                if first_iter {
                                    first_iter = false;
                                    fa.start_accumulating_types();
                                }
                            }
                        }
                        _ => {
                            self.assign_tuple_target(
                                targets.clone(),
                                value_iterator,
                                value_node_ref,
                                assign_kind,
                            );
                            if first_iter {
                                first_iter = false;
                                fa.start_accumulating_types();
                            }
                        }
                    }
                }
                if !first_iter {
                    fa.stop_accumulating_types()
                }
            }),
            Target::Starred(starred) => {
                // This is always invalid, just set it to Any. Issues were added before.
                self.assign_targets(
                    starred.as_target(),
                    Inferred::new_list_of(self.i_s.db, Type::Any(AnyCause::FromError)),
                    value_node_ref,
                    assign_kind,
                );
            }
            _ => {
                self.assign_single_target(
                    target,
                    value_node_ref,
                    &value,
                    assign_kind,
                    |index, value| {
                        // Since it's possible that we are assigning unions to tuple/star targets, we
                        // iterate over the different possibilities and end up with name definitions
                        // that are already set. In those cases we use the "old" types and merge them.
                        // In Mypy that is called "accumulate_type_assignments".
                        NodeRef::new(self.file, index).accumulate_types(self.i_s, value);
                    },
                )
            }
        };
    }

    fn assign_tuple_target(
        &self,
        targets: TargetIterator,
        mut value_iterator: IteratorContent,
        value_node_ref: NodeRef,
        assign_kind: AssignKind,
    ) {
        let (star_count, expected_lens) = targets_len_infos(targets.clone());
        let mut had_issue = false;
        // 1. Check length mismatch to maybe abort
        if let Some(actual_lens) = value_iterator.len_infos() {
            use TupleLenInfos::*;
            had_issue = match (expected_lens, actual_lens) {
                (FixedLen(expected), FixedLen(actual)) if actual != expected => {
                    value_node_ref.add_issue(
                        self.i_s,
                        if actual < expected {
                            IssueKind::TooFewValuesToUnpack { actual, expected }
                        } else {
                            IssueKind::TooManyValuesToUnpack { actual, expected }
                        },
                    );
                    true
                }
                (WithStar { before, after }, FixedLen(actual)) if before + after > actual => {
                    value_node_ref.add_issue(
                        self.i_s,
                        IssueKind::TooFewValuesToUnpack {
                            actual,
                            expected: before + after,
                        },
                    );
                    true
                }
                (
                    WithStar {
                        before: before1,
                        after: after1,
                    },
                    WithStar {
                        before: before2,
                        after: after2,
                    },
                ) if before1 > before2 || after1 > after2 => {
                    value_node_ref.add_issue(
                        self.i_s,
                        IssueKind::TooManyAssignmentTargetsForVariadicUnpack,
                    );
                    true
                }
                (FixedLen(expected), WithStar { before, after }) => {
                    value_node_ref.add_issue(
                        self.i_s,
                        IssueKind::VariadicTupleUnpackingRequiresStarTarget,
                    );
                    true
                }
                _ => false,
            };
        }
        // 2. Check for stuff like *x, *y = ...
        if star_count > 1 {
            had_issue = true;
            let star_target = targets
                .clone()
                .find_map(|target| match target {
                    Target::Starred(t) => Some(t),
                    _ => None,
                })
                .unwrap();
            self.add_issue(
                star_target.index(),
                IssueKind::MultipleStarredExpressionsInAssignment,
            );
        }

        // 3. Abort if necessary.
        if had_issue {
            for target in targets {
                self.assign_any_to_target(target, value_node_ref);
            }
            return;
        }

        // 4. Actually assign targets, now that everything is fine
        for target in targets {
            if let Target::Starred(star_target) = target {
                let TupleLenInfos::WithStar { after, .. } = expected_lens else {
                    unreachable!()
                };
                let new_target = star_target.as_target();
                let expect_tuple = matches!(new_target, Target::Tuple(_));
                let (is_empty, mut value) =
                    value_iterator.unpack_starred(self.i_s, after, expect_tuple);
                if is_empty
                    && !expect_tuple
                    && self.infer_target(star_target.as_target(), false).is_some()
                {
                    // The type is already defined, just use any here, because the
                    // list really can be anything.
                    value = Inferred::from_type(new_class!(
                        self.i_s.db.python_state.list_node_ref().as_link(),
                        Type::Any(AnyCause::Todo),
                    ))
                }
                self.assign_targets(new_target, value, value_node_ref, assign_kind);
            } else {
                let value = value_iterator.unpack_next();
                self.assign_targets(target, value, value_node_ref, assign_kind);
            }
        }
    }

    pub fn infer_star_expressions(
        &self,
        exprs: StarExpressions,
        result_context: &mut ResultContext,
    ) -> Inferred {
        match exprs.unpack() {
            StarExpressionContent::Expression(expr) => {
                if true {
                    self.infer_expression_with_context(expr, result_context)
                } else {
                    // TODO use this somewhere
                    /*
                    debug!("Found {} type vars in {}", type_vars.len(), expr.as_code());
                    ComplexPoint::TypeAlias(Box::new(TypeAlias {
                        type_vars: type_vars.into_boxed_slice(),
                        type_: self.infer_expression(expr).as_type(self.i_s),
                    }))
                    */
                    todo!()
                }
            }
            StarExpressionContent::StarExpression(expr) => {
                self.add_issue(expr.index(), IssueKind::StarredExpressionOnlyNoTarget);
                Inferred::new_any_from_error()
            }
            StarExpressionContent::Tuple(tuple) => self
                .infer_tuple_iterator(tuple.iter(), result_context)
                .save_redirect(self.i_s, self.file, tuple.index()),
        }
    }

    pub fn infer_named_expression(&self, named_expr: NamedExpression) -> Inferred {
        self.infer_named_expression_with_context(named_expr, &mut ResultContext::Unknown)
    }

    pub fn infer_named_expression_with_context(
        &self,
        named_expr: NamedExpression,
        result_context: &mut ResultContext,
    ) -> Inferred {
        match named_expr.unpack() {
            NamedExpressionContent::Expression(expr) => {
                self.infer_expression_with_context(named_expr.expression(), result_context)
            }
            NamedExpressionContent::Walrus(walrus) => {
                self.infer_walrus(walrus, Some(result_context))
            }
        }
    }

    pub fn infer_walrus(
        &self,
        walrus: Walrus,
        result_context: Option<&mut ResultContext>,
    ) -> Inferred {
        let (name_def, expr) = walrus.unpack();
        if let Some(inferred) = self.check_point_cache(name_def.index()) {
            return inferred;
        }

        let inf = if let Some(inf) = self.infer_name_target(name_def, false) {
            self.infer_expression_with_context(
                expr,
                &mut ResultContext::new_known(&inf.as_cow_type(self.i_s)),
            )
        } else if let Some(result_context) = result_context {
            self.infer_expression_with_context(expr, result_context)
        } else {
            self.infer_expression(expr)
        };

        self.save_walrus(name_def, inf)
    }

    pub(crate) fn check_for_redefinition(
        &self,
        name_def: NodeRef,
        add_issue: impl FnOnce(IssueKind),
    ) {
        let name_index = name_def.node_index + NAME_DEF_TO_NAME_DIFFERENCE;
        debug_assert_eq!(name_def.file_index(), self.file.file_index);
        if let Some(first) = first_defined_name_of_multi_def(self.file, name_index) {
            if name_def.as_code() != "_" {
                self.add_redefinition_issue(first, name_def.as_code(), false, add_issue)
            }
        }
    }

    fn add_redefinition_issue(
        &self,
        first_index_of_definition: NodeIndex,
        name: &str,
        is_self_attribute: bool,
        add_issue: impl FnOnce(IssueKind),
    ) {
        let first_ref = NodeRef::new(self.file, first_index_of_definition);
        let mut line = first_ref.line();
        let i_s = self.i_s;
        if i_s.db.project.settings.mypy_compatible {
            // Mypy uses the line of the first decorator as the definition line. This feels
            // weird, because the name is what matters, so in our implementation we use a
            // different line.
            if let Some(decorated) = first_ref
                .maybe_name_of_function()
                .and_then(|func| func.maybe_decorated())
            {
                line = NodeRef::new(self.file, decorated.index()).line();
            }
        }
        let first_name_def = first_ref.as_name().name_def().unwrap();
        let suffix = match first_name_def.maybe_import() {
            Some(import_parent) => {
                let mut s = "(possibly by an import)";
                if matches!(
                    self.infer_name_def(first_name_def)
                        .as_cow_type(i_s)
                        .as_ref(),
                    Type::Module(_)
                ) {
                    s = "(by an import)";
                }
                Box::from(s)
            }
            None => format!("on line {line}").into(),
        };
        add_issue(IssueKind::Redefinition {
            name: name.into(),
            suffix,
            is_self_attribute,
        })
    }

    fn follow_and_maybe_saved(&self, name_index: NodeIndex) -> Option<NodeRef<'db>> {
        if std::cfg!(debug_assertions) {
            // Make sure it's a NameDef
            let ref_ = NodeRef::new(self.file, name_index - NAME_DEF_TO_NAME_DIFFERENCE);
            ref_.as_name_def();
        }
        self.check_point_cache(name_index - NAME_DEF_TO_NAME_DIFFERENCE)
            .and_then(|inf| inf.maybe_saved_node_ref(self.i_s.db))
    }

    pub fn save_walrus(&self, name_def: NameDef, inf: Inferred) -> Inferred {
        let from = NodeRef::new(self.file, name_def.index());
        let inf = inf.avoid_implicit_literal(self.i_s);
        self.assign_to_name_def_simple(name_def, from, &inf, AssignKind::Normal);
        self.check_point_cache(name_def.index()).unwrap_or(inf)
    }

    pub fn infer_expression(&self, expr: Expression) -> Inferred {
        self.infer_expression_with_context(expr, &mut ResultContext::Unknown)
    }

    check_point_cache_with!(
        pub infer_expression_with_context,
        Self::infer_expression_without_cache,
        Expression,
        result_context
    );
    pub fn infer_expression_without_cache(
        &self,
        expr: Expression,
        result_context: &mut ResultContext,
    ) -> Inferred {
        let inferred = match expr.unpack() {
            ExpressionContent::ExpressionPart(n) => {
                self.infer_expression_part_with_context(n, result_context)
            }
            ExpressionContent::Lambda(l) => self.infer_lambda(l, result_context),
            ExpressionContent::Ternary(t) => self.flow_analysis_for_ternary(t, result_context),
        };
        // We only save the result if nothing is there, yet. It could be that we pass this function
        // twice, when for example a class F(List[X]) is created, where X = F and X is defined
        // before F, this might happen.
        let inferred = inferred.maybe_save_redirect(self.i_s, self.file, expr.index(), true);
        if self.flags().disallow_any_expr && !self.file.is_stub() {
            let t = inferred.as_cow_type(self.i_s);
            if t.has_any(self.i_s) {
                self.add_issue(
                    expr.index(),
                    IssueKind::DisallowedAnyExpr {
                        type_: t.format_short(self.i_s.db),
                    },
                );
            }
        }
        inferred
    }

    pub fn infer_expression_part(&self, node: ExpressionPart) -> Inferred {
        self.infer_expression_part_with_context(node, &mut ResultContext::Unknown)
    }

    pub fn infer_expression_part_with_context(
        &self,
        node: ExpressionPart,
        result_context: &mut ResultContext,
    ) -> Inferred {
        match node {
            ExpressionPart::Atom(atom) => self.infer_atom(atom, result_context),
            ExpressionPart::Primary(primary) => self.infer_primary(primary, result_context),
            ExpressionPart::Sum(sum) => self.infer_operation(sum.as_operation()),
            ExpressionPart::Term(term) => {
                let op = term.as_operation();
                // Mypy special cases the case [...] * n where n is an int (see check_list_multiply
                // in mypy)
                if op.infos.operand == "*" {
                    if let ExpressionPart::Atom(atom) = op.left {
                        if matches!(atom.unpack(), AtomContent::List(_))
                            && self
                                .infer_expression_part(op.right)
                                .as_cow_type(self.i_s)
                                .is_simple_sub_type_of(
                                    self.i_s,
                                    &self.i_s.db.python_state.int_type(),
                                )
                                .bool()
                        {
                            return self.infer_atom(atom, result_context);
                        }
                    }
                }
                self.infer_operation(op)
            }
            ExpressionPart::Power(power) => self.infer_operation(power.as_operation()),
            ExpressionPart::ShiftExpr(shift) => self.infer_operation(shift.as_operation()),
            ExpressionPart::BitwiseOr(or) => self.infer_operation(or.as_operation()),
            ExpressionPart::BitwiseAnd(and) => self.infer_operation(and.as_operation()),
            ExpressionPart::BitwiseXor(xor) => self.infer_operation(xor.as_operation()),
            ExpressionPart::Disjunction(or) => {
                self.flow_analysis_for_disjunction(or, result_context)
            }
            ExpressionPart::Conjunction(and) => self.flow_analysis_for_conjunction(and),
            ExpressionPart::Inversion(inversion) => {
                let expr = inversion.expression();
                self.infer_expression_part(expr);
                Inferred::from_type(self.i_s.db.python_state.bool_type())
            }
            ExpressionPart::Comparisons(cmps) => Inferred::gather_base_types(self.i_s, |gather| {
                let mut left_inf = self.infer_expression_part(cmps.iter().next().unwrap().left());
                for cmp in cmps.iter() {
                    let right_inf = self.infer_expression_part(cmp.right());
                    gather(self.infer_comparison_part(cmp, left_inf, &right_inf));
                    left_inf = right_inf;
                }
            }),
            ExpressionPart::Factor(f) => {
                let (operand, right) = f.unpack();
                let inf = self.infer_expression_part(right);
                if operand.as_code() != "~" {
                    match inf.maybe_literal(self.i_s.db) {
                        UnionValue::Single(literal) => {
                            if let LiteralKind::Int(i) = &literal.kind {
                                if operand.as_code() == "+" {
                                    // Rust weirdness: Why do we need to clone here?
                                    return inf.clone();
                                }
                                return Inferred::from_type(Type::Literal(Literal {
                                    kind: LiteralKind::Int(-i),
                                    implicit: true,
                                }));
                            }
                        }
                        UnionValue::Multiple(literals) => todo!(),
                        UnionValue::Any => (),
                    }
                }
                let method_name = match operand.as_code() {
                    "-" => "__neg__",
                    "+" => "__pos__",
                    "~" => "__invert__",
                    _ => unreachable!(),
                };
                let node_ref = NodeRef::new(self.file, f.index());
                inf.type_lookup_and_execute(
                    self.i_s,
                    node_ref.file,
                    method_name,
                    &NoArgs::new(node_ref),
                    &|type_| {
                        let operand = match operand.as_code() {
                            "~" => "~",
                            "-" => "unary -",
                            "+" => "unary +",
                            _ => unreachable!(),
                        };
                        let got = type_.format_short(self.i_s.db);
                        node_ref.add_issue(
                            self.i_s,
                            IssueKind::UnsupportedOperandForUnary { operand, got },
                        )
                    },
                )
            }
            ExpressionPart::AwaitPrimary(await_node) => {
                let from = NodeRef::new(self.file, await_node.index());
                if let Some(function) = self.i_s.current_function() {
                    if function.is_async() {
                        await_(
                            self.i_s,
                            self.infer_expression_part_with_context(
                                await_node.primary(),
                                &mut match result_context {
                                    ResultContext::ExpectUnused => ResultContext::ExpectUnused,
                                    _ => ResultContext::Unknown,
                                },
                            ),
                            from,
                            "\"await\"",
                            result_context.expect_not_none(self.i_s),
                        )
                    } else {
                        from.add_issue(self.i_s, IssueKind::AwaitOutsideCoroutine);
                        Inferred::new_any_from_error()
                    }
                } else {
                    from.add_issue(self.i_s, IssueKind::AwaitOutsideFunction);
                    Inferred::new_any_from_error()
                }
            }
        }
    }

    pub fn infer_comparison_part(
        &self,
        cmp: ComparisonContent,
        left_inf: Inferred,
        right_inf: &Inferred,
    ) -> Inferred {
        let needs_strict_equality_error = || {
            if !self.flags().strict_equality {
                return None;
            }
            // Now check --strict-equality
            let left_t = left_inf.as_cow_type(self.i_s);
            let right_t = right_inf.as_cow_type(self.i_s);
            (!self.is_strict_equality_comparison(&left_t, &right_t))
                .then(|| format_got_expected(self.i_s.db, &left_t, &right_t))
        };
        match cmp {
            ComparisonContent::Equals(l, op, r) | ComparisonContent::NotEquals(l, op, r) => {
                if let Some(formatted_err) = needs_strict_equality_error() {
                    self.file.add_issue(
                        self.i_s,
                        Issue {
                            kind: IssueKind::NonOverlappingEqualityCheck {
                                left_type: formatted_err.got,
                                right_type: formatted_err.expected,
                            },
                            start_position: l.start(),
                            end_position: r.end(),
                        },
                    )
                }
                let from = NodeRef::new(self.file, op.index());
                left_inf.type_lookup_and_execute(
                    self.i_s,
                    from.file,
                    "__eq__",
                    &KnownArgs::new(right_inf, from),
                    &|_| {
                        debug!(
                            "__eq__ is normally accessible, but might not be \
                         for protocols and other things: {}",
                            left_inf.format_short(self.i_s)
                        )
                    },
                )
            }
            ComparisonContent::Is(l, op, r) | ComparisonContent::IsNot(l, op, r) => {
                let from = NodeRef::new(self.file, op.index());
                if let Some(formatted_err) = needs_strict_equality_error() {
                    self.file.add_issue(
                        self.i_s,
                        Issue {
                            kind: IssueKind::NonOverlappingIdentityCheck {
                                left_type: formatted_err.got,
                                right_type: formatted_err.expected,
                            },
                            start_position: l.start(),
                            end_position: r.end(),
                        },
                    )
                }
                Inferred::from_type(self.i_s.db.python_state.bool_type())
            }
            ComparisonContent::In(l, op, r) | ComparisonContent::NotIn(l, op, r) => {
                let from = NodeRef::new(self.file, op.index());
                if self.flags().strict_equality {
                    // Now check --strict-equality

                    let overlaps_bytes_or_bytearray = |t: &Type| {
                        t.simple_overlaps(self.i_s, &self.i_s.db.python_state.bytes_type())
                            || t.simple_overlaps(
                                self.i_s,
                                &self.i_s.db.python_state.bytearray_type(),
                            )
                            || t.simple_overlaps(
                                self.i_s,
                                &self.i_s.db.python_state.memoryview_type(),
                            )
                    };
                    let element_t = left_inf.as_cow_type(self.i_s);
                    let right_t = right_inf.as_cow_type(self.i_s);
                    // bytes are a bit special, we just try to mimic Mypy here.
                    // b'a' == bytesarray(b'a') is fine.
                    if !(overlaps_bytes_or_bytearray(&element_t)
                        && overlaps_bytes_or_bytearray(&right_t))
                    {
                        if let Some(container_t) = right_t.container_types(self.i_s.db) {
                            if !self.is_strict_equality_comparison(&element_t, &container_t) {
                                let formatted =
                                    format_got_expected(self.i_s.db, &element_t, &container_t);
                                self.file.add_issue(
                                    self.i_s,
                                    Issue {
                                        kind: IssueKind::NonOverlappingContainsCheck {
                                            element_type: formatted.got,
                                            container_type: formatted.expected,
                                        },
                                        start_position: l.start(),
                                        end_position: r.end(),
                                    },
                                )
                            }
                        }
                    }
                }
                self.infer_in_operator(from, &left_inf, right_inf)
            }
            ComparisonContent::Ordering(op) => {
                self.infer_detailed_operation(op.index, op.infos, left_inf, right_inf)
            }
        }
    }

    fn is_strict_equality_comparison(&self, left_t: &Type, right_t: &Type) -> bool {
        debug_assert!(self.flags().strict_equality);
        // In mypy this is implemented as "def dangerous_comparison"

        // Mypy considers None in general to be fine.
        if matches!(left_t, Type::None)
            || matches!(right_t, Type::None)
            || has_custom_special_method(self.i_s, left_t, "__eq__")
            || has_custom_special_method(self.i_s, right_t, "__eq__")
        {
            return true;
        }

        let db = self.i_s.db;
        let left_t = left_t.remove_none(db);
        let right_t = right_t.remove_none(db);
        if let Some((c1, c2)) = left_t.maybe_class(db).zip(right_t.maybe_class(db)) {
            if c1.node_ref == c2.node_ref && c1.node_ref == db.python_state.list_node_ref() {
                return self.is_strict_equality_comparison(
                    &c1.nth_type_argument(db, 0),
                    &c2.nth_type_argument(db, 0),
                );
            }
            let is_bytes_like = |c: Class| {
                c.node_ref == db.python_state.bytes_node_ref()
                    || c.node_ref == db.python_state.bytearray_node_ref()
                    || c.node_ref == db.python_state.memoryview_node_ref()
            };
            if is_bytes_like(c1) && is_bytes_like(c2) {
                return true;
            }
            let mapping_link = db.python_state.mapping_link();
            if let Some(map1) = c1.class_in_mro(db, mapping_link) {
                if let Some(map2) = c2.class_in_mro(db, mapping_link) {
                    return self.is_strict_equality_comparison(
                        &map1.nth_type_argument(db, 0),
                        &map2.nth_type_argument(db, 0),
                    ) && self.is_strict_equality_comparison(
                        &map1.nth_type_argument(db, 1),
                        &map2.nth_type_argument(db, 1),
                    );
                }
            }
        }
        if let Type::Tuple(tup1) = left_t.as_ref() {
            if let Type::Tuple(tup2) = right_t.as_ref() {
                if let TupleArgs::ArbitraryLen(inner1) = &tup1.args {
                    if let TupleArgs::ArbitraryLen(inner2) = &tup2.args {
                        return self.is_strict_equality_comparison(inner1, inner2);
                    }
                }
            }
        }
        left_t.simple_overlaps(self.i_s, &right_t)
    }

    pub fn infer_in_operator(
        &self,
        from: NodeRef,
        left_inf: &Inferred,
        right_inf: &Inferred,
    ) -> Inferred {
        let mut had_union_member_passing = false;
        let i_s = self.i_s;
        right_inf.run_after_lookup_on_each_union_member(
            i_s,
            from.file,
            "__contains__",
            LookupKind::OnlyType,
            &|issue| todo!(),
            &mut |r_type, lookup_result| {
                if let Some(method) = lookup_result.lookup.into_maybe_inferred() {
                    for l_type in left_inf.as_cow_type(i_s).iter_with_unpacked_unions(i_s.db) {
                        let had_local_error = Cell::new(false);
                        method.execute_with_details(
                            i_s,
                            &KnownArgs::new(&Inferred::from_type(l_type.clone()), from),
                            &mut ResultContext::Unknown,
                            OnTypeError::new(&|i_s, _, _, types| {
                                had_local_error.set(true);
                            }),
                        );
                        if !had_local_error.get() {
                            had_union_member_passing = true;
                        }
                    }
                } else {
                    for l_type in left_inf.as_cow_type(i_s).iter_with_unpacked_unions(i_s.db) {
                        let match_ = r_type
                            .lookup(
                                i_s,
                                from.file_index(),
                                "__iter__",
                                LookupKind::OnlyType,
                                &mut ResultContext::Unknown,
                                &|issue| from.add_issue(i_s, issue),
                                &|_| {
                                    let right = right_inf.format_short(i_s);
                                    from.add_issue(i_s, IssueKind::UnsupportedIn { right })
                                },
                            )
                            .into_inferred()
                            .execute(i_s, &NoArgs::new(from))
                            .type_lookup_and_execute(
                                i_s,
                                from.file,
                                "__next__",
                                &NoArgs::new(from),
                                &|_| todo!(),
                            )
                            .as_cow_type(i_s)
                            .is_simple_super_type_of(i_s, l_type);
                        if match_.bool() {
                            had_union_member_passing = true;
                        }
                    }
                }
            },
        );
        if !had_union_member_passing
            && !matches!(right_inf.as_cow_type(i_s).as_ref(), Type::Never(_))
        {
            from.add_issue(
                i_s,
                IssueKind::UnsupportedOperand {
                    operand: Box::from("in"),
                    left: left_inf.format_short(i_s),
                    right: right_inf.format_short(i_s),
                },
            );
        }
        Inferred::from_type(self.i_s.db.python_state.bool_type())
    }

    fn infer_lambda(&self, lambda: Lambda, result_context: &mut ResultContext) -> Inferred {
        let check_defaults = || {
            let (params, expr) = lambda.unpack();
            for param in params {
                if let Some(default) = param.default() {
                    self.infer_expression(default);
                }
            }
        };
        let to_callable_param = |param: Param| CallableParam {
            type_: match param.kind() {
                ParamKind::PositionalOnly => {
                    ParamType::PositionalOnly(Type::Any(AnyCause::Unannotated))
                }
                ParamKind::PositionalOrKeyword => {
                    ParamType::PositionalOrKeyword(Type::Any(AnyCause::Unannotated))
                }
                ParamKind::KeywordOnly => ParamType::KeywordOnly(Type::Any(AnyCause::Unannotated)),
                ParamKind::Star => ParamType::Star(StarParamType::ArbitraryLen(Type::Any(
                    AnyCause::Unannotated,
                ))),
                ParamKind::StarStar => ParamType::StarStar(StarStarParamType::ValueType(
                    Type::Any(AnyCause::Unannotated),
                )),
            },
            name: Some(
                StringSlice::from_name(self.file.file_index, param.name_def().name()).into(),
            ),
            has_default: param.default().is_some(),
        };
        result_context
            .with_type_if_exists_and_replace_type_var_likes(self.i_s, |type_| {
                if let Type::Callable(c) = type_ {
                    let i_s = self.i_s.with_lambda_callable(c);
                    let (params, expr) = lambda.unpack();
                    let inference = self.file.inference(&i_s);
                    check_defaults();
                    let result = inference.flow_analysis_for_lambda_body(
                        expr,
                        // This cannot be ResultContext::Known, because that would imply that a
                        // value is expected and there would be an error:
                        //     `does not return a value (it only ever returns None`
                        &mut ResultContext::KnownLambdaReturn(&c.return_type),
                    );
                    let mut c = (**c).clone();
                    c.guard = None;

                    let c_params = params.clone().map(to_callable_param);
                    match &mut c.params {
                        CallableParams::Simple(expected_params) => {
                            let c_params: Vec<_> = c_params.collect();
                            if matches_simple_params(
                                self.i_s,
                                &mut Matcher::default(),
                                expected_params.iter(),
                                c_params.iter().peekable(),
                                Variance::Invariant,
                            )
                            .bool()
                            {
                                if expected_params
                                    .iter()
                                    .any(|p| matches!(p.type_, ParamType::KeywordOnly(_)))
                                {
                                    // In the case of keyword only arguments we can sometimes
                                    // return a more general lambda.
                                    move_lambda_context_keyword_to_positional_or_keyword(
                                        i_s.db,
                                        expected_params,
                                        params,
                                    )
                                }
                            } else {
                                self.add_issue(lambda.index(), IssueKind::CannotInferLambdaParams);
                                c.params = CallableParams::new_simple(c_params.into());
                            }
                        }
                        _ => {
                            c.params = CallableParams::new_simple(c_params.collect());
                        }
                    }
                    c.return_type = result.as_type(&i_s);
                    debug!(
                        "Inferred lambda from context as '{}'",
                        c.format(&FormatData::new_short(i_s.db))
                    );
                    Some(Inferred::from_type(Type::Callable(Rc::new(c))))
                } else {
                    None
                }
            })
            .flatten()
            .unwrap_or_else(|| {
                let (params, expr) = lambda.unpack();
                check_defaults();
                let result =
                    self.flow_analysis_for_lambda_body(expr, &mut ResultContext::ExpectUnused);
                let c = CallableContent::new_simple(
                    None,
                    None,
                    PointLink::new(self.file.file_index, lambda.index()),
                    self.i_s.db.python_state.empty_type_var_likes.clone(),
                    CallableParams::new_simple(params.map(to_callable_param).collect()),
                    result.as_type(self.i_s),
                );
                Inferred::from_type(Type::Callable(Rc::new(c)))
            })
    }

    fn infer_operation(&self, op: Operation) -> Inferred {
        let left = self.infer_expression_part(op.left);
        let right = self.infer_expression_part(op.right);
        self.infer_detailed_operation(op.index, op.infos, left, &right)
    }

    fn infer_detailed_operation(
        &self,
        error_index: NodeIndex,
        op_infos: OpInfos,
        left: Inferred,
        right: &Inferred,
    ) -> Inferred {
        enum LookupStrategy {
            ShortCircuit,
            NormalThenReverse,
            ReverseThenNormal,
        }

        let from = NodeRef::new(self.file, error_index);
        let mut had_error = false;
        let i_s = self.i_s;
        let result = Inferred::gather_simplified_union(i_s, |add_to_union| {
            left.run_after_lookup_on_each_union_member(
                i_s,
                from.file,
                op_infos.magic_method,
                LookupKind::OnlyType,
                &|issue| todo!(),
                &mut |l_type, lookup_result| {
                    let left_op_method = lookup_result.lookup.into_maybe_inferred();
                    for r_type in right.as_cow_type(i_s).iter_with_unpacked_unions(i_s.db) {
                        if let Type::Any(cause) = r_type {
                            return add_to_union(Inferred::new_any(*cause));
                        }
                        let instance;
                        let (r_defined_in, right_op_method) = match r_type {
                            Type::Class(r_class) => {
                                instance = r_class.class(i_s.db).instance();
                                let l = instance.lookup_with_details(
                                    i_s,
                                    |issue| from.add_issue(i_s, issue),
                                    op_infos.reverse_magic_method,
                                    LookupKind::OnlyType,
                                );
                                (Some(l.class), l.lookup.into_maybe_inferred())
                            }
                            _ => (
                                None,
                                r_type
                                    .lookup(
                                        i_s,
                                        from.file_index(),
                                        op_infos.reverse_magic_method,
                                        LookupKind::OnlyType,
                                        &mut ResultContext::Unknown,
                                        &|_| todo!(),
                                        &|_| {},
                                    )
                                    .into_maybe_inferred(),
                            ),
                        };

                        let l_defined_in = Some(&lookup_result.class);
                        let get_strategy = || {
                            // Check for shortcuts first (in Mypy it's called
                            // `op_methods_that_shortcut`)
                            if op_infos.shortcut_when_same_type {
                                if let Some(left_instance) = l_type.maybe_class(i_s.db) {
                                    if let Some(right_instance) = r_type.maybe_class(i_s.db) {
                                        if left_instance.node_ref == right_instance.node_ref {
                                            return LookupStrategy::ShortCircuit;
                                        }
                                    }
                                }
                            }
                            // If right is a sub type of left, Python and Mypy execute right first
                            if r_type.is_simple_sub_type_of(i_s, l_type).bool() {
                                if let Some(TypeOrClass::Class(l_class)) = l_defined_in {
                                    if let Some(TypeOrClass::Class(r_class)) = r_defined_in {
                                        if l_class.node_ref != r_class.node_ref {
                                            return LookupStrategy::ReverseThenNormal;
                                        }
                                    }
                                }
                            }
                            LookupStrategy::NormalThenReverse
                        };
                        let strategy = get_strategy();

                        let mut result_backup = None;
                        let mut run = |first: &Inferred, second_type: &Type| {
                            let second = Inferred::from_type(second_type.clone());
                            let local_error = Cell::new(false);
                            let result = first.execute_with_details(
                                i_s,
                                &KnownArgs::new(&second, from),
                                &mut ResultContext::Unknown,
                                OnTypeError::with_overload_mismatch(
                                    &|_, _, _, _| local_error.set(true),
                                    Some(&|| local_error.set(true)),
                                ),
                            );
                            if local_error.get() {
                                if result_backup.is_none() {
                                    result_backup = Some(result);
                                } else {
                                    // If this is called multiple times we always return Any,
                                    // because it's unclear what type there should be and an error
                                    // has been raised.
                                    result_backup = Some(Inferred::new_any_from_error())
                                }
                                None
                            } else {
                                Some(result)
                            }
                        };

                        let result = match strategy {
                            LookupStrategy::ShortCircuit => {
                                left_op_method.as_ref().and_then(|left| run(left, r_type))
                            }
                            LookupStrategy::NormalThenReverse => left_op_method
                                .as_ref()
                                .and_then(|left| run(left, r_type))
                                .or_else(|| {
                                    right_op_method
                                        .as_ref()
                                        .and_then(|right| run(right, l_type))
                                }),
                            LookupStrategy::ReverseThenNormal => right_op_method
                                .as_ref()
                                .and_then(|right| run(right, l_type))
                                .or_else(|| {
                                    left_op_method.as_ref().and_then(|left| run(left, r_type))
                                }),
                        };
                        add_to_union(result.unwrap_or_else(|| {
                            had_error = true;
                            let issue = if left_op_method.is_none()
                                && (right_op_method.is_none()
                                    || matches!(strategy, LookupStrategy::ShortCircuit))
                            {
                                IssueKind::UnsupportedLeftOperand {
                                    operand: Box::from(op_infos.operand),
                                    left: l_type.format_short(i_s.db),
                                }
                            } else {
                                IssueKind::UnsupportedOperand {
                                    operand: Box::from(op_infos.operand),
                                    left: l_type.format_short(i_s.db),
                                    right: r_type.format_short(i_s.db),
                                }
                            };
                            from.add_issue(i_s, issue);
                            result_backup.unwrap_or_else(Inferred::new_any_from_error)
                        }))
                    }
                },
            )
        });
        if had_error {
            let note = match (left.is_union_like(self.i_s), right.is_union_like(self.i_s)) {
                (false, false) => return result,
                (true, false) => {
                    format!("Left operand is of type {:?}", left.format_short(self.i_s),).into()
                }
                (false, true) => format!(
                    "Right operand is of type {:?}",
                    right.format_short(self.i_s),
                )
                .into(),
                (true, true) => Box::from("Both left and right operands are unions"),
            };
            from.add_issue(self.i_s, IssueKind::Note(note));
        }
        debug!(
            "Operation between {} and {} results in {}",
            left.format_short(i_s),
            right.format_short(i_s),
            result.format_short(i_s)
        );
        result
    }

    fn infer_potential_partial_base(
        &self,
        primary_method: Primary,
        maybe_defaultdict: bool,
    ) -> Option<NodeRef> {
        match primary_method.first() {
            PrimaryOrAtom::Primary(prim) => {
                let index = prim.index();
                if self.file.points.get(index).calculated() {
                    // This means that we have already tried so return.
                    return None;
                }
                match prim.second() {
                    PrimaryContent::Attribute(attr) => {
                        // Only care about very specific cases here.
                        if !matches!(prim.first(), PrimaryOrAtom::Atom(_)) {
                            return None;
                        }
                        self.infer_primary(prim, &mut ResultContext::Unknown)
                            .save_redirect(self.i_s, self.file, index)
                            .maybe_saved_node_ref(self.i_s.db)
                    }
                    PrimaryContent::GetItem(getitem) => {
                        if maybe_defaultdict {
                            // This is for defaultdicts
                            return self.infer_potential_partial_base(prim, false);
                        }
                        None
                    }
                    PrimaryContent::Execution(_) => None,
                }
            }
            PrimaryOrAtom::Atom(atom) => self
                .infer_atom(atom, &mut ResultContext::Unknown)
                .maybe_saved_node_ref(self.i_s.db),
        }
    }

    fn try_to_infer_partial_from_primary(&self, primary: Primary) {
        let PrimaryContent::Execution(execution) = primary.second() else {
            return;
        };
        let PrimaryOrAtom::Primary(primary_method) = primary.first() else {
            return;
        };
        let PrimaryContent::Attribute(method_name) = primary_method.second() else {
            return;
        };
        let i_s = self.i_s;
        let Some(base) = self.infer_potential_partial_base(primary_method, true) else {
            return;
        };
        let first_arg_as_t = || {
            let args = SimpleArgs::new(*i_s, self.file, primary.index(), execution);
            let arg = args.maybe_single_positional_arg(i_s, &mut ResultContext::Unknown)?;
            Some(arg.as_type(i_s).avoid_implicit_literal(i_s.db))
        };
        let save_partial = |resolved_partial: Type| {
            let point = base.point();
            if point.kind() != PointKind::Specific {
                // This is a nested partial like:
                //
                //     arr = []
                //     arr.append(arr.append(1))
                //
                return None;
            }
            if point.partial_flags().finished {
                debug!(r#"Partial "{}" was already finished"#, primary.as_code());
                return None;
            }
            if resolved_partial.has_never_from_inference(self.i_s.db) {
                base.finish_partial_with_annotation_needed(i_s);
                return Some(());
            }
            debug!(
                r#"Infer partial for "{}" as "{}""#,
                primary.as_code(),
                resolved_partial.format_short(i_s.db)
            );
            base.insert_type(resolved_partial);
            Some(())
        };
        let find_container_types = |unwrap_from_iterable| {
            let mut t = first_arg_as_t()?;
            if unwrap_from_iterable && !t.is_any() {
                t = t.mro(i_s.db).find_map(|(_, type_or_class)| {
                    if let TypeOrClass::Class(maybe_iterable_cls) = type_or_class {
                        if maybe_iterable_cls.node_ref == i_s.db.python_state.iterable_node_ref() {
                            return Some(maybe_iterable_cls.nth_type_argument(i_s.db, 0));
                        }
                    }
                    None
                })?;
            }
            Some(t)
        };
        let try_to_save = |partial_class_link, unwrap_from_iterable| {
            let t = find_container_types(unwrap_from_iterable)?;
            save_partial(new_class!(partial_class_link, t))
        };
        let try_to_save_defaultdict = |container_partial_link, unwrap_from_iterable| {
            let t = find_container_types(unwrap_from_iterable)?;
            save_partial(new_class!(
                i_s.db.python_state.defaultdict_link(),
                Type::Any(AnyCause::Todo),
                new_class!(container_partial_link, t)
            ))
        };
        match base.point().maybe_specific() {
            Some(Specific::PartialList) => match method_name.as_code() {
                "append" => {
                    try_to_save(i_s.db.python_state.list_node_ref().as_link(), false);
                }
                "extend" => {
                    try_to_save(i_s.db.python_state.list_node_ref().as_link(), true);
                }
                _ => (),
            },
            Some(Specific::PartialDict) => match method_name.as_code() {
                "update" => {
                    let Some(t) = first_arg_as_t() else { return };
                    let dct_node_ref = i_s.db.python_state.dict_node_ref();
                    if t.is_any() {
                        save_partial(new_class!(dct_node_ref.as_link(), t));
                    } else if t
                        .maybe_class(i_s.db)
                        .is_some_and(|c| c.node_ref == dct_node_ref)
                    {
                        save_partial(t);
                    }
                }
                _ => (),
            },
            Some(Specific::PartialSet) => match method_name.as_code() {
                "add" | "discard" => {
                    try_to_save(i_s.db.python_state.set_node_ref().as_link(), false);
                }
                "update" => {
                    try_to_save(i_s.db.python_state.set_node_ref().as_link(), true);
                }
                _ => (),
            },
            Some(Specific::PartialDefaultDictWithList) => match method_name.as_code() {
                "append" => {
                    let t = find_container_types(false);
                    try_to_save_defaultdict(i_s.db.python_state.list_node_ref().as_link(), false);
                }
                "extend" => {
                    try_to_save_defaultdict(i_s.db.python_state.list_node_ref().as_link(), true);
                }
                _ => (),
            },
            Some(Specific::PartialDefaultDictWithSet) => match method_name.as_code() {
                _ => todo!(),
            },
            _ => (),
        };
    }

    // Primary is not saved by this function, but can be saved by other stuff and to avoid
    // re-executing, we check the point cache here.
    check_point_cache_with!(pub infer_primary, Self::_infer_primary, Primary, result_context);
    fn _infer_primary(&self, primary: Primary, result_context: &mut ResultContext) -> Inferred {
        if let Some(inf) = self.maybe_lookup_narrowed_primary(primary) {
            return inf;
        }
        self.try_to_infer_partial_from_primary(primary);
        let base = self.infer_primary_or_atom(primary.first());
        let result = self.infer_primary_or_primary_t_content(
            &base,
            primary.index(),
            primary.second(),
            false,
            result_context,
        );
        /*
         * TODO reenable this? see test testNewAnalyzerAliasToNotReadyNestedClass2
        debug!(
            "Infer primary {} as {}",
            primary.short_debug(),
            result.format_short(self.i_s)
        );
        */
        result
    }

    pub(super) fn infer_primary_or_primary_t_content(
        &self,
        base: &Inferred,
        node_index: NodeIndex,
        second: PrimaryContent,
        is_target: bool,
        result_context: &mut ResultContext,
    ) -> Inferred {
        let node_ref = NodeRef::new(self.file, node_index);
        match second {
            PrimaryContent::Attribute(name) => {
                debug!("Lookup {}.{}", base.format_short(self.i_s), name.as_str());
                base.lookup_with_result_context(
                    self.i_s,
                    node_ref,
                    name.as_str(),
                    LookupKind::Normal,
                    result_context,
                )
                .save_name(
                    self.i_s,
                    self.file,
                    if is_target {
                        // If it's a name def it might be something like self.foo = 1, which should not
                        // be overwritten.
                        if let Some(name_def) = name.name_def() {
                            name_def.index()
                        } else {
                            name.index()
                        }
                    } else {
                        name.index()
                    },
                )
                .unwrap_or_else(Inferred::new_any_from_error)
            }
            PrimaryContent::Execution(details) => {
                let f = self.file;
                let args = SimpleArgs::new(*self.i_s, f, node_index, details);
                base.execute_with_details(
                    self.i_s,
                    &args,
                    result_context,
                    OnTypeError::new(&on_argument_type_error),
                )
            }
            PrimaryContent::GetItem(slice_type) => {
                let f = self.file;
                // TODO enable this debug
                //debug!("Get Item on {}", base.format_short(self.i_s));
                base.get_item(
                    self.i_s,
                    &SliceType::new(f, node_index, slice_type),
                    result_context,
                )
            }
        }
    }

    pub fn infer_primary_or_atom(&self, p: PrimaryOrAtom) -> Inferred {
        match p {
            PrimaryOrAtom::Primary(primary) => {
                self.infer_primary(primary, &mut ResultContext::Unknown)
            }
            PrimaryOrAtom::Atom(atom) => self.infer_atom(atom, &mut ResultContext::Unknown),
        }
    }

    check_point_cache_with!(pub infer_atom, Self::_infer_atom, Atom, result_context);
    fn _infer_atom(&self, atom: Atom, result_context: &mut ResultContext) -> Inferred {
        let i_s = self.i_s;
        let check_literal = |result_context: &ResultContext, i_s, index, literal| {
            let specific = match result_context.could_be_a_literal(i_s) {
                CouldBeALiteral::Yes { implicit: false } => {
                    let mut t = specific_to_type(
                        i_s,
                        NodeRef::new(self.file, index).to_db_lifetime(i_s.db),
                        literal,
                    )
                    .into_owned();
                    let Type::Literal(literal) = &mut t else {
                        unreachable!()
                    };
                    literal.implicit = false;
                    return Inferred::from_type(t).save_redirect(i_s, self.file, index);
                }
                _ => literal,
            };
            let point = Point::new_specific(specific, Locality::Todo);
            Inferred::new_and_save(self.file, index, point)
        };

        use AtomContent::*;
        let specific = match atom.unpack() {
            Name(n) => return self.infer_name_reference(n),
            Int(i) => match self.parse_int(i, result_context) {
                Some(parsed) => {
                    return check_literal(result_context, i_s, i.index(), Specific::IntLiteral);
                }
                None => Specific::Int,
            },
            Float(_) => Specific::Float,
            Complex(_) => Specific::Complex,
            Strings(s_o_b) => {
                for string in s_o_b.iter() {
                    if let StringType::FString(f) = string {
                        self.calc_fstring_diagnostics(f)
                    }
                }
                if let Some(s) = s_o_b.maybe_single_string_literal() {
                    return check_literal(result_context, i_s, s.index(), Specific::StringLiteral);
                } else {
                    Specific::String
                }
            }
            Bytes(b) => {
                if let Some(b) = b.maybe_single_bytes_literal() {
                    return check_literal(result_context, i_s, b.index(), Specific::BytesLiteral);
                } else {
                    Specific::Bytes
                }
            }
            NoneLiteral => Specific::None,
            Bool(b) => return check_literal(result_context, i_s, b.index(), Specific::BoolLiteral),
            Ellipsis => Specific::Ellipsis,
            List(list) => {
                if let Some(result) = self.infer_list_or_set_literal_from_context(
                    list.unpack(),
                    result_context,
                    i_s.db.python_state.list_node_ref(),
                ) {
                    return result.save_redirect(i_s, self.file, atom.index());
                }
                let result = match list.unpack() {
                    elements @ StarLikeExpressionIterator::Elements(_) => {
                        self.create_list_or_set_generics(elements)
                    }
                    StarLikeExpressionIterator::Empty => Type::Never(NeverCause::Inference),
                };
                return Inferred::from_type(new_class!(
                    i_s.db.python_state.list_node_ref().as_link(),
                    result,
                ));
            }
            ListComprehension(comp) => return self.infer_list_comprehension(comp, result_context),
            Dict(dict) => {
                if let Some(result) = self.infer_dict_literal_from_context(dict, result_context) {
                    return result.save_redirect(i_s, self.file, atom.index());
                } else {
                    return self.dict_literal_without_context(dict);
                }
            }
            DictComprehension(comp) => return self.infer_dict_comprehension(comp, result_context),
            Set(set) => {
                if let Some(result) = self.infer_list_or_set_literal_from_context(
                    set.unpack(),
                    result_context,
                    i_s.db.python_state.set_node_ref(),
                ) {
                    return result.save_redirect(i_s, self.file, atom.index());
                }
                if let elements @ StarLikeExpressionIterator::Elements(_) = set.unpack() {
                    return Inferred::from_type(new_class!(
                        i_s.db.python_state.set_node_ref().as_link(),
                        self.create_list_or_set_generics(elements),
                    ))
                    .save_redirect(i_s, self.file, atom.index());
                } else {
                    // A set can never be empty, because at that point it's a dict: `{}`
                    unreachable!()
                }
            }
            SetComprehension(comp) => return self.infer_set_comprehension(comp, result_context),
            Tuple(tuple) => {
                return self
                    .infer_tuple_iterator(tuple.iter(), result_context)
                    .save_redirect(i_s, self.file, atom.index())
            }
            GeneratorComprehension(comp) => {
                return self.infer_generator_comprehension(comp, result_context)
            }
            YieldExpr(yield_expr) => return self.infer_yield_expr(yield_expr, result_context),
            NamedExpression(named_expression) => {
                return self.infer_named_expression_with_context(named_expression, result_context)
            }
        };
        let point = Point::new_specific(specific, Locality::Todo);
        Inferred::new_and_save(self.file, atom.index(), point)
    }

    fn infer_tuple_iterator<'x>(
        &self,
        iterator: impl ClonableTupleIterator<'x>,
        result_context: &mut ResultContext,
    ) -> Inferred {
        struct TupleGatherer {
            // "before" means before an unpack, which is usually always the case.
            before: Vec<Type>,
            unpack: Option<TupleUnpack>,
            after: Vec<Type>,
            is_arbitrary_length: bool,
        }

        impl TupleGatherer {
            fn add(&mut self, t: Type) {
                if self.unpack.is_some() {
                    self.after.push(t)
                } else {
                    self.before.push(t)
                }
            }

            fn extend_from_slice(&mut self, ts: &[Type]) {
                if self.unpack.is_some() {
                    self.after.extend_from_slice(ts)
                } else {
                    self.before.extend_from_slice(ts)
                }
            }

            fn into_tuple<'x>(
                self,
                inference: &Inference,
                iterator: impl ClonableTupleIterator<'x>,
            ) -> Inferred {
                let content = if self.is_arbitrary_length {
                    let generic = inference.create_list_or_set_generics(iterator);
                    Tuple::new_arbitrary_length(generic)
                } else if let Some(unpack) = self.unpack {
                    Tuple::new(TupleArgs::WithUnpack(WithUnpack {
                        before: self.before.into(),
                        unpack,
                        after: self.after.into(),
                    }))
                } else {
                    Tuple::new_fixed_length(self.before.into())
                };
                debug!(
                    "Inferred: {}",
                    content.format(&FormatData::new_short(inference.i_s.db))
                );
                Inferred::from_type(Type::Tuple(content))
            }
        }

        let mut gatherer = TupleGatherer {
            before: vec![],
            unpack: None,
            after: vec![],
            is_arbitrary_length: false,
        };

        result_context.with_tuple_context_iterator(self.i_s, |tuple_context_iterator| {
            let add_from_stars = |gatherer: &mut TupleGatherer, inferred: Inferred, from_index| {
                match inferred.iter(self.i_s, NodeRef::new(self.file, from_index)) {
                    it @ (IteratorContent::Inferred(_) | IteratorContent::Any(_)) => {
                        if gatherer.unpack.is_some() {
                            gatherer.is_arbitrary_length = true;
                            return;
                        }
                        //gatherer.unpack = Some(TupleUnpack::ArbitraryLen(it.infer_all(self.i_s).as_type(self.i_s)));
                        // TODO this is part of --enable-incomplete-feature=PreciseTupleTypes
                        gatherer.is_arbitrary_length = true;
                    }
                    IteratorContent::FixedLenTupleGenerics { entries, .. } => {
                        gatherer.extend_from_slice(&entries);
                    }
                    IteratorContent::WithUnpack { unpack, .. } => {
                        if gatherer.unpack.is_some() {
                            // Fallback to simplified tuple inference.
                            gatherer.is_arbitrary_length = true;
                            return;
                        }
                        gatherer.extend_from_slice(&unpack.before);
                        gatherer.unpack = Some(unpack.unpack);
                        gatherer.extend_from_slice(&unpack.after)
                    }
                    // TODO this is not correct. The star expression can be a union as well.
                    IteratorContent::Union(_) => todo!(),
                }
            };
            for (e, expected) in iterator.clone().zip(tuple_context_iterator) {
                match e {
                    StarLikeExpression::NamedExpression(e) => {
                        let t = self
                            .infer_named_expression_with_context(
                                e,
                                &mut ResultContext::new_known(expected),
                            )
                            .as_type(self.i_s);
                        gatherer.add(t)
                    }
                    StarLikeExpression::Expression(e) => {
                        let t = self
                            .infer_expression_with_context(
                                e,
                                &mut ResultContext::new_known(expected),
                            )
                            .as_type(self.i_s);
                        gatherer.add(t)
                    }
                    StarLikeExpression::StarNamedExpression(e) => {
                        let inferred = self.infer_expression_part(e.expression_part());
                        add_from_stars(&mut gatherer, inferred, e.index())
                    }
                    StarLikeExpression::StarExpression(e) => {
                        let inferred = self.infer_expression_part(e.expression_part());
                        add_from_stars(&mut gatherer, inferred, e.index())
                    }
                }
                if gatherer.is_arbitrary_length {
                    return;
                }
            }
        });
        gatherer.into_tuple(self, iterator)
    }

    fn infer_primary_target(&self, primary_target: PrimaryTarget) -> Option<Inferred> {
        if let Some(inferred) = self.check_point_cache(primary_target.index()) {
            return Some(inferred);
        }
        if let Some(inf) = self.maybe_lookup_narrowed_primary_target(primary_target) {
            return Some(inf);
        }
        let first = self.infer_primary_target_or_atom(primary_target.first());
        let second = primary_target.second();
        if first.maybe_saved_specific(self.i_s.db) == Some(Specific::MaybeSelfParam) {
            if let PrimaryContent::Attribute(attr) = second {
                let i = attr.index();
                if self.file.points.get(i).calculated() {
                    if let Some(first) = first_defined_name_of_multi_def(self.file, i) {
                        let point = self.file.points.get(first - NAME_DEF_TO_NAME_DIFFERENCE);
                        if point.calculated()
                            && point.maybe_specific().is_some_and(|s| s.is_partial())
                        {
                            return None;
                        }
                    } else {
                        // This is the initial definition of self. The definition is not defined at
                        // this point is probably just inferred to know its context (which is not
                        // known, because this is going to be the definition).
                        return None;
                    }
                }
            }
        }
        Some(
            self.infer_primary_or_primary_t_content(
                &first,
                primary_target.index(),
                second,
                true,
                &mut ResultContext::Unknown,
            )
            .save_redirect(self.i_s, self.file, primary_target.index()),
        )
    }

    pub fn infer_primary_target_or_atom(&self, t: PrimaryTargetOrAtom) -> Inferred {
        match t {
            PrimaryTargetOrAtom::Atom(atom) => self.infer_atom(atom, &mut ResultContext::Unknown),
            PrimaryTargetOrAtom::PrimaryTarget(p) => self
                .infer_primary_target(p)
                .unwrap_or_else(|| Inferred::new_any(AnyCause::Internal)),
        }
    }

    check_point_cache_with!(pub infer_name_reference, Self::_infer_name_reference, Name);
    fn _infer_name_reference(&self, name: Name) -> Inferred {
        self.infer_name_by_str(name.as_code(), name.index())
    }

    fn infer_name_by_str(&self, name_str: &str, save_to_index: NodeIndex) -> Inferred {
        // If it's not inferred already through the name binder, it's either a star import, a
        // builtin or really missing.
        let i_s = self.i_s;
        if let Some(star_imp) = self.lookup_from_star_import(name_str, true) {
            return match star_imp {
                StarImportResult::Link(link) => {
                    self.file.points.set(
                        save_to_index,
                        Point::new_redirect(link.file, link.node_index, Locality::Todo),
                    );
                    self.check_point_cache(save_to_index).unwrap()
                }
                StarImportResult::AnyDueToError => {
                    star_imp
                        .as_inferred(i_s)
                        .save_redirect(i_s, self.file, save_to_index)
                }
            };
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
            _ => {
                if let Some(link) = builtins.lookup_global(name_str).filter(|link| {
                    (is_valid_builtins_export(name_str))
                        && !is_private_import(i_s.db, (*link).into())
                }) {
                    debug_assert!(
                        link.file != self.file.file_index || link.node_index != save_to_index
                    );
                    link.into_point_redirect()
                } else {
                    // The builtin module should really not have any issues.
                    debug_assert!(
                        self.file.file_index != builtins.file_index,
                        "{name_str}; {save_to_index}"
                    );
                    if i_s.in_class_scope().is_some()
                        && matches!(name_str, "__name__" | "__module__" | "__qualname__")
                    {
                        return Inferred::from_type(i_s.db.python_state.str_type());
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
                        if let Some(inf) = i_s
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
                                return inf.remove_none(i_s);
                            }
                            return inf;
                        }
                    }
                    // TODO check star imports
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
        self.check_point_cache(save_to_index).unwrap()
    }

    pub fn lookup_from_star_import(
        &self,
        name: &str,
        check_local: bool,
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
            if let Some(result) =
                self.lookup_name_in_star_import(star_import, name, is_class_star_import)
            {
                return Some(result);
            }
        }
        if let Some(super_file) = &self.file.super_file {
            // This sub file currently means we're in a type definition.
            if let Some(func) = self.i_s.current_function() {
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
                .inference(self.i_s)
                .lookup_from_star_import(name, false)
        } else {
            None
        }
    }

    pub fn lookup_name_in_star_import(
        &self,
        star_import: &StarImport,
        name: &str,
        is_class_star_import: bool,
    ) -> Option<StarImportResult> {
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
            if !is_reexport_issue_if_check_needed(self.i_s.db, other_file, link.into()) {
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
            .inference(self.i_s)
            .lookup_from_star_import(name, false)
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

    pub fn check_point_cache(&self, node_index: NodeIndex) -> Option<Inferred> {
        let point = self.file.points.get(node_index);
        self.check_point_cache_internal(node_index, point, false)
    }

    pub fn check_point_cache_internal(
        &self,
        node_index: NodeIndex,
        point: Point,
        global_redirect: bool,
    ) -> Option<Inferred> {
        point
            .calculated()
            .then(|| self.infer_point(node_index, point, global_redirect))
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
                    Some(Inferred::new_cycle())
                } else {
                    None
                }
            })
    }

    #[inline]
    fn infer_point(&self, node_index: NodeIndex, point: Point, global_redirect: bool) -> Inferred {
        match point.kind() {
            PointKind::Redirect => {
                let file_index = point.file_index();
                let next_node_index = point.node_index();
                if point.needs_flow_analysis() {
                    debug_assert!(Name::maybe_by_index(&self.file.tree, node_index).is_some());
                    if let Some(result) = self.maybe_lookup_narrowed_name(
                        node_index,
                        PointLink::new(file_index, next_node_index),
                    ) {
                        return result;
                    }
                }
                debug_assert!(
                    file_index != self.file.file_index || next_node_index != node_index,
                    "{file_index}:{node_index}"
                );
                let infer = |inference: &Inference| {
                    let new_p = inference.file.points.get(next_node_index);
                    inference
                        .check_point_cache_internal(
                            next_node_index,
                            new_p,
                            global_redirect || !point.in_global_scope() && new_p.in_global_scope(),
                        )
                        .unwrap_or_else(|| {
                            todo!(
                                "When does this ever happen? {}",
                                NodeRef::new(inference.file, next_node_index)
                                    .debug_info(self.i_s.db)
                            )
                        })
                };
                if file_index == self.file.file_index {
                    infer(self)
                } else {
                    infer(
                        &mut self
                            .i_s
                            .db
                            .loaded_python_file(file_index)
                            .inference(self.i_s),
                    )
                }
            }
            PointKind::Specific => match point.specific() {
                specific @ (Specific::Param | Specific::MaybeSelfParam) => self
                    .with_correct_context(global_redirect, |inference| {
                        inference.infer_param(node_index, specific)
                    }),
                specific @ (Specific::GlobalVariable | Specific::NonlocalVariable) => {
                    let index = node_index - GLOBAL_NONLOCAL_TO_NAME_DIFFERENCE
                        + NAME_DEF_TO_NAME_DIFFERENCE;
                    if self.file.points.get(index).calculated() {
                        self.check_point_cache(index).unwrap()
                    } else {
                        debug_assert_eq!(specific, Specific::GlobalVariable);
                        self.with_correct_context(true, |inference| {
                            inference.infer_name_by_str(
                                NodeRef::new(self.file, node_index).as_code(),
                                index,
                            )
                        })
                    }
                }
                Specific::NameOfNameDef => {
                    // MultiDefinition means we are on a Name that has a NameDef as a
                    // parent.
                    let node_index = node_index - NAME_DEF_TO_NAME_DIFFERENCE;
                    let p = self.file.points.get(node_index);
                    self.check_point_cache_internal(node_index, p, global_redirect)
                        .unwrap_or_else(|| {
                            let name_def = NameDef::by_index(&self.file.tree, node_index);
                            self.with_correct_context(global_redirect, |inference| {
                                inference._infer_name_def(name_def)
                            })
                        })
                }
                _ => Inferred::new_saved(self.file, node_index),
            },
            PointKind::Complex | PointKind::FileReference => {
                Inferred::new_saved(self.file, node_index)
            }
            PointKind::NodeAnalysis => {
                unreachable!(
                    "Invalid NodeAnalysis, should not happen on node index {node_index:?}"
                );
            }
        }
    }

    #[inline]
    fn with_correct_context<T>(
        &self,
        global_redirect: bool,
        callable: impl Fn(&Inference) -> T,
    ) -> T {
        if global_redirect {
            FLOW_ANALYSIS.with(|fa| {
                fa.with_new_empty(self.i_s, || {
                    callable(&self.file.inference(&InferenceState::new(self.i_s.db)))
                })
            })
        } else {
            callable(self)
        }
    }

    fn infer_param(&self, node_index: NodeIndex, specific: Specific) -> Inferred {
        let name_def = NameDef::by_index(&self.file.tree, node_index);
        // Performance: This could be improved by not needing to lookup all the
        // parents all the time.
        match name_def.function_or_lambda_ancestor().unwrap() {
            FunctionOrLambda::Function(func_node) => {
                let func = Function::new(
                    NodeRef::new(self.file, func_node.index()),
                    self.i_s.current_class(),
                );
                func.ensure_cached_func(self.i_s);

                if let Some(annotation) = name_def.maybe_param_annotation() {
                    self.use_cached_param_annotation(annotation)
                } else if let Some(function) = self.i_s.current_function() {
                    if specific == Specific::MaybeSelfParam {
                        match func.first_param_kind(self.i_s) {
                            FirstParamKind::Self_ => Inferred::new_saved(self.file, node_index),
                            FirstParamKind::ClassOfSelf => {
                                Inferred::from_type(Type::Type(Rc::new(Type::Self_)))
                            }
                            FirstParamKind::InStaticmethod => {
                                Inferred::from_type(Type::Any(AnyCause::Unannotated))
                            }
                        }
                    } else {
                        for param in func_node.params().iter() {
                            if param.name_def().index() == name_def.index() {
                                return match param.kind() {
                                    ParamKind::Star => Inferred::from_type(
                                        self.i_s.db.python_state.tuple_of_unannotated_any.clone(),
                                    ),
                                    ParamKind::StarStar => Inferred::from_type(new_class!(
                                        self.i_s.db.python_state.dict_node_ref().as_link(),
                                        self.i_s.db.python_state.str_type(),
                                        Type::Any(AnyCause::Unannotated),
                                    )),
                                    _ => Inferred::new_any(AnyCause::Unannotated),
                                };
                            }
                        }
                        unreachable!()
                    }
                } else if specific == Specific::MaybeSelfParam {
                    Inferred::new_saved(self.file, node_index)
                } else {
                    Inferred::new_any(AnyCause::Unannotated)
                }
            }
            FunctionOrLambda::Lambda(lambda) => lookup_lambda_param(self.i_s, lambda, node_index),
        }
    }

    pub fn infer_name_of_definition_by_index(&self, node_index: NodeIndex) -> Inferred {
        self.infer_name_of_definition(Name::by_index(&self.file.tree, node_index))
    }

    pub fn infer_name_of_definition(&self, name: Name) -> Inferred {
        let point = self.file.points.get(name.index());
        if point.calculated() && point.maybe_specific() != Some(Specific::NameOfNameDef) {
            if let Some(inf) = self.check_point_cache(name.index()) {
                return inf;
            }
        }
        self.infer_name_def(name.name_def().unwrap())
    }

    check_point_cache_with!(pub infer_name_def, Self::_infer_name_def, NameDef);
    fn _infer_name_def(&self, name_def: NameDef) -> Inferred {
        let defining_stmt = name_def.expect_defining_stmt();
        self.cache_defining_stmt(defining_stmt, NodeRef::new(self.file, name_def.index()));
        debug_assert!(
            self.file.points.get(name_def.index()).calculated(),
            "{name_def:?}",
        );
        self.infer_name_def(name_def)
    }

    fn cache_defining_stmt(&self, defining_stmt: DefiningStmt, name_def: NodeRef) {
        debug!(
            "Infer name of stmt (#{}, {}:{})",
            name_def.line(),
            self.file.file_index,
            defining_stmt.index(),
        );
        match defining_stmt {
            DefiningStmt::FunctionDef(func_def) => {
                Function::new(
                    NodeRef::new(self.file, func_def.index()),
                    self.i_s.current_class(),
                )
                .cache_func_with_name_def(self.i_s, name_def);
            }
            DefiningStmt::ClassDef(cls) => cache_class_name(name_def, cls),
            DefiningStmt::Assignment(assignment) => {
                self.cache_assignment(assignment);
            }
            DefiningStmt::ImportName(import_name) => {
                self.cache_import_name(import_name);
            }
            DefiningStmt::ImportFromAsName(as_name) => {
                self.cache_import_from_only_particular_name_def(as_name)
            }
            DefiningStmt::Walrus(walrus) => {
                self.infer_walrus(walrus, None);
            }
            DefiningStmt::Lambda(_)
            | DefiningStmt::Comprehension(_)
            | DefiningStmt::DictComprehension(_) => unreachable!(),
            DefiningStmt::ForStmt(for_stmt) => {
                name_def.set_point(Point::new_calculating());
                let (star_targets, star_exprs, _, _) = for_stmt.unpack();
                // Performance: We probably do not need to calculate diagnostics just for
                // calculating the names.
                self.cache_for_stmt_names(star_targets, star_exprs, false);
            }
            DefiningStmt::TryStmt(try_stmt) => {
                for block in try_stmt.iter_blocks() {
                    match block {
                        TryBlockType::Except(except) => {
                            if let (Some(except_expr), _) = except.unpack() {
                                let (expr, name_def) = except_expr.unpack();
                                if let Some(name_def) = name_def {
                                    let inf = self.infer_expression(expr);
                                    Inferred::from_type(instantiate_except(
                                        self.i_s,
                                        &inf.as_cow_type(self.i_s),
                                    ))
                                    .maybe_save_redirect(
                                        self.i_s,
                                        self.file,
                                        name_def.index(),
                                        false,
                                    );
                                }
                            }
                        }
                        TryBlockType::ExceptStar(except_star) => {
                            let (except_expr, _) = except_star.unpack();
                            let (expr, name_def) = except_expr.unpack();
                            if let Some(name_def) = name_def {
                                let inf = self.infer_expression(expr);
                                Inferred::from_type(instantiate_except_star(
                                    self.i_s,
                                    &inf.as_cow_type(self.i_s),
                                ))
                                .maybe_save_redirect(
                                    self.i_s,
                                    self.file,
                                    name_def.index(),
                                    false,
                                );
                            }
                        }
                        _ => (),
                    }
                }
            }
        }
    }

    pub fn infer_comprehension_recursively<T>(
        &self,
        mut for_if_clauses: ForIfClauseIterator,
        item_callable: impl FnOnce() -> T,
    ) -> T {
        if let Some(for_if_clause) = for_if_clauses.next() {
            let mut needs_await = false;
            let (targets, expr_part, comp_ifs) = match for_if_clause {
                ForIfClause::Sync(sync) => sync.unpack(),
                ForIfClause::Async(async_) => {
                    needs_await = true;
                    async_.unpack()
                }
            };
            let clause_node_ref = NodeRef::new(self.file, for_if_clause.index());
            let base = self.infer_expression_part(expr_part);
            let inf = if needs_await {
                await_aiter_and_next(self.i_s, base, clause_node_ref)
            } else {
                base.iter(self.i_s, NodeRef::new(self.file, expr_part.index()))
                    .infer_all(self.i_s)
            };
            self.assign_targets(
                targets.as_target(),
                inf,
                clause_node_ref,
                AssignKind::Normal,
            );
            self.flow_analysis_for_comprehension_with_comp_ifs(
                for_if_clauses,
                comp_ifs,
                item_callable,
            )
        } else {
            item_callable()
        }
    }

    fn infer_dict_comprehension(
        &self,
        dict_comp: DictComprehension,
        result_context: &mut ResultContext,
    ) -> Inferred {
        let i_s = self.i_s;
        let (key_value, for_if_clauses) = dict_comp.unpack();
        self.infer_comprehension_recursively(for_if_clauses.iter(), || {
            let to_dict = |key: Type, value: Type| {
                new_class!(
                    self.i_s.db.python_state.dict_node_ref().as_link(),
                    key.avoid_implicit_literal(i_s.db),
                    value.avoid_implicit_literal(i_s.db),
                )
            };
            let found = infer_dict_like(i_s, result_context, |matcher, key_t, value_t| {
                let mut check = |expected_t: &Type, expr, part| {
                    let inf = self.infer_expression_with_context(
                        expr,
                        &mut ResultContext::new_known(expected_t),
                    );
                    let t = inf.as_cow_type(i_s);
                    if expected_t.is_super_type_of(i_s, matcher, &t).bool() {
                        Some(t.into_owned())
                    } else {
                        self.add_issue(
                            expr.index(),
                            IssueKind::DictComprehensionMismatch {
                                part,
                                got: t.format_short(i_s.db),
                                expected: expected_t.format_short(i_s.db),
                            },
                        );
                        None
                    }
                };
                let key_result = check(key_t, key_value.key(), "Key");
                let value_result = check(value_t, key_value.value(), "Value");
                key_result.zip(value_result).map(|(k, v)| to_dict(k, v))
            });
            found.unwrap_or_else(|| {
                let key = self.infer_expression(key_value.key()).as_type(i_s);
                let value = self.infer_expression(key_value.value()).as_type(i_s);
                Inferred::from_type(to_dict(key, value))
            })
        })
    }

    fn infer_comprehension_expr_with_context(
        &self,
        result_context: &mut ResultContext,
        class: NodeRef,
        mut on_mismatch: impl FnMut(&ErrorTypes) -> IssueKind,
        comp: Comprehension,
    ) -> Type {
        let i_s = self.i_s;
        let (comp_expr, for_if_clauses) = comp.unpack();
        self.infer_comprehension_recursively(for_if_clauses.iter(), || {
            result_context
                .on_unique_type_in_unpacked_union(i_s, class, |matcher, cls_matcher| {
                    let inner_expected = cls_matcher
                        .into_type_arg_iterator_or_any(i_s.db)
                        .next()
                        .unwrap();
                    let inf = self.infer_named_expression_with_context(
                        comp_expr,
                        &mut ResultContext::WithMatcher {
                            matcher,
                            type_: &inner_expected,
                        },
                    );
                    inner_expected.error_if_not_matches_with_matcher(
                        i_s,
                        matcher,
                        &inf,
                        |issue| self.add_issue(comp_expr.index(), issue),
                        |error_types, _: &_| Some(on_mismatch(error_types)),
                    );
                    matcher.replace_type_var_likes_for_unknown_type_vars(i_s.db, &inner_expected)
                })
                .unwrap_or_else(|| self.infer_named_expression(comp_expr).as_type(i_s))
                .avoid_implicit_literal(i_s.db)
        })
    }

    fn infer_list_comprehension(
        &self,
        comp: Comprehension,
        result_context: &mut ResultContext,
    ) -> Inferred {
        let t = self.infer_comprehension_expr_with_context(
            result_context,
            self.i_s.db.python_state.list_node_ref(),
            |error_types| {
                let ErrorStrs { expected, got } = error_types.as_boxed_strs(self.i_s.db);
                IssueKind::ListComprehensionMismatch { got, expected }
            },
            comp,
        );
        Inferred::from_type(new_class!(
            self.i_s.db.python_state.list_node_ref().as_link(),
            t,
        ))
    }

    fn infer_set_comprehension(
        &self,
        comp: Comprehension,
        result_context: &mut ResultContext,
    ) -> Inferred {
        let t = self.infer_comprehension_expr_with_context(
            result_context,
            self.i_s.db.python_state.set_node_ref(),
            |error_types| {
                let ErrorStrs { expected, got } = error_types.as_boxed_strs(self.i_s.db);
                IssueKind::SetComprehensionMismatch { got, expected }
            },
            comp,
        );
        Inferred::from_type(new_class!(
            self.i_s.db.python_state.set_node_ref().as_link(),
            t,
        ))
    }

    pub fn infer_generator_comprehension(
        &self,
        comp: Comprehension,
        result_context: &mut ResultContext,
    ) -> Inferred {
        let t = self.infer_comprehension_expr_with_context(
            result_context,
            self.i_s.db.python_state.generator_node_ref(),
            |error_types| {
                let ErrorStrs { expected, got } = error_types.as_boxed_strs(self.i_s.db);
                IssueKind::GeneratorComprehensionMismatch { got, expected }
            },
            comp,
        );
        let (named_expr, for_if_clauses) = comp.unpack();
        let is_async = named_expr.has_await()
            || for_if_clauses
                .iter()
                .enumerate()
                .any(|(i, for_if_clause)| match for_if_clause {
                    ForIfClause::Async(_) => true,
                    ForIfClause::Sync(sync_for_if) => match i {
                        0 => {
                            let (_, _, mut conditionals) = sync_for_if.unpack();
                            conditionals.any(|c| c.has_await())
                        }
                        _ => sync_for_if.has_await(),
                    },
                });
        Inferred::from_type(if is_async {
            new_class!(
                self.i_s.db.python_state.async_generator_link(),
                t,
                Type::None,
            )
        } else {
            new_class!(
                self.i_s.db.python_state.generator_link(),
                t,
                Type::None,
                Type::None,
            )
        })
    }

    check_point_cache_with!(pub infer_decorator, Self::_infer_decorator, Decorator);
    fn _infer_decorator(&self, decorator: Decorator) -> Inferred {
        let i = self.infer_named_expression(decorator.named_expression());
        i.save_redirect(self.i_s, self.file, decorator.index())
    }

    pub fn is_no_type_check(&self, decorated: Decorated) -> bool {
        let no_type_check_link = self.i_s.db.python_state.no_type_check_link();
        decorated.decorators().iter().any(|decorator| {
            self.infer_decorator(decorator).maybe_saved_link() == Some(no_type_check_link)
        })
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

pub fn instantiate_except(i_s: &InferenceState, t: &Type) -> Type {
    match t {
        // No need to check these here, this is done when calculating diagnostics
        Type::Type(t) => match t.as_ref() {
            inner @ Type::Class(..) => inner.clone(),
            _ => Type::Any(AnyCause::FromError),
        },
        Type::Any(cause) => Type::Any(*cause),
        Type::Tuple(content) => Inferred::gather_simplified_union(i_s, |add| match &content.args {
            TupleArgs::FixedLen(ts) => {
                for t in ts.iter() {
                    add(Inferred::from_type(instantiate_except(i_s, t)))
                }
            }
            TupleArgs::ArbitraryLen(t) => add(Inferred::from_type(instantiate_except(i_s, t))),
            TupleArgs::WithUnpack(_) => add(Inferred::new_any_from_error()),
        })
        .as_cow_type(i_s)
        .into_owned(),
        Type::Union(union) => Type::Union(UnionType::new(
            union
                .entries
                .iter()
                .map(|e| UnionEntry {
                    type_: instantiate_except(i_s, &e.type_),
                    format_index: e.format_index,
                })
                .collect(),
        )),
        _ => Type::Any(AnyCause::FromError),
    }
}

pub fn instantiate_except_star(i_s: &InferenceState, t: &Type) -> Type {
    let result = gather_except_star(i_s, t);
    // When BaseException is used, we need a BaseExceptionGroup. Otherwise when every exception
    // inherits from Exception, ExceptionGroup is used.
    let is_base_exception_group = has_base_exception(i_s.db, &result);
    new_class!(
        match is_base_exception_group {
            false => i_s
                .db
                .python_state
                .exception_group_node_ref()
                .unwrap_or_else(|| todo!("Star syntax without stdlib valid symbol"))
                .as_link(),
            true => i_s
                .db
                .python_state
                .base_exception_group_node_ref()
                .unwrap_or_else(|| todo!("Star syntax without stdlib valid symbol"))
                .as_link(),
        },
        result,
    )
}

fn has_base_exception(db: &Database, t: &Type) -> bool {
    match t {
        Type::Class(c) => !c.class(db).is_exception(db),
        Type::Union(u) => u.iter().any(|t| has_base_exception(db, t)),
        Type::Any(_) => false,
        // Gathering the exceptions already makes sure we do not end up with arbitrary types here.
        _ => unreachable!(),
    }
}

fn gather_except_star(i_s: &InferenceState, t: &Type) -> Type {
    match t {
        Type::Type(t) => match t.as_ref() {
            inner @ Type::Class(c) => {
                let cls = c.class(i_s.db);
                if cls.is_base_exception_group(i_s.db) {
                    // Diagnostics are calculated when calculating diagnostics, not here.
                    Type::Any(AnyCause::FromError)
                } else if cls.is_base_exception(i_s.db) {
                    inner.clone()
                } else {
                    Type::Any(AnyCause::FromError)
                }
            }
            _ => Type::Any(AnyCause::FromError),
        },
        Type::Any(cause) => Type::Any(*cause),
        Type::Tuple(content) => Inferred::gather_simplified_union(i_s, |add| match &content.args {
            TupleArgs::FixedLen(ts) => {
                for t in ts.iter() {
                    add(Inferred::from_type(gather_except_star(i_s, t)))
                }
            }
            TupleArgs::ArbitraryLen(t) => add(Inferred::from_type(gather_except_star(i_s, t))),
            TupleArgs::WithUnpack(_) => add(Inferred::new_any_from_error()),
        })
        .as_cow_type(i_s)
        .into_owned(),
        Type::Union(union) => Type::Union(UnionType::new(
            union
                .entries
                .iter()
                .map(|e| UnionEntry {
                    type_: gather_except_star(i_s, &e.type_),
                    format_index: e.format_index,
                })
                .collect(),
        )),
        _ => Type::Any(AnyCause::FromError),
    }
}

fn get_generator_return_type(db: &Database, t: &Type) -> Type {
    match t {
        Type::Class(c) => {
            if c.link == db.python_state.generator_link() {
                c.class(db).nth_type_argument(db, 2)
            } else {
                todo!("{t:?}")
            }
        }
        Type::Any(cause) => Type::Any(*cause),
        Type::Union(union) => Type::Union(UnionType::new(
            union
                .entries
                .iter()
                .map(|entry| UnionEntry {
                    type_: get_generator_return_type(db, &entry.type_),
                    format_index: entry.format_index,
                })
                .collect(),
        )),
        _ => todo!("{t:?}"),
    }
}

pub fn first_defined_name(file: &PythonFile, name_index: NodeIndex) -> NodeIndex {
    let point = file.points.get(name_index);
    if !point.calculated() || point.specific() != Specific::NameOfNameDef {
        // Happens e.g. for the definition of builtins.type (overwritten in python_state.rs)
        // Or definitions of names that look like self (e.g. in testInferAttributeInitializedToEmptyNonSelf)
        return name_index;
    }
    let mut current = point.node_index();
    loop {
        let point = file.points.get(current);
        debug_assert!(point.calculated());
        debug_assert_eq!(point.specific(), Specific::NameOfNameDef);
        // Here we circle through multi definitions to find the first one.
        // Note that multi definition links loop, i.e. A -> B -> C -> A.
        let next = point.node_index();
        if next <= current {
            return next;
        }
        current = next;
    }
}

pub fn first_defined_name_of_multi_def(
    file: &PythonFile,
    name_index: NodeIndex,
) -> Option<NodeIndex> {
    // Returns the first definition, if the name_index is a later definition.
    let first = first_defined_name(file, name_index);
    (first != name_index).then_some(first)
}

pub fn await_(
    i_s: &InferenceState,
    inf: Inferred,
    from: NodeRef,
    no_lookup_cause: &'static str,
    expect_not_none: bool,
) -> Inferred {
    let t = get_generator_return_type(
        i_s.db,
        inf.type_lookup_and_execute(i_s, from.file, "__await__", &NoArgs::new(from), &|t| {
            from.add_issue(
                i_s,
                IssueKind::IncompatibleTypes {
                    cause: no_lookup_cause,
                    got: t.format_short(i_s.db),
                    expected: "Awaitable[Any]".into(),
                },
            );
        })
        .as_cow_type(i_s)
        .as_ref(),
    );
    if matches!(t, Type::Never(_)) {
        FLOW_ANALYSIS.with(|fa| fa.mark_current_frame_unreachable())
    }
    if expect_not_none && matches!(t, Type::None) {
        from.add_issue(i_s, IssueKind::DoesNotReturnAValue("Function".into()));
        Inferred::new_any_from_error()
    } else {
        Inferred::from_type(t)
    }
}

fn targets_len_infos(targets: TargetIterator) -> (usize, TupleLenInfos) {
    let mut before = 0;
    let mut star_count = 0;
    let mut after = 0;
    for target in targets {
        match target {
            Target::Starred(_) => star_count += 1,
            _ if star_count > 0 => after += 1,
            _ => before += 1,
        }
    }
    (
        star_count,
        if star_count > 0 {
            TupleLenInfos::WithStar { before, after }
        } else {
            TupleLenInfos::FixedLen(before)
        },
    )
}

#[derive(Debug, Copy, Clone, PartialEq)]
pub enum AssignKind {
    Annotation { specific: Option<Specific> }, // `a: int = 1` or `a = 1 # type: int
    Normal,                                    // a = 1
    Import,
    AugAssign, // a += 1
}

pub enum StarImportResult {
    Link(PointLink),
    AnyDueToError,
}

impl StarImportResult {
    pub fn as_inferred(&self, i_s: &InferenceState) -> Inferred {
        match self {
            Self::Link(link) => i_s
                .db
                .loaded_python_file(link.file)
                .inference(i_s)
                .infer_name_of_definition_by_index(link.node_index),
            Self::AnyDueToError => Inferred::new_any_from_error(),
        }
    }

    pub fn into_lookup_result(self, i_s: &InferenceState) -> LookupResult {
        let inf = self.as_inferred(i_s);
        match self {
            StarImportResult::Link(link) => LookupResult::GotoName { name: link, inf },
            StarImportResult::AnyDueToError => LookupResult::UnknownName(inf),
        }
    }
}

fn move_lambda_context_keyword_to_positional_or_keyword(
    db: &Database,
    context_params: &mut Rc<[CallableParam]>,
    params: ParamIterator,
) {
    *context_params = context_params
        .iter()
        .map(|p| {
            if let ParamType::KeywordOnly(t) = &p.type_ {
                let search = p.name.as_ref().unwrap().as_str(db);
                for lambda_p in params.clone() {
                    if lambda_p.kind() == ParamKind::PositionalOrKeyword
                        && lambda_p.name_def().as_code() == search
                    {
                        return CallableParam {
                            type_: ParamType::PositionalOrKeyword(t.clone()),
                            name: p.name.clone(),
                            has_default: p.has_default,
                        };
                    }
                }
            }
            p.clone()
        })
        .collect();
}

fn lookup_lambda_param(
    i_s: &InferenceState,
    lambda: Lambda,
    name_node_index: NodeIndex,
) -> Inferred {
    for (i, p) in lambda.params().enumerate() {
        if p.name_def().index() == name_node_index {
            if let Some(current_callable) = i_s.current_lambda_callable() {
                return match &current_callable.params {
                    CallableParams::Simple(c_params) => {
                        for p2 in c_params.iter() {
                            if let Some(n) = &p2.name {
                                if n.as_str(i_s.db) == p.name_def().as_code() {
                                    if let Some(t) = p2.type_.maybe_type() {
                                        return Inferred::from_type(t.clone());
                                    }
                                }
                            }
                        }
                        if p.kind() == ParamKind::PositionalOrKeyword {
                            if let Some(p2) = c_params.get(i) {
                                if let ParamType::PositionalOnly(t) = &p2.type_ {
                                    return Inferred::from_type(t.clone());
                                }
                            }
                        }
                        // TODO here we should do proper matching for lambda params.
                        Inferred::new_any(AnyCause::FromError)
                    }
                    CallableParams::Any(cause) => Inferred::new_any(*cause),
                    CallableParams::Never(_) => Inferred::new_any(AnyCause::Todo),
                };
            } else {
                return Inferred::new_any(AnyCause::Todo);
            }
        }
    }
    unreachable!()
}

fn is_valid_builtins_export(name: &str) -> bool {
    !name.starts_with('_') || name.starts_with("__") && name.ends_with("__")
}
