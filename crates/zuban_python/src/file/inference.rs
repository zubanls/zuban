use parsa_python_cst::*;
use std::{borrow::Cow, cell::Cell, sync::Arc};

use super::{
    ClassNodeRef, FLOW_ANALYSIS, File, PythonFile,
    diagnostics::{await_aiter_and_next, check_override},
    flow_analysis::has_custom_special_method,
    name_resolution::{ModuleAccessDetail, NameResolution},
    on_argument_type_error, process_unfinished_partials,
    type_computation::ANNOTATION_TO_EXPR_DIFFERENCE,
    utils::{func_of_self_symbol, infer_dict_like},
};
use crate::{
    arguments::{Args, InferredArg, KnownArgs, KnownArgsWithCustomAddIssue, NoArgs, SimpleArgs},
    database::{ComplexPoint, Database, Locality, Point, PointKind, PointLink, RunCause, Specific},
    debug,
    diagnostics::{Issue, IssueKind},
    file::{
        OtherDefinitionIterator, flow_analysis::RedefinitionResult,
        name_resolution::PointResolution, type_computation::TypeCommentState, utils::TupleGatherer,
    },
    format_data::FormatData,
    getitem::SliceType,
    inference_state::{InferenceState, Mode},
    inferred::{
        ApplyClassDescriptorsOrigin, AttributeKind, Inferred, MroIndex,
        NAME_DEF_TO_DEFAULTDICT_DIFF, UnionValue, add_attribute_error, specific_to_type,
    },
    matching::{
        ErrorStrs, ErrorTypes, Generics, IteratorContent, LookupKind, Matcher, OnTypeError,
        TupleLenInfos, format_got_expected,
    },
    new_class,
    node_ref::NodeRef,
    params::matches_simple_params,
    pytest::maybe_infer_pytest_param,
    recoverable_error,
    result_context::{CouldBeALiteral, ResultContext, ResultContextOrigin},
    type_::{
        AnyCause, CallableContent, CallableParam, CallableParams, DbString, IterCause, IterInfos,
        Literal, LiteralKind, LookupResult, ParamType, StarParamType, StarStarParamType,
        StringSlice, Tuple, TupleArgs, TupleUnpack, Type, UnionEntry, UnionType, Variance,
        dataclass_converter_fields_lookup,
    },
    type_helpers::{
        Class, ClassLookupOptions, FirstParamKind, Function, GeneratorType, Instance,
        InstanceLookupOptions, LookupDetails, TypeOrClass, cache_class_name, is_private,
    },
    utils::debug_indent,
};

const ENUM_NAMES_OVERRIDABLE: [&str; 2] = ["value", "name"];

pub(crate) struct Inference<'db, 'file, 'i_s>(pub(super) NameResolution<'db, 'file, 'i_s>);

impl<'db: 'file, 'file, 'i_s> std::ops::Deref for Inference<'db, 'file, 'i_s> {
    type Target = NameResolution<'db, 'file, 'i_s>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

macro_rules! check_point_cache_with {
    ($vis:vis $name:ident, $func:path, $ast:ident $(, $result_context:ident )?) => {
        $vis fn $name(&self, node: $ast $(, $result_context : &mut ResultContext)?) -> $crate::inferred::Inferred {
            if let Some(inferred) = self.check_point_cache(node.index()) {
                debug!(
                    "{} {:?} ({}:#{}) from cache: {}",
                    stringify!($name),
                    node.short_debug(),
                    self.file.qualified_name(self.i_s.db),
                    self.file.byte_to_position_infos(self.i_s.db, node.start()).line_one_based(),
                    {
                        let point = self.point(node.index());
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
                    "{} {:?} ({}:#{})",
                    stringify!($name),
                    node.short_debug(),
                    self.file.qualified_name(self.i_s.db),
                    self.file.byte_to_position_infos(self.i_s.db, node.start()).line_one_based(),
                );
                let _indent = debug_indent();
                $func(self, node $(, $result_context)?)
            }
        }
    }
}

impl<'db, 'file> Inference<'db, 'file, '_> {
    pub(super) fn cache_import_name(&self, imp: ImportName) {
        if self.point(imp.index()).calculated() {
            return;
        }
        for dotted_as_name in imp.iter_dotted_as_names() {
            let inf = self
                .file
                .infer_dotted_as_name_import(self.i_s.db, dotted_as_name);
            let name_def = dotted_as_name.name_def();
            let node_ref = NodeRef::new(self.file, name_def.index());
            if node_ref.point().calculated() {
                // It was already assigned (probably during type computation)
                return;
            }
            node_ref.set_point(Point::new_calculating());

            self.assign_to_name_def_simple(
                name_def,
                NodeRef::new(self.file, name_def.index()),
                &inf,
                AssignKind::Import,
            );
            if node_ref.point().calculating() {
                node_ref.set_point(Point::new_uncalculated())
            }
        }
        self.set_point(
            imp.index(),
            Point::new_specific(Specific::Analyzed, Locality::Todo),
        );
    }

    pub(super) fn cache_import_from(&self, imp: ImportFrom) {
        if self.point(imp.index()).calculated() {
            return;
        }
        match imp.unpack_targets() {
            ImportFromTargets::Star(keyword) => {
                self.file
                    .assign_star_import(self.i_s.db, imp, keyword.index())
            }
            ImportFromTargets::Iterator(as_names) => {
                let from_first_part = self.file.import_from_first_part(self.i_s.db, imp);
                for as_name in as_names {
                    self.cache_import_from_part(
                        imp,
                        &from_first_part,
                        as_name,
                        |name_def, pr, redirect_to_link| {
                            self.assign_to_import_from_name(name_def, pr, redirect_to_link)
                        },
                    )
                }
            }
        }

        self.set_point(
            imp.index(),
            Point::new_specific(Specific::Analyzed, Locality::Todo),
        );
    }

    fn assign_to_import_from_name(
        &self,
        name_def: NameDef,
        pr: PointResolution,
        redirect_to: Option<ModuleAccessDetail>,
    ) {
        let inf = self.infer_module_point_resolution(pr, |k| self.add_issue(name_def.index(), k));
        if self.i_s.db.project.flags.disallow_deprecated {
            inf.add_issue_if_deprecated(self.i_s.db, None, |issue| {
                self.add_issue(name_def.index(), issue)
            })
        }
        self.assign_to_name_def(
            name_def,
            NodeRef::new(self.file, name_def.index()),
            &inf,
            AssignKind::Import,
            |_, inf| match redirect_to {
                Some(to) if inf.is_saved() => {
                    self.set_point(name_def.index(), to.into_point(Locality::Todo));
                }
                _ => {
                    inf.clone()
                        .save_redirect(self.i_s, self.file, name_def.index());
                }
            },
        );
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
                            ClassLookupOptions::new(&|_| ())
                                .with_origin(ApplyClassDescriptorsOrigin::AssignContext),
                        )
                        .lookup
                    } else {
                        let t = base.as_cow_type(self.i_s);
                        if matches!(t.as_ref(), Type::Self_) {
                            // To make partials possible on Self, we just use the normal
                            // infer_target mechanism, which returns None when partials are
                            // detected.
                            if let Some(inferred) = self.infer_target(target, false) {
                                return Some(inferred);
                            }
                            continue;
                        } else {
                            t.lookup(
                                self.i_s,
                                self.file,
                                name_def.as_code(),
                                LookupKind::Normal,
                                &mut ResultContext::ValueExpected,
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

    pub(super) fn set_calculating_on_target(&self, target: Target) {
        match target {
            Target::Name(name_def) | Target::NameExpression(_, name_def) => {
                self.set_point(name_def.index(), Point::new_calculating());
            }
            Target::IndexExpression(_) => (),
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
                if let AssignmentRightSide::StarExpressions(star_exprs) = right_side
                    && let StarExpressionContent::Expression(expr) = star_exprs.unpack()
                    && expr.is_ellipsis_literal()
                {
                    return None;
                }
            }
            let ErrorStrs { expected, got } = error_types.as_boxed_strs(self.i_s.db);
            Some(IssueKind::IncompatibleAssignment { got, expected })
        };
        expected.error_if_not_matches(
            self.i_s,
            &right,
            |issue| self.maybe_add_issue(right_side.index(), issue),
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
                origin: ResultContextOrigin::AssignmentAnnotation,
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
                    self.set_point(
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

    pub fn ensure_cached_assignment(&self, assignment: Assignment) {
        let node_ref = NodeRef::new(self.file, assignment.index());
        if node_ref.point().calculated() {
            return;
        }
        debug!("Cache assignment {}", assignment.as_code());
        match assignment.unpack() {
            AssignmentContent::Normal(targets, right_side) => {
                self.cache_normal_assignment(assignment, targets, right_side)
            }
            AssignmentContent::WithAnnotation(target, annotation, right_side) => {
                self.cache_annotation_assignment(node_ref, target, annotation, right_side)
            }
            AssignmentContent::AugAssign(target, aug_assign, right_side) => {
                self.set_calculating_on_target(target.clone());
                self.cache_aug_assign(node_ref, target, aug_assign, right_side)
            }
        }
        self.set_point(
            assignment.index(),
            Point::new_specific(Specific::Analyzed, Locality::Todo),
        );
    }

    #[inline]
    fn cache_normal_assignment<'x>(
        &self,
        assignment: Assignment,
        targets: AssignmentTargetIterator<'x>,
        right_side: AssignmentRightSide,
    ) {
        for target in targets.clone() {
            self.set_calculating_on_target(target);
        }

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
                            origin: ResultContextOrigin::AssignmentAnnotation,
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
                    self.fill_potentially_unfinished_final_or_class_var(node_ref, Some(right_side));
                }
            }
            type_comment.inferred
        } else {
            let inf = self.inferred_context_for_simple_assignment(targets.clone());
            let return_type = inf.as_ref().map(|inf| inf.as_cow_type(self.i_s));
            let mut result_context = match &return_type {
                Some(t) => ResultContext::Known {
                    type_: t,
                    origin: ResultContextOrigin::NormalAssignment,
                },
                None => ResultContext::AssignmentNewDefinition {
                    assignment_definition: PointLink::new(self.file.file_index, assignment.index()),
                },
            };
            self.infer_assignment_right_side(right_side, &mut result_context)
        };
        let n = NodeRef::new(self.file, right_side.index());
        for target in targets {
            self.assign_targets(target, right.clone(), n, assign_kind)
        }
    }

    #[inline]
    fn cache_annotation_assignment(
        &self,
        assignment_node_ref: NodeRef,
        target: Target,
        annotation: Annotation,
        right_side: Option<AssignmentRightSide>,
    ) {
        self.ensure_cached_annotation(annotation, right_side.is_some());
        let specific = self.point(annotation.index()).maybe_specific();
        let assign_kind = AssignKind::Annotation { specific };
        match specific {
            Some(Specific::AnnotationTypeAlias) => {
                let inf =
                    self.compute_explicit_type_assignment(assignment_node_ref.expect_assignment());
                self.assign_single_target(
                    target,
                    assignment_node_ref,
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
                    // There can be potential cycles here like x: Final = x
                    self.set_calculating_on_target(target.clone());
                    checked = self.fill_potentially_unfinished_final_or_class_var(
                        NodeRef::new(self.file, annotation.index()),
                        right_side,
                    )
                }
                self.assign_for_annotation(annotation, target, assignment_node_ref);
                if let Some(right_side) = right_side
                    && !checked
                {
                    let t = self.use_cached_annotation_type(annotation);
                    self.check_right_side_against_annotation(&t, right_side);
                }
            }
        }
    }

    #[inline]
    fn cache_aug_assign(
        &self,
        node_ref: NodeRef,
        target: Target,
        aug_assign: AugAssign,
        right_side: AssignmentRightSide,
    ) {
        let (inplace_method, op_infos) = aug_assign.magic_methods();
        let right = self.infer_assignment_right_side(right_side, &mut ResultContext::ValueExpected);
        let lookup_and_execute = |left: Inferred| {
            let had_lookup_error = Cell::new(false);
            let mut result = left.type_lookup_and_execute(
                self.i_s,
                node_ref.file,
                inplace_method,
                &KnownArgs::new(&right, node_ref),
                &mut ResultContext::ValueExpected,
                &|_type| had_lookup_error.set(true),
            );
            if had_lookup_error.get() {
                result = self.infer_detailed_operation(
                    right_side.index(),
                    op_infos,
                    left,
                    &right,
                    &mut ResultContext::ValueExpected,
                )
            }
            result
        };
        if let Some(left) = self.infer_target(target.clone(), true) {
            let result = lookup_and_execute(left);

            let n = NodeRef::new(self.file, right_side.index());
            self.assign_single_target(
                target.clone(),
                n,
                &result,
                AssignKind::AugAssign,
                |index, inf| {
                    if let Target::NameExpression(_, n) = target
                        && !self.point(n.index()).calculated()
                        && first_defined_name_of_multi_def(self.file, n.name_index()).is_none()
                    {
                        // In some cases where we have a self.foo += 1 where foo is defined
                        // in the super class we need to save.
                        inf.clone().save_redirect(self.i_s, self.file, index);
                    }
                    // There is no need to save this in other cases, because it's never used
                },
            )
        } else if self
            .maybe_partial_aug_assignment(&target, aug_assign, &right, lookup_and_execute)
            .is_none()
        {
            // This is essentially a bare `foo += 1` that does not have any definition and
            // leads to a NameError within Python.
            match target.clone() {
                Target::Name(name_def) => {
                    debug!("Name not found for aug assignment");
                    self.add_issue(
                        name_def.index(),
                        IssueKind::NameError {
                            name: name_def.as_code().into(),
                            note: None,
                        },
                    )
                }
                Target::NameExpression(t, n) => node_ref.add_issue(
                    self.i_s,
                    IssueKind::AttributeError {
                        name: n.as_code().into(),
                        object: format!(
                            "\"{}\"",
                            self.infer_primary_target(t, false)
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

    fn maybe_partial_aug_assignment(
        &self,
        target: &Target,
        aug_assign: AugAssign,
        right: &Inferred,
        lookup_and_execute: impl Fn(Inferred) -> Inferred,
    ) -> Option<()> {
        let name_index = match target {
            Target::Name(name_def) => name_def.name_index(),
            Target::NameExpression(_, name_def) => {
                let name_index = name_def.name_index();
                let p = NodeRef::new(self.file, name_index).point();
                let specific = p.maybe_calculated_and_specific()?;
                debug_assert!(p.is_name_of_name_def_like(), "{specific:?}");
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
        } else if specific.is_partial() {
            let left_inf = maybe_partial_node_ref.expect_inferred(self.i_s);
            lookup_and_execute(left_inf);
            return Some(());
        } else {
            return None;
        };
        let mut right_t = right.as_type(self.i_s);
        if right_t.is_any() {
            right_t = self.i_s.db.python_state.list_of_any.clone()
        }
        let class = right_t.maybe_class(self.i_s.db);
        if class.is_none_or(|cls| cls.node_ref != wanted) {
            let left_inf = maybe_partial_node_ref.expect_inferred(self.i_s);
            lookup_and_execute(left_inf);
            return Some(());
        }
        if matches!(
            class.unwrap().nth_type_argument(self.i_s.db, 0),
            Type::Any(AnyCause::UnknownTypeParam)
        ) {
            // This adds an empty list again, which should be fine.
            return Some(());
        }
        if point.partial_flags().nullable && !self.i_s.db.project.strict_optional_partials() {
            self.save_narrowed_partial_target(target, right_t.clone());
            right_t.union_in_place(Type::None)
        }

        maybe_partial_node_ref.insert_type(right_t);
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
                let module_point = NodeRef::new(self.file, 0).point();
                if !module_point.calculating() && !module_point.calculated() {
                    let result = self.file.ensure_module_symbols_flow_analysis(self.i_s.db);
                    debug_assert_eq!(result, Ok(()));
                    debug_assert!(to_annot_expr.point().calculated());
                    if to_annot_expr.point().calculated() {
                        return true;
                    }
                }
                self.infer_assignment_right_side(right_side, &mut ResultContext::ValueExpected)
                    .as_type(self.i_s)
            } else {
                annotation_ref.add_issue(
                    self.i_s,
                    IssueKind::WithoutInitializerAndType {
                        kind: match annotation_ref.point().maybe_specific() {
                            Some(Specific::AnnotationOrTypeCommentClassVar) => "ClassVar",
                            Some(Specific::AnnotationOrTypeCommentFinal) => "Final",
                            _ => {
                                recoverable_error!("Got unknown initializer {annotation_ref:?}");
                                "<unknown>"
                            }
                        },
                    },
                );
                Type::ERROR
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
                yield_type: Type::ERROR,
                send_type: Some(Type::ERROR),
                return_type: Some(Type::ERROR),
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
                        |issue| from.maybe_add_issue(i_s, issue),
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
                let (iter_result, yields) = self.infer_yield_from_details(yield_from);
                generator.yield_type.error_if_not_matches(
                    i_s,
                    &yields,
                    |issue| from.maybe_add_issue(i_s, issue),
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
                    if let Some(expected_send_type) = &generator.send_type
                        && let Some(got_send_type) = &other.send_type
                        && !expected_send_type
                            .is_simple_sub_type_of(i_s, got_send_type)
                            .bool()
                    {
                        from.add_issue(
                            i_s,
                            IssueKind::YieldFromIncompatibleSendTypes {
                                got: got_send_type.format_short(i_s.db),
                                expected: expected_send_type.format_short(i_s.db),
                            },
                        );
                    }
                    if let Some(return_type) = other.return_type {
                        Inferred::from_type(return_type)
                    } else {
                        if result_context.expect_not_none() {
                            from.add_issue(i_s, IssueKind::DoesNotReturnAValue("Function".into()));
                            if i_s.db.mypy_compatible() {
                                return Inferred::new_any_from_error();
                            }
                        }
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

    fn infer_yield_from_details(&self, yield_from: YieldFrom) -> (Inferred, Inferred) {
        let from = NodeRef::new(self.file, yield_from.index());
        let expr_result = self.infer_expression(yield_from.expression());
        let added_iter_issue = Cell::new(false);
        let iter_result = expr_result.type_lookup_and_execute(
            self.i_s,
            self.file,
            "__iter__",
            &NoArgs::new(from),
            &mut ResultContext::ValueExpected,
            &|_| {
                if !added_iter_issue.get() {
                    added_iter_issue.set(true);
                    from.add_issue(
                        self.i_s,
                        IssueKind::YieldFromCannotBeApplied {
                            to: expr_result.format_short(self.i_s),
                        },
                    )
                }
            },
        );
        let yields = iter_result.type_lookup_and_execute_with_attribute_error(
            self.i_s,
            from,
            "__next__",
            &NoArgs::new(from),
            &mut ResultContext::ValueExpected,
        );
        (
            iter_result,
            yields.save_redirect(self.i_s, self.file, yield_from.index()),
        )
    }

    pub fn infer_yield_from_expr(&self, yield_from: YieldFrom) -> Inferred {
        if let Some(inferred) = self.check_point_cache(yield_from.index()) {
            return inferred;
        }
        self.infer_yield_from_details(yield_from).1
    }

    pub fn infer_target(&self, target: Target, from_aug_assign: bool) -> Option<Inferred> {
        match target {
            Target::Name(name_def) => self.infer_name_target(name_def, from_aug_assign),
            Target::NameExpression(primary_target, _) => {
                self.infer_primary_target(primary_target, from_aug_assign)
            }
            Target::IndexExpression(t) if from_aug_assign => {
                self.infer_primary_target(t, from_aug_assign)
            }
            Target::Tuple(targets) => {
                let out: Option<Arc<[Type]>> = targets
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
        if name_def.as_code() == "__slots__" || name_def.as_code() == "_" {
            return None;
        }
        let check_fallback = |name_def: NameDef| {
            self.i_s
                .in_class_scope()
                .and_then(|cls| {
                    if cls.is_calculating_class_infos() {
                        return None;
                    }
                    cls.lookup(
                        self.i_s,
                        name_def.as_code(),
                        ClassLookupOptions::new(&|_| ()).with_ignore_self(),
                    )
                    .lookup
                    .into_maybe_inferred()
                    .and_then(|x| {
                        if let Some(ComplexPoint::TypeInstance(Type::Class(c))) =
                            x.maybe_complex_point(self.i_s.db)
                            && c.link == self.i_s.db.python_state.property_link()
                        {
                            // Properties can beo overwritten with the property value type as a
                            // normal variable. Here we make sure that the context is correct.
                            return cls
                                .instance()
                                .lookup(
                                    self.i_s,
                                    name_def.as_code(),
                                    InstanceLookupOptions::new(&|_| ())
                                        .with_skip_first_of_mro(self.i_s.db, cls),
                                )
                                .lookup
                                .into_maybe_inferred();
                        }
                        Some(x)
                    })
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
                if narrow
                    && let Some(result) = self.maybe_lookup_narrowed_name(
                        name_index,
                        PointLink::new(self.file.file_index, first_index),
                    )
                {
                    return Some(result);
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
                &Inferred::new_unsaved_complex(ComplexPoint::IndirectFinal(Arc::new(
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
                    false,
                ) {
                    new
                } else {
                    value.clone()
                };
                let override_class_infos = override_class.use_cached_class_infos(i_s.db);
                if let Some(t) = override_class_infos.undefined_generics_type.get()
                    && let Type::Enum(e) = t.as_ref()
                    && e.members
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
                    |c| c.name(i_s.db).into(),
                    None,
                );
                had_error = !matched;
                RedefinitionResult::TypeMismatch(had_error)
            },
        );
        if had_error && assign_kind.is_normal_assignment() {
            save(name_def.index(), ancestor_inf);
        } else {
            save(name_def.index(), value);
        }
    }

    pub(super) fn assign_to_name_def_simple(
        &self,
        name_def: NameDef,
        from: NodeRef,
        value: &Inferred,
        assign_kind: AssignKind,
    ) {
        self.assign_to_name_def(name_def, from, value, assign_kind, |index, value| {
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
    ) -> Option<RedefinitionResult> {
        debug!(
            "Assign to name {} ({}:#{}): {}",
            name_def.as_code(),
            self.file.qualified_name(self.i_s.db),
            self.file
                .byte_to_position_infos(self.i_s.db, name_def.start())
                .line_one_based(),
            value.debug_info(self.i_s.db),
        );
        let _indent = debug_indent();

        let i_s = self.i_s;
        if let Some(class) = i_s.in_class_scope() {
            let name_str = name_def.as_code();
            if class.node_ref != i_s.db.python_state.bare_type_node_ref()
                && !matches!(name_str, "__slots__" | "__match_args__")
                && !is_private(name_str)
                // This happens for NamedTuples and should probably not be here, but otherwise we
                // cannot do lookups.
                && !class.is_calculating_class_infos()
            {
                // Handle assignments in classes where the variable exists in a super class.
                let ancestor_lookup = class.instance().lookup(
                    i_s,
                    name_str,
                    InstanceLookupOptions::new(&|_| ()).with_skip_first_of_mro(i_s.db, class),
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
                        &value.clone().avoid_implicit_literal(i_s),
                        &ancestor_lookup,
                        &ancestor_inf,
                        save,
                    );
                    return None; // TODO?
                }
            }
        }
        let result = Cell::new(None);
        self.assign_to_name_def_or_self_name_def(
            name_def,
            from,
            value,
            assign_kind,
            |save_to_index, inf| {
                self.add_initial_name_definition(name_def);
                save(save_to_index, inf)
            },
            None,
            |first_name_link, declaration_t| {
                let current_t = value.as_cow_type(i_s);
                self.narrow_or_widen_name_target(first_name_link, declaration_t, &current_t, || {
                    let allow_redefinitions = self.allow_redefinitions_in_specific_scope();
                    let r = if (allow_redefinitions || matches!(*current_t, Type::None))
                        && (NodeRef::from_link(self.i_s.db, first_name_link)
                            .point()
                            .can_be_redefined()
                            // Star imports are defined in different files
                            || first_name_link.file != self.file.file_index
                                && allow_redefinitions)
                    {
                        RedefinitionResult::RedefinitionAllowed
                    } else {
                        RedefinitionResult::TypeMismatch(self.check_assignment_type(
                            value,
                            declaration_t,
                            from,
                            None,
                            assign_kind,
                        ))
                    };
                    result.set(Some(r));
                    r
                })
            },
        );
        result.into_inner()
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
            |issue| from.maybe_add_issue(self.i_s, issue),
            |error_types| {
                had_error = true;
                let ErrorStrs { expected, got } = error_types.as_boxed_strs(self.i_s.db);
                Some(if let Some(base_class) = base_class.as_ref() {
                    IssueKind::IncompatibleAssignmentInSubclass {
                        base_class: base_class.name(self.i_s.db).into(),
                        got,
                        expected,
                    }
                } else {
                    match assign_kind {
                        AssignKind::Import => IssueKind::IncompatibleImportAssignment {
                            name: from.as_code().into(),
                            got,
                            expected,
                        },
                        AssignKind::Pattern => {
                            IssueKind::IncompatiblePatternAssignment { got, expected }
                        }
                        _ => IssueKind::IncompatibleAssignment { got, expected },
                    }
                })
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
                        &declaration_t.avoid_implicit_literal_cow(i_s.db),
                        from,
                        None,
                        assign_kind,
                    );
                    return;
                }
                if declaration_t.type_of_protocol_to_type_of_protocol_assignment(i_s, value) {
                    from.add_issue(
                        self.i_s,
                        IssueKind::OnlyConcreteClassAllowedWhereTypeExpectedForVariable {
                            type_: declaration_t.format_short(i_s.db),
                        },
                    );
                    return;
                }

                if matches!(
                    assign_kind,
                    AssignKind::Annotation { .. } | AssignKind::TypeAlias
                ) {
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
        let set_defaultdict_type = |name_node_ref: NodeRef, t: Type| {
            // It feels very weird that we're saving on the index before the defaultdict
            // definition, but it seems to be fine since this should either be a `,` for tuple
            // assignments or a `.` for self assignments or a star_targets / single_target / walrus
            // that is not used.
            let save_to = name_node_ref.add_to_node_index(NAME_DEF_TO_DEFAULTDICT_DIFF);
            debug!("Set defaultdict type to {}", t.format_short(i_s.db));
            debug_assert!(
                !save_to.point().calculated()
                    || save_to.point().maybe_calculated_and_specific()
                        == Some(Specific::PartialNone),
                "{save_to:?}"
            );
            save_to.insert_type(t)
        };
        let check_assign_including_partials = |first_index, original: &Inferred, base_class| {
            if let Some(saved_node_ref) = original.maybe_saved_node_ref(i_s.db) {
                let point = saved_node_ref.point();
                let maybe_overwrite_partial = |class_node_ref| {
                    let mut partial_flags = point.partial_flags();
                    if partial_flags.finished {
                        return false;
                    }
                    let t = value.as_cow_type(i_s);
                    if t.maybe_class(i_s.db)
                        .is_some_and(|c| c.node_ref == class_node_ref)
                    {
                        let mut t = t.into_owned();
                        if t.has_any_with_unknown_type_params(i_s.db) {
                            saved_node_ref.finish_partial_with_annotation_needed(i_s.db)
                        } else {
                            if partial_flags.nullable && !i_s.db.project.strict_optional_partials()
                            {
                                t.union_in_place(Type::None);
                                narrow(PointLink::new(self.file.file_index, first_index), &t);
                            }
                            saved_node_ref.insert_type(t)
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
                        if let Some(p) = value.maybe_new_nullable_partial_point(i_s, |t| {
                            set_defaultdict_type(saved_node_ref, t)
                        }) {
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
                            let new_declaration = value_t
                                .avoid_implicit_literal_cow(i_s.db)
                                .simplified_union(i_s, &Type::None);
                            narrow(
                                PointLink::new(self.file.file_index, first_index),
                                &new_declaration,
                            );
                            saved_node_ref.insert_type(new_declaration);
                        }
                        return;
                    }
                    Some(Specific::PartialList) => {
                        maybe_overwrite_partial(i_s.db.python_state.list_node_ref())
                    }
                    Some(Specific::PartialDict) => {
                        maybe_overwrite_partial(i_s.db.python_state.dict_node_ref())
                    }
                    Some(Specific::PartialSet) => {
                        maybe_overwrite_partial(i_s.db.python_state.set_node_ref())
                    }
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
                } else if matches!(assign_kind, AssignKind::Annotation { .. })
                    // Mypy does not allow assigning two vars in the same scope with x: int
                    && !self.i_s.db.mypy_compatible()
                    && self
                        .infer_name_of_definition_by_index(first_index)
                        .as_cow_type(i_s)
                        .is_equal_type(i_s.db, &value.as_cow_type(i_s))
                {
                } else {
                    let mut node_ref = name_def_ref;
                    if self.i_s.db.mypy_compatible() {
                        // Mypy adds redefiniton errors onto the whole import instead of just the
                        // name.
                        match name_def.maybe_import() {
                            Some(NameImportParent::ImportFromAsName(i)) => {
                                if let Some(imp) = i.import_from() {
                                    node_ref = NodeRef::new(self.file, imp.index())
                                }
                            }
                            Some(NameImportParent::DottedAsName(i)) => {
                                node_ref = NodeRef::new(self.file, i.import().index())
                            }
                            _ => {}
                        };
                    }
                    self.add_redefinition_issue(
                        first_index,
                        name_def.as_code(),
                        lookup_self_attribute_in_bases.is_some(),
                        |issue| node_ref.add_issue(self.i_s, issue),
                    );
                }
            };

            let maybe_saved = self.follow_and_maybe_saved(first_index);
            let maybe_complex_def = maybe_saved.and_then(|n| n.maybe_complex());
            // This is mostly to make it clear that things like NewType/TypeVars are special
            // and cannot be redefined
            let is_special_def = || match maybe_complex_def {
                None
                | Some(
                    ComplexPoint::TypeInstance(_)
                    | ComplexPoint::IndirectFinal(_)
                    | ComplexPoint::FunctionOverload(_)
                    | ComplexPoint::TypeAlias(_),
                ) => false,
                Some(ComplexPoint::TypeVarLike(_)) => i_s.db.mypy_compatible(),
                Some(ComplexPoint::Class(_))
                    if !matches!(
                        NodeRef::new(self.file, first_index)
                            .expect_name()
                            .expect_type(),
                        TypeLike::ClassDef(_)
                    ) =>
                {
                    false
                }
                _ => true,
            };
            let assign_as_new_definition = match assign_kind {
                AssignKind::Annotation { .. } | AssignKind::TypeAlias => true,
                AssignKind::Import => {
                    // Imports are a bit special since most of the time they are allowed and not
                    // considered a redefinition in Mypy and then there's unresolved imports and
                    // imports of files that are considered to be redefinitions.
                    if value.is_unsaved_module_not_found() {
                        true
                    } else {
                        maybe_saved.is_some_and(|n| {
                            if let Some(complex) = maybe_complex_def {
                                return is_special_def()
                                    && !matches!(
                                        complex,
                                        ComplexPoint::Class(_)
                                            | ComplexPoint::FunctionOverload(_)
                                            | ComplexPoint::TypeAlias(_)
                                    );
                            }
                            let p = n.point();
                            p.kind() == PointKind::FileReference
                                && matches!(
                                    value.as_cow_type(i_s).as_ref(),
                                    Type::Module(f) if *f != p.file_index()
                                )
                        })
                    }
                }
                _ => is_special_def(),
            };
            if assign_as_new_definition {
                add_redefinition_issue();
                // Nothing needed to assign anymore, the original definition was already assigned.
                return;
            }
            if let Some(lookup_in_bases) = lookup_self_attribute_in_bases {
                let lookup_details = lookup_in_bases();
                if let Some(inf) = lookup_details.lookup.into_maybe_inferred() {
                    if lookup_details.attr_kind == AttributeKind::Final
                        && (self.is_initialized(first_index)
                            || !self.self_in_init_function(name_def))
                    {
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
            // Walrus is special, because it relays values from the expression to the outer
            // expression.
            if self.i_s.db.run_cause == RunCause::LanguageServer
                && !matches!(assign_kind, AssignKind::Walrus)
            {
                // This information is only needed if we need to access it again and otherwise
                // irrelevant, because we only acccess the information of the first name def.
                save(name_def.index(), &original_inf);
            }
            check_assign_including_partials(first_index, &original_inf, None)
        } else {
            if let Some(lookup_in_bases) = lookup_self_attribute_in_bases {
                let lookup_details = lookup_in_bases();
                if lookup_details.lookup.is_some() {
                    return self.assign_name_with_info_from_base_class(
                        name_def,
                        from,
                        assign_kind,
                        lookup_details,
                        save,
                        check_assign_including_partials,
                    );
                }
            } else if let Some(star_imp) = self.lookup_from_star_import_with_node_index(
                name_def.as_code(),
                true,
                Some(name_def.index()),
                None,
            ) {
                let original = star_imp.as_inferred(self.i_s);
                match star_imp {
                    StarImportResult::Link(star_link) => {
                        check_assign_to_known_definition(star_link, &original, None);
                    }
                    StarImportResult::AnyDueToError => (),
                };

                save(
                    name_def.index(),
                    if self.allow_redefinitions_in_specific_scope() {
                        self.add_star_import_to_base_narrowing(name_def, original);
                        value
                    } else {
                        &original
                    },
                );
                return;
            }
            let value = match assign_kind {
                AssignKind::Normal | AssignKind::Walrus => {
                    value.avoid_implicit_literal_cow(self.i_s)
                }
                _ => Cow::Borrowed(value),
            };
            if assign_kind.is_normal_assignment() {
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
                    let point = self.point(name_def_index);
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
                            self.set_point(name_def_index, point.set_partial_flags(flags))
                        }
                    }

                    return;
                } else if let Some(inf) = value
                    .maybe_any_with_unknown_type_params(i_s, NodeRef::new(self.file, current_index))
                {
                    save(name_def.index(), &inf);
                    return;
                } else if lookup_self_attribute_in_bases.is_none()
                    && name_def.as_code() == "_"
                    && self.i_s.current_function().is_some()
                    && name_def.maybe_import().is_none()
                    && !self.flags().allow_redefinition
                {
                    save(name_def.index(), &Inferred::new_any(AnyCause::Todo));
                    return;
                }
            }
            if let Some(value_without_final) = value.remove_final(i_s) {
                save(name_def.index(), &value_without_final);
            } else {
                save(name_def.index(), &value);
            }
        }
    }

    fn assign_name_with_info_from_base_class<'x>(
        &self,
        name_def: NameDef,
        from: NodeRef,
        assign_kind: AssignKind,
        base_lookup: LookupDetails<'x>,
        save: impl FnOnce(NodeIndex, &Inferred),
        check_assign_including_partials: impl FnOnce(NodeIndex, &Inferred, Option<TypeOrClass<'x>>),
    ) {
        let base_inf = base_lookup.lookup.into_inferred();
        let i_s = self.i_s;
        match assign_kind {
            AssignKind::Annotation { specific: reason }
                if matches!(
                    base_lookup.class,
                    TypeOrClass::Class(c)
                    if c.node_ref == i_s.current_class().unwrap().node_ref
                ) =>
            {
                if reason == Some(Specific::AnnotationOrTypeCommentFinal) {
                    from.add_issue(self.i_s, IssueKind::CannotRedefineAsFinal);
                } else if let Some(link) = base_inf
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
            _ => (),
        }
        if base_lookup.attr_kind.is_final() {
            if let TypeOrClass::Class(c) = base_lookup.class {
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
                }) || !self.self_in_init_function(name_def)
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
                } else {
                    check_assign_including_partials(
                        name_def.name_index(),
                        &base_inf,
                        Some(base_lookup.class),
                    );
                }
            }
            save(
                name_def.index(),
                &Inferred::new_unsaved_complex(ComplexPoint::IndirectFinal(Arc::new(
                    base_inf.as_type(i_s),
                ))),
            );
        } else {
            if !base_lookup.attr_kind.is_overwritable() {
                from.add_issue(
                    i_s,
                    IssueKind::PropertyIsReadOnly {
                        class_name: base_lookup.class.name(i_s.db).into(),
                        property_name: name_def.as_code().into(),
                    },
                );
            }
            check_assign_including_partials(
                name_def.name_index(),
                &base_inf,
                Some(base_lookup.class),
            );
            // TODO maybe this is needed?
            //if matches!(assign_kind, AssignKind::Annotation { .. }) {
            //save(name_def.index(), value);
            //} else {
            save(name_def.index(), &base_inf);
            //}
        }
    }

    fn self_in_init_function(&self, name_def: NameDef) -> bool {
        func_of_self_symbol(self.file, name_def.name_index())
            .name_def()
            .as_code()
            == "__init__"
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
        let save_narrowed = Cell::new(true);
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
                    save_narrowed.set(
                        c.class(i_s.db)
                            .instance()
                            .check_set_descriptor_and_return_should_narrow(
                                i_s,
                                node_ref,
                                name_def.name(),
                                value,
                            )
                            & save_narrowed.get(),
                    );
                    continue;
                }
                Type::Dataclass(d) => {
                    let inst = Instance::new(d.class(i_s.db), None);
                    if d.options.frozen == Some(true) {
                        // For dataclass_transform there are dataclasses that are initialized by a
                        // metaclass and have an unknown frozen state. See also
                        // testDataclassTransformDirectMetaclassNeitherFrozenNorNotFrozen
                        let is_unknown = match inst
                            .lookup(i_s, name_str, InstanceLookupOptions::new(&|_| ()))
                            .class
                        {
                            TypeOrClass::Type(t) => matches!(
                                t.as_ref(),
                                Type::Dataclass(dc) if dc.options.frozen.is_none(),
                            ),
                            _ => false,
                        };
                        if !is_unknown {
                            save_narrowed.set(false);
                            property_is_read_only(d.class(i_s.db).name().into())
                        }
                    }
                    if let Some(expected) =
                        dataclass_converter_fields_lookup(d, i_s.db, name_def.as_code())
                    {
                        let got = value.as_cow_type(i_s);
                        if !expected.from.is_simple_super_type_of(i_s, &got).bool() {
                            from.add_issue(
                                i_s,
                                IssueKind::IncompatibleDataclassTransformConverterAssignment {
                                    got: got.format_short(i_s.db),
                                    expected: expected.from.format_short(i_s.db),
                                },
                            );
                        }
                    } else {
                        save_narrowed.set(
                            inst.check_set_descriptor_and_return_should_narrow(
                                i_s,
                                node_ref,
                                name_def.name(),
                                value,
                            ) & save_narrowed.get(),
                        );
                    }
                    continue;
                }
                Type::NamedTuple(nt) => {
                    if nt.search_param(i_s.db, name_def.as_code()).is_some() {
                        save_narrowed.set(false);
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
                        save_narrowed.set(false);
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
                    save_narrowed.set(false);
                    from.add_issue(i_s, IssueKind::InvalidAssignmentTarget);
                    continue;
                }
                Type::None if i_s.should_ignore_none_in_untyped_context() => continue,
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
                    ClassLookupOptions::new(&|issue| {
                        save_narrowed.set(false);
                        node_ref.add_issue(i_s, issue)
                    })
                    .with_origin(ApplyClassDescriptorsOrigin::AssignToClass),
                );
                if let Some(inf) = lookup_details.lookup.maybe_inferred()
                    && inf.as_cow_type(i_s).is_func_or_overload_not_any_callable()
                {
                    from.add_issue(i_s, IssueKind::CannotAssignToAMethod);
                }
                lookup = lookup_details.lookup;
                attr_kind = lookup_details.attr_kind;
            }
            lookup = lookup.or_else(|| {
                let result = t.lookup_with_first_attr_kind(
                    i_s,
                    node_ref.file,
                    name_str,
                    LookupKind::Normal,
                    &mut ResultContext::ValueExpected,
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
                save_narrowed.set(false);
            }
            declaration_t.error_if_not_matches(
                i_s,
                value,
                |issue| from.maybe_add_issue(i_s, issue),
                |error_types| {
                    save_narrowed.set(false);
                    let ErrorStrs { expected, got } = error_types.as_boxed_strs(i_s.db);
                    Some(IssueKind::IncompatibleAssignment { got, expected })
                },
            );
        }
        if assign_kind.is_normal_assignment()
            && save_narrowed.get()
            // It seems like on explicit Any Mypy does not narrow
            // TODO it should not narrow on all Any declaration, not just base
            && !matches!(base.as_ref(), Type::Any(AnyCause::Explicit))
        {
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
                self.assign_to_name_def(name_def, from, value, assign_kind, save);
            }
            Target::NameExpression(primary_target, name_def) => {
                if self.is_self(primary_target.first()) {
                    // TODO The func should ALWAYS exist, this is just a bug at the moment.
                    if let Some(func) = i_s.current_function()
                        && let FirstParamKind::Self_ = func.first_param_kind(self.i_s)
                        && let Some(in_class) = func.parent_class(self.i_s.db)
                    {
                        self.check_self_assign(
                            in_class,
                            primary_target,
                            name_def,
                            from,
                            value,
                            assign_kind,
                            save,
                        );
                        return;
                    }
                }
                let base = self.infer_primary_target_or_atom(primary_target.first());
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
                        let partial_flags = point.partial_flags();
                        if !partial_flags.finished {
                            let value_t = value.as_type(i_s).avoid_implicit_literal(i_s.db);
                            if specific == Specific::PartialDefaultDict {
                                let Some(ComplexPoint::TypeInstance(original_value)) = from
                                    .add_to_node_index(NAME_DEF_TO_DEFAULTDICT_DIFF)
                                    .maybe_complex()
                                else {
                                    unreachable!(
                                        "The defaultdict value type should always be defined"
                                    )
                                };
                                if !original_value.is_simple_same_type(i_s, &value_t).bool() {
                                    from.add_need_type_annotation_issue(i_s.db, specific);
                                    return;
                                }
                            }
                            let mut new_dict = new_class!(
                                match specific {
                                    Specific::PartialDict =>
                                        i_s.db.python_state.dict_node_ref().as_link(),
                                    _ => i_s.db.python_state.defaultdict_link(),
                                },
                                s_t.infer(i_s).as_type(i_s).avoid_implicit_literal(i_s.db),
                                value_t,
                            );
                            if new_dict.has_any_with_unknown_type_params(i_s.db) {
                                from.finish_partial_with_annotation_needed(i_s.db);
                                return;
                            }
                            debug!(
                                r#"Infer dict assignment partial for "{}" as "{}""#,
                                primary_target.as_code(),
                                new_dict.format_short(i_s.db)
                            );
                            if partial_flags.nullable && !i_s.db.project.strict_optional_partials()
                            {
                                self.save_narrowed_partial_primary_target_or_atom(
                                    primary_target.first(),
                                    new_dict.clone(),
                                );
                                new_dict.union_in_place(Type::None)
                            }
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

    fn is_self(&self, primary_target_first: PrimaryTargetOrAtom) -> bool {
        match primary_target_first {
            PrimaryTargetOrAtom::PrimaryTarget(_) => false,
            PrimaryTargetOrAtom::Atom(atom) => match atom.unpack() {
                AtomContent::Name(name) => matches!(
                    self.resolve_name_without_narrowing(name),
                    PointResolution::Param {
                        maybe_self: true,
                        ..
                    }
                ),
                _ => false,
            },
        }
    }

    fn check_self_assign(
        &self,
        in_class: Class,
        primary_target: PrimaryTarget,
        name_def: NameDef,
        from: NodeRef,
        value: &Inferred,
        assign_kind: AssignKind,
        save: impl FnOnce(NodeIndex, &Inferred),
    ) {
        let i_s = self.i_s;
        self.assign_to_name_def_or_self_name_def(
            name_def,
            from,
            value,
            assign_kind,
            |node_index, inf| {
                self.add_initial_name_definition(name_def);
                save(node_index, inf)
            },
            Some(&|| {
                in_class.instance().lookup(
                    i_s,
                    name_def.as_code(),
                    InstanceLookupOptions::new(&|issue| from.add_issue(i_s, issue))
                        .with_skip_first_self_variables(),
                )
            }),
            |_, declaration_t| {
                let current_t = value.as_cow_type(i_s);
                self.narrow_or_widen_self_target(primary_target, declaration_t, &current_t, || {
                    RedefinitionResult::TypeMismatch(self.check_assignment_type(
                        value,
                        declaration_t,
                        from,
                        None,
                        assign_kind,
                    ))
                })
            },
        );
        in_class.check_self_definition(i_s, |issue| from.add_issue(i_s, issue), name_def.as_code());
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
                    if matches!(union_part, Type::None)
                        && self.i_s.should_ignore_none_in_untyped_context()
                    {
                        continue;
                    }
                    let value_iterator = union_part.iter(
                        self.i_s,
                        IterInfos::new(value_node_ref, IterCause::AssignmentUnpack, &|issue| {
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
                    Inferred::new_list_of(self.i_s.db, Type::ERROR),
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
                (FixedLen(_), WithStar { .. }) => {
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
                let (is_empty, mut value) = value_iterator.unpack_starred_and_return_is_empty(
                    self.i_s,
                    after,
                    expect_tuple,
                    true,
                );
                if is_empty
                    && !expect_tuple
                    && self.infer_target(star_target.as_target(), false).is_some()
                {
                    // The type is already defined, just use any here, because the
                    // list really can be anything.
                    value = Inferred::from_type(self.i_s.db.python_state.list_of_any.clone())
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
                self.infer_expression_with_context(expr, result_context)
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
        self.infer_named_expression_with_context(named_expr, &mut ResultContext::ValueExpected)
    }

    pub fn infer_named_expression_with_context(
        &self,
        named_expr: NamedExpression,
        result_context: &mut ResultContext,
    ) -> Inferred {
        match named_expr.unpack() {
            NamedExpressionContent::Expression(expr) => {
                self.infer_expression_with_context(expr, result_context)
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

        if first_defined_name_of_multi_def(self.file, name_def.name_index()).is_none() {
            self.set_point(name_def.index(), Point::new_calculating());
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

        self.save_walrus(name_def, inf).1
    }

    pub(crate) fn check_for_redefinition(
        &self,
        name_def: NodeRef,
        add_issue: impl FnOnce(IssueKind),
    ) {
        let name_index = name_def.node_index + NAME_DEF_TO_NAME_DIFFERENCE;
        debug_assert_eq!(name_def.file_index(), self.file.file_index);
        if let Some(first) = first_defined_name_of_multi_def(self.file, name_index)
            && name_def.as_code() != "_"
        {
            self.add_redefinition_issue(first, name_def.as_code(), false, add_issue)
        }
    }

    pub(super) fn add_redefinition_issue(
        &self,
        first_index_of_definition: NodeIndex,
        name: &str,
        is_self_attribute: bool,
        add_issue: impl FnOnce(IssueKind),
    ) {
        let first_ref = NodeRef::new(self.file, first_index_of_definition);
        let mut line = first_ref.line_one_based(self.i_s.db);
        let i_s = self.i_s;
        if i_s.db.mypy_compatible() {
            // Mypy uses the line of the first decorator as the definition line. This feels
            // weird, because the name is what matters, so in our implementation we use a
            // different line.
            if let Some(decorated) = first_ref
                .maybe_name_of_function()
                .and_then(|func| func.maybe_decorated())
            {
                line = NodeRef::new(self.file, decorated.index()).line_one_based(self.i_s.db);
            }
        }
        let first_name_def = first_ref.expect_name().name_def().unwrap();
        let suffix = match first_name_def.maybe_import() {
            Some(_) => {
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
            ref_.expect_name_def();
        }
        self.check_point_cache(name_index - NAME_DEF_TO_NAME_DIFFERENCE)
            .and_then(|inf| inf.maybe_saved_node_ref(self.i_s.db))
    }

    pub fn save_walrus(
        &self,
        name_def: NameDef,
        inf: Inferred,
    ) -> (Option<RedefinitionResult>, Inferred) {
        let from = NodeRef::new(self.file, name_def.index());
        let narrowing_result =
            self.assign_to_name_def(name_def, from, &inf, AssignKind::Walrus, |index, value| {
                value.clone().save_redirect(self.i_s, self.file, index);
            });
        (
            narrowing_result,
            self.check_point_cache(name_def.index()).unwrap_or(inf),
        )
    }

    pub fn infer_expression(&self, expr: Expression) -> Inferred {
        self.infer_expression_with_context(expr, &mut ResultContext::ValueExpected)
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
        if result_context.expects_type_form()
            && !inferred
                .as_cow_type(self.i_s)
                .valid_in_type_form_assignment(self.i_s.db)
        {
            return self.compute_type_form_expr(expr);
        }
        inferred
    }

    pub fn infer_expression_part(&self, node: ExpressionPart) -> Inferred {
        self.infer_expression_part_with_context(node, &mut ResultContext::ValueExpected)
    }

    pub fn infer_expression_part_with_context(
        &self,
        node: ExpressionPart,
        result_context: &mut ResultContext,
    ) -> Inferred {
        match node {
            ExpressionPart::Atom(atom) => self.infer_atom(atom, result_context),
            ExpressionPart::Primary(primary) => self.infer_primary(primary, result_context),
            ExpressionPart::Sum(sum) => self.infer_operation(sum.as_operation(), result_context),
            ExpressionPart::Term(term) => {
                let op = term.as_operation();
                // Mypy special cases the case [...] * n where n is an int (see check_list_multiply
                // in mypy)
                if op.infos.operand == "*"
                    && let ExpressionPart::Atom(atom) = op.left
                    && matches!(atom.unpack(), AtomContent::List(_))
                    && self
                        .infer_expression_part(op.right)
                        .as_cow_type(self.i_s)
                        .is_simple_sub_type_of(self.i_s, &self.i_s.db.python_state.int_type())
                        .bool()
                {
                    return self.infer_atom(atom, result_context);
                }
                self.infer_operation(op, result_context)
            }
            ExpressionPart::Power(power) => {
                self.infer_operation(power.as_operation(), result_context)
            }
            ExpressionPart::ShiftExpr(shift) => {
                self.infer_operation(shift.as_operation(), result_context)
            }
            ExpressionPart::BitwiseOr(or) => {
                if let ResultContext::AssignmentNewDefinition {
                    assignment_definition,
                } = result_context
                    && let Some(union_type) = self.i_s.db.python_state.union_type()
                    && self.bitwise_or_might_be_a_type(or)
                {
                    debug!("Found a BitwiseOr expression that looks like a type alias");
                    let node_ref = NodeRef::from_link(self.i_s.db, *assignment_definition);
                    let assignment = node_ref.expect_assignment();
                    if let Some((_, None, _)) = assignment.maybe_simple_type_expression_assignment()
                    {
                        self.compute_explicit_type_assignment(assignment);
                        return Inferred::from_type(union_type);
                    }
                }
                self.infer_operation(or.as_operation(), result_context)
            }
            ExpressionPart::BitwiseAnd(and) => {
                self.infer_operation(and.as_operation(), result_context)
            }
            ExpressionPart::BitwiseXor(xor) => {
                self.infer_operation(xor.as_operation(), result_context)
            }
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
                        UnionValue::Multiple(_) => (), // I'm unsure if we need logic here to match Mypy
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
                    &mut ResultContext::ValueExpected,
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
                                &mut ResultContext::Await,
                            ),
                            from,
                            "\"await\"",
                            result_context.expect_not_none(),
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
                    self.file.maybe_add_issue(
                        self.i_s,
                        Issue::from_start_stop(
                            l.start(),
                            r.end(),
                            IssueKind::NonOverlappingEqualityCheck {
                                left_type: formatted_err.got,
                                right_type: formatted_err.expected,
                            },
                        ),
                    );
                }
                let from = NodeRef::new(self.file, op.index());
                left_inf.type_lookup_and_execute(
                    self.i_s,
                    from.file,
                    if matches!(cmp, ComparisonContent::Equals(..)) {
                        "__eq__"
                    } else {
                        "__ne__"
                    },
                    &KnownArgs::new(right_inf, from),
                    &mut ResultContext::ValueExpected,
                    &|_| {
                        debug!(
                            "__eq__ is normally accessible, but might not be \
                         for protocols and other things: {}",
                            left_inf.format_short(self.i_s)
                        )
                    },
                )
            }
            ComparisonContent::Is(l, _, r) | ComparisonContent::IsNot(l, _, r) => {
                if let Some(formatted_err) = needs_strict_equality_error() {
                    self.file.maybe_add_issue(
                        self.i_s,
                        Issue::from_start_stop(
                            l.start(),
                            r.end(),
                            IssueKind::NonOverlappingIdentityCheck {
                                left_type: formatted_err.got,
                                right_type: formatted_err.expected,
                            },
                        ),
                    );
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
                                &self
                                    .i_s
                                    .db
                                    .python_state
                                    .memoryview_type_with_any_generics(self.i_s.db),
                            )
                    };
                    let element_t = left_inf.as_cow_type(self.i_s);
                    let right_t = right_inf.as_cow_type(self.i_s);
                    // bytes are a bit special, we just try to mimic Mypy here.
                    // b'a' == bytesarray(b'a') is fine.
                    if !(overlaps_bytes_or_bytearray(&element_t)
                        && overlaps_bytes_or_bytearray(&right_t))
                        && let Some(container_t) = right_t.container_types(self.i_s.db)
                        && !self.is_strict_equality_comparison(&element_t, &container_t)
                    {
                        let formatted = format_got_expected(self.i_s.db, &element_t, &container_t);
                        self.file.maybe_add_issue(
                            self.i_s,
                            Issue::from_start_stop(
                                l.start(),
                                r.end(),
                                IssueKind::NonOverlappingContainsCheck {
                                    element_type: formatted.got,
                                    container_type: formatted.expected,
                                },
                            ),
                        );
                    }
                }
                self.infer_in_operator(from, &left_inf, right_inf)
            }
            ComparisonContent::Ordering(op) => self.infer_detailed_operation(
                op.index,
                op.infos,
                left_inf,
                right_inf,
                &mut ResultContext::ValueExpected,
            ),
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
            let mapping_node_ref = db.python_state.mapping_node_ref();
            if let Some(map1) = c1.class_in_mro(db, mapping_node_ref)
                && let Some(map2) = c2.class_in_mro(db, mapping_node_ref)
            {
                return self.is_strict_equality_comparison(
                    &map1.nth_type_argument(db, 0),
                    &map2.nth_type_argument(db, 0),
                ) && self.is_strict_equality_comparison(
                    &map1.nth_type_argument(db, 1),
                    &map2.nth_type_argument(db, 1),
                );
            }
        }
        if let Type::Tuple(tup1) = left_t.as_ref()
            && let Type::Tuple(tup2) = right_t.as_ref()
            && let TupleArgs::ArbitraryLen(inner1) = &tup1.args
            && let TupleArgs::ArbitraryLen(inner2) = &tup2.args
        {
            return self.is_strict_equality_comparison(inner1, inner2);
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
            &|issue| from.add_issue(i_s, issue),
            &mut |r_type, lookup_result| {
                if let Some(method) = lookup_result.lookup.into_maybe_inferred() {
                    for l_type in left_inf.as_cow_type(i_s).iter_with_unpacked_unions(i_s.db) {
                        let had_local_error = Cell::new(false);
                        method.execute_with_details(
                            i_s,
                            &KnownArgs::new(&Inferred::from_type(l_type.clone()), from),
                            &mut ResultContext::ValueExpected,
                            OnTypeError::new(&|_, _, _, _| {
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
                                from.file,
                                "__iter__",
                                LookupKind::OnlyType,
                                &mut ResultContext::ValueExpected,
                                &|issue| from.add_issue(i_s, issue),
                                &|_| {
                                    let right = right_inf.format_short(i_s);
                                    from.add_issue(i_s, IssueKind::UnsupportedIn { right })
                                },
                            )
                            .into_inferred()
                            .execute(i_s, &NoArgs::new(from))
                            .type_lookup_and_execute_with_attribute_error(
                                i_s,
                                from,
                                "__next__",
                                &NoArgs::new(from),
                                &mut ResultContext::ValueExpected,
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
            let (params, _) = lambda.unpack();
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
            might_have_type_vars: true,
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
                    Some(Inferred::from_type(Type::Callable(Arc::new(c))))
                } else {
                    None
                }
            })
            .flatten()
            .unwrap_or_else(|| {
                let (params, expr) = lambda.unpack();
                check_defaults();
                let result = self.flow_analysis_for_lambda_body(expr, &mut ResultContext::Unknown);
                let c = CallableContent::new_simple(
                    None,
                    None,
                    PointLink::new(self.file.file_index, lambda.index()),
                    self.i_s.db.python_state.empty_type_var_likes.clone(),
                    CallableParams::new_simple(params.map(to_callable_param).collect()),
                    result.as_type(self.i_s),
                );
                Inferred::from_type(Type::Callable(Arc::new(c)))
            })
    }

    fn infer_operation(&self, op: Operation, result_context: &mut ResultContext) -> Inferred {
        let context = if result_context.has_explicit_type() && op.infos.operand != "%" {
            // Pass on the context to each side. I'm not sure that's correct, but it's necessary at
            // least for list additions. However it's wrong for `"%s" % ...`.
            &mut *result_context
        } else {
            &mut ResultContext::ValueExpected
        };
        let left = self.infer_expression_part_with_context(op.left, context);
        let right = self.infer_expression_part_with_context(op.right, context);
        self.infer_detailed_operation(op.index, op.infos, left, &right, result_context)
    }

    fn infer_detailed_operation(
        &self,
        error_index: NodeIndex,
        op_infos: OpInfos,
        left: Inferred,
        right: &Inferred,
        result_context: &mut ResultContext,
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
                &|issue| from.add_issue(i_s, issue),
                &mut |l_type, lookup_result| {
                    if op_infos.operand == "%"
                        && l_type.is_allowed_as_literal_string(false)
                        && right
                            .as_cow_type(i_s)
                            .is_literal_string_only_argument_for_string_percent_formatting()
                    {
                        add_to_union(Inferred::from_type(Type::LiteralString { implicit: true }));
                        return;
                    }

                    let left_op_method = lookup_result.lookup.into_maybe_inferred();
                    for r_type in right.as_cow_type(i_s).iter_with_unpacked_unions(i_s.db) {
                        match r_type {
                            Type::Any(cause) => {
                                return add_to_union(Inferred::new_any(*cause));
                            }
                            Type::Literal(literal) => {
                                if let Some(result) = l_type.try_operation_against_literal(
                                    i_s.db,
                                    op_infos.operand,
                                    literal,
                                    &|issue| from.add_issue(i_s, issue),
                                ) {
                                    add_to_union(Inferred::from_type(result));
                                    continue;
                                }
                            }
                            Type::LiteralString { .. } => {
                                if let Some(result) =
                                    l_type.try_operation_against_literal_string(op_infos.operand)
                                {
                                    add_to_union(Inferred::from_type(result));
                                    continue;
                                }
                            }
                            _ => (),
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
                                        from.file,
                                        op_infos.reverse_magic_method,
                                        LookupKind::OnlyType,
                                        result_context,
                                        &|issue| from.add_issue(i_s, issue),
                                        &|_| {},
                                    )
                                    .into_maybe_inferred(),
                            ),
                        };

                        let l_defined_in = Some(&lookup_result.class);
                        let get_strategy = || {
                            // Check for shortcuts first (in Mypy it's called
                            // `op_methods_that_shortcut`)
                            if op_infos.shortcut_when_same_type
                                && let Some(left_instance) = l_type.maybe_class(i_s.db)
                                && let Some(right_instance) = r_type.maybe_class(i_s.db)
                                && left_instance.node_ref == right_instance.node_ref
                            {
                                return LookupStrategy::ShortCircuit;
                            }
                            // If right is a sub type of left, Python and Mypy execute right first
                            if r_type.is_simple_sub_type_of(i_s, l_type).bool()
                                && let Some(TypeOrClass::Class(l_class)) = l_defined_in
                                && let Some(TypeOrClass::Class(r_class)) = r_defined_in
                                && l_class.node_ref != r_class.node_ref
                            {
                                return LookupStrategy::ReverseThenNormal;
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
                                result_context,
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
                            let issue = if left_op_method.is_none()
                                && (right_op_method.is_none()
                                    || matches!(strategy, LookupStrategy::ShortCircuit))
                            {
                                if matches!(l_type, Type::None)
                                    && i_s.should_ignore_none_in_untyped_context()
                                {
                                    return Inferred::new_any_from_error();
                                }
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
                            had_error |= from.maybe_add_issue(i_s, issue);
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
        primary_method: Primary<'file>,
        maybe_defaultdict: bool,
    ) -> Option<(NodeRef<'_>, PrimaryOrAtom<'file>, Option<Inferred>)> {
        let primary_or_atom = primary_method.first();
        match primary_or_atom {
            PrimaryOrAtom::Primary(prim) => {
                let index = prim.index();
                if self.point(index).calculated() {
                    // This means that we have already tried so return.
                    return None;
                }
                match prim.second() {
                    PrimaryContent::Attribute(_) => {
                        // Only care about very specific cases here.
                        if !matches!(prim.first(), PrimaryOrAtom::Atom(_)) {
                            return None;
                        }
                        let mut inf = self.infer_primary(prim, &mut ResultContext::ValueExpected);
                        if !self.point(index).calculated() {
                            // This could have been set in infer_primary (especially in
                            // language server mode)
                            inf = inf.save_redirect(self.i_s, self.file, index);
                        }
                        Some((
                            inf.maybe_saved_node_ref(self.i_s.db)?,
                            primary_or_atom,
                            None,
                        ))
                    }
                    PrimaryContent::GetItem(getitem) => {
                        if maybe_defaultdict {
                            // This is for defaultdicts
                            let (base, p_before, _) =
                                self.infer_potential_partial_base(prim, false)?;
                            match base.point().maybe_specific()? {
                                Specific::PartialDefaultDictWithList
                                | Specific::PartialDefaultDictWithSet => {
                                    let s = SliceType::new(self.file, prim.index(), getitem);
                                    Some((base, p_before, Some(s.infer(self.i_s))))
                                }
                                _ => None,
                            }
                        } else {
                            None
                        }
                    }
                    PrimaryContent::Execution(_) => None,
                }
            }
            PrimaryOrAtom::Atom(atom) => Some((
                self.infer_atom(atom, &mut ResultContext::ValueExpected)
                    .maybe_saved_node_ref(self.i_s.db)?,
                primary_or_atom,
                None,
            )),
        }
    }

    fn try_to_infer_partial_from_primary(&self, primary: Primary) -> Option<Type> {
        let PrimaryContent::Execution(execution) = primary.second() else {
            return None;
        };
        let PrimaryOrAtom::Primary(primary_method) = primary.first() else {
            return None;
        };
        let PrimaryContent::Attribute(method_name) = primary_method.second() else {
            return None;
        };
        let i_s = self.i_s;
        let (base, primary_or_atom, defaultdict_key) =
            self.infer_potential_partial_base(primary_method, true)?;
        let first_arg_as_t = || {
            let args = SimpleArgs::new(*i_s, self.file, primary.index(), execution);
            let arg = args.maybe_single_positional_arg(i_s, &mut ResultContext::ValueExpected)?;
            Some(arg.as_type(i_s).avoid_implicit_literal(i_s.db))
        };
        let save_partial = |mut resolved_partial: Type| {
            let point = base.point();
            if point.kind() != PointKind::Specific {
                // This is a nested partial like:
                //
                //     arr = []
                //     arr.append(arr.append(1))
                //
                return None;
            }
            let flags = point.partial_flags();
            if flags.finished {
                debug!(r#"Partial "{}" was already finished"#, primary.as_code());
                return None;
            }
            if resolved_partial.has_any_with_unknown_type_params(i_s.db) {
                base.finish_partial_with_annotation_needed(i_s.db);
                return Some(Type::None);
            }
            debug!(
                r#"Infer partial for "{}" as "{}""#,
                primary.as_code(),
                resolved_partial.format_short(i_s.db)
            );
            if flags.nullable && !i_s.db.project.strict_optional_partials() {
                self.save_narrowed_partial(primary_or_atom, resolved_partial.clone());
                resolved_partial.union_in_place(Type::None)
            }
            base.insert_type(resolved_partial);
            Some(Type::None)
        };
        let find_container_types = |unwrap_from_iterable| {
            let mut t = first_arg_as_t()?;
            if unwrap_from_iterable && !t.is_any() {
                t = t.mro(i_s.db).find_map(|(_, type_or_class)| {
                    if let TypeOrClass::Class(maybe_iterable_cls) = type_or_class
                        && maybe_iterable_cls.node_ref == i_s.db.python_state.iterable_node_ref()
                    {
                        return Some(maybe_iterable_cls.nth_type_argument(i_s.db, 0));
                    }
                    None
                })?;
            }
            Some(t)
        };
        let try_to_save = |partial_class_link, unwrap_from_iterable| {
            let t = find_container_types(unwrap_from_iterable)?;
            // None is not inferred, in some untyped contexts, because it only increases the false
            // positive rate.
            if matches!(t, Type::None) && i_s.should_ignore_none_in_untyped_context() {
                let point = base.point();
                let mut partial_flags = point.partial_flags();
                partial_flags.finished = true;
                base.set_point(point.set_partial_flags(partial_flags));
                Some(Type::None)
            } else {
                save_partial(new_class!(partial_class_link, t))
            }
        };
        let try_to_save_defaultdict = |container_partial_link, unwrap_from_iterable| {
            let t = find_container_types(unwrap_from_iterable)?;
            save_partial(new_class!(
                i_s.db.python_state.defaultdict_link(),
                defaultdict_key?.as_type(i_s).avoid_implicit_literal(i_s.db),
                new_class!(container_partial_link, t)
            ))
        };
        match base.point().maybe_specific() {
            Some(Specific::PartialList) => match method_name.as_code() {
                "append" => try_to_save(i_s.db.python_state.list_node_ref().as_link(), false),
                "extend" => try_to_save(i_s.db.python_state.list_node_ref().as_link(), true),
                _ => None,
            },
            Some(Specific::PartialDict) => match method_name.as_code() {
                "update" => {
                    let t = first_arg_as_t()?;
                    let dct_node_ref = i_s.db.python_state.dict_node_ref();
                    if t.is_any() {
                        save_partial(new_class!(dct_node_ref.as_link(), t.clone(), t))
                    } else if t
                        .maybe_class(i_s.db)
                        .is_some_and(|c| c.node_ref == dct_node_ref)
                    {
                        save_partial(t)
                    } else {
                        None
                    }
                }
                _ => None,
            },
            Some(Specific::PartialSet) => match method_name.as_code() {
                "add" | "discard" => {
                    try_to_save(i_s.db.python_state.set_node_ref().as_link(), false)
                }
                "update" => try_to_save(i_s.db.python_state.set_node_ref().as_link(), true),
                _ => None,
            },
            Some(Specific::PartialDefaultDictWithList) => match method_name.as_code() {
                "append" => {
                    try_to_save_defaultdict(i_s.db.python_state.list_node_ref().as_link(), false)
                }
                "extend" => {
                    try_to_save_defaultdict(i_s.db.python_state.list_node_ref().as_link(), true)
                }
                _ => None,
            },
            Some(Specific::PartialDefaultDictWithSet) => match method_name.as_code() {
                "add" | "discard" => {
                    try_to_save_defaultdict(i_s.db.python_state.set_node_ref().as_link(), false)
                }
                "update" => {
                    try_to_save_defaultdict(i_s.db.python_state.set_node_ref().as_link(), true)
                }
                _ => None,
            },
            _ => None,
        }
    }

    // Primary is not saved by this function, but can be saved by other stuff and to avoid
    // re-executing, we check the point cache here.
    check_point_cache_with!(pub infer_primary, Self::_infer_primary, Primary, result_context);
    fn _infer_primary(&self, primary: Primary, result_context: &mut ResultContext) -> Inferred {
        if let Some(inf) = self.maybe_lookup_narrowed_primary(primary) {
            return if self.i_s.db.run_cause == RunCause::LanguageServer {
                inf.save_redirect(self.i_s, self.file, primary.index())
            } else {
                inf
            };
        }
        let base = match self.try_to_infer_partial_from_primary(primary) {
            Some(t) => return Inferred::from_type(t),
            None => self.infer_primary_or_atom(primary.first()),
        };

        /*
         * TODO reenable this? see test testNewAnalyzerAliasToNotReadyNestedClass2
        debug!(
            "Infer primary {} as {}",
            primary.short_debug(),
            result.format_short(self.i_s)
        );
        */
        self.infer_primary_or_primary_t_content(
            &base,
            primary.index(),
            primary.second(),
            false,
            result_context,
        )
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
                let result = base
                    .lookup_with_result_context(
                        self.i_s,
                        node_ref,
                        name.as_str(),
                        LookupKind::Normal,
                        result_context,
                    )
                    .save_name(
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
                    .unwrap_or_else(Inferred::new_any_from_error);
                if self.i_s.db.project.flags.disallow_deprecated {
                    result.add_issue_if_deprecated(self.i_s.db, None, |issue| {
                        self.add_issue(name.index(), issue)
                    })
                }
                result
            }
            PrimaryContent::Execution(details) => {
                self.primary_execute(base, node_index, details, result_context)
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

    fn primary_execute(
        &self,
        base: &Inferred,
        node_index: NodeIndex,
        details: ArgumentsDetails,
        result_context: &mut ResultContext,
    ) -> Inferred {
        let f = self.file;
        let args = SimpleArgs::new(*self.i_s, f, node_index, details);
        base.execute_with_details(
            self.i_s,
            &args,
            result_context,
            OnTypeError::new(&on_argument_type_error),
        )
    }

    pub fn infer_primary_or_atom(&self, p: PrimaryOrAtom) -> Inferred {
        match p {
            PrimaryOrAtom::Primary(primary) => {
                self.infer_primary(primary, &mut ResultContext::ValueExpected)
            }
            PrimaryOrAtom::Atom(atom) => self.infer_atom(atom, &mut ResultContext::ValueExpected),
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
            Name(n) => {
                let result = self.infer_name_reference(n);
                let mut should_save = self.i_s.db.run_cause == RunCause::LanguageServer;
                if i_s.db.project.flags.disallow_deprecated {
                    result.add_issue_if_deprecated(
                        i_s.db,
                        Some(NodeRef::new(self.file, n.index())),
                        |issue| {
                            self.add_issue(n.index(), issue);
                            should_save = true;
                        },
                    );
                }
                return if should_save
                    && !self.point(atom.index()).calculated()
                    // Avoid saving cycles, so that they are treated the same in all modes (easier
                    // for consistent test results).
                    && result.maybe_specific(self.i_s.db) != Some(Specific::Cycle)
                {
                    // This information is needed when doing goto/completions
                    result.save_redirect(i_s, self.file, atom.index())
                } else {
                    result
                };
            }
            Int(i) => return check_literal(result_context, i_s, i.index(), Specific::IntLiteral),
            Float(_) => Specific::Float,
            Complex(_) => Specific::Complex,
            Strings(strings) => match self.process_str_literal(strings) {
                ProcessedStrings::Literal(s) => {
                    return check_literal(result_context, i_s, s.index(), Specific::StringLiteral);
                }
                ProcessedStrings::LiteralString => {
                    return Inferred::from_type(Type::LiteralString { implicit: true });
                }
                ProcessedStrings::WithFStringVariables => Specific::String,
            },
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
                    StarLikeExpressionIterator::Empty => Type::Any(AnyCause::UnknownTypeParam),
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
                    .save_redirect(i_s, self.file, atom.index());
            }
            GeneratorComprehension(comp) => {
                return self.infer_generator_comprehension(comp, result_context);
            }
            YieldExpr(yield_expr) => return self.infer_yield_expr(yield_expr, result_context),
            NamedExpression(named_expression) => {
                return self.infer_named_expression_with_context(named_expression, result_context);
            }
        };
        let point = Point::new_specific(specific, Locality::Todo);
        Inferred::new_and_save(self.file, atom.index(), point)
    }

    pub(super) fn process_str_literal<'x>(&self, strings: Strings<'x>) -> ProcessedStrings<'x> {
        let mut is_string_literal = true;
        for string in strings.iter() {
            if let StringType::FString(f) = string {
                is_string_literal &= self
                    .calc_fstring_content_diagnostics_and_return_is_string_literal(f.iter_content())
            }
        }
        if let Some(s) = strings.maybe_single_string_literal() {
            ProcessedStrings::Literal(s)
        } else if is_string_literal {
            ProcessedStrings::LiteralString
        } else {
            ProcessedStrings::WithFStringVariables
        }
    }

    pub(super) fn strings_to_type(&self, strings: Strings) -> Type {
        match self.process_str_literal(strings) {
            ProcessedStrings::Literal(s) => {
                if let Some(s) =
                    DbString::from_python_string(self.file.file_index, s.as_python_string())
                {
                    Type::Literal(Literal::new(LiteralKind::String(s)))
                } else {
                    self.i_s.db.python_state.str_type()
                }
            }
            ProcessedStrings::LiteralString => Type::LiteralString { implicit: true },
            ProcessedStrings::WithFStringVariables => self.i_s.db.python_state.str_type(),
        }
    }

    pub(super) fn infer_tuple_iterator<'x>(
        &self,
        iterator: impl ClonableTupleIterator<'x>,
        result_context: &mut ResultContext,
    ) -> Inferred {
        let mut gatherer = TupleGatherer::default();
        result_context.with_tuple_context_iterator(self.i_s, |tuple_context_iterator| {
            let add_from_stars = |gatherer: &mut TupleGatherer, inferred: Inferred, from_index| {
                gatherer.extend_from_inferred_iterator(
                    inferred.iter(
                        self.i_s,
                        NodeRef::new(self.file, from_index),
                        IterCause::VariadicUnpack,
                    ),
                    0,
                )
            };
            for (entry, expected) in iterator.clone().zip(tuple_context_iterator) {
                match entry {
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
        gatherer.into_tuple(self.i_s.db, || self.create_list_or_set_generics(iterator))
    }

    fn calc_fstring_content_diagnostics_and_return_is_string_literal<'x>(
        &self,
        iter: impl Iterator<Item = FStringContent<'x>>,
    ) -> bool {
        let mut is_string_literal = true;
        for content in iter {
            match content {
                FStringContent::FStringExpr(e) => {
                    let (expressions, spec) = e.unpack();
                    for expr in expressions.iter() {
                        is_string_literal &= self
                            .infer_expression(expr)
                            .as_cow_type(self.i_s)
                            .is_allowed_as_literal_string(true);
                    }
                    if let Some(spec) = spec {
                        is_string_literal &= self
                            .calc_fstring_content_diagnostics_and_return_is_string_literal(
                                spec.iter_content(),
                            );
                    }
                }
                FStringContent::FStringString(_) => (),
            }
        }
        is_string_literal
    }

    pub fn infer_primary_target(
        &self,
        primary_target: PrimaryTarget,
        use_narrows: bool,
    ) -> Option<Inferred> {
        if let Some(inferred) = self.check_point_cache(primary_target.index()) {
            return Some(inferred);
        }
        if use_narrows && let Some(inf) = self.maybe_lookup_narrowed_primary_target(primary_target)
        {
            return Some(inf);
        }
        let second = primary_target.second();
        if self.is_self(primary_target.first())
            && let PrimaryContent::Attribute(attr) = second
        {
            let i = attr.index();
            if self.point(i).calculated() {
                if let Some(first) = first_defined_name_of_multi_def(self.file, i) {
                    let point = self.point(first - NAME_DEF_TO_NAME_DIFFERENCE);
                    if point.calculated() && point.maybe_specific().is_some_and(|s| s.is_partial())
                    {
                        return None;
                    }
                } else {
                    // This is the initial definition of self. The definition is not defined at
                    // this point is probably just inferred to know its context (which is not
                    // known, because this is going to be the definition).
                    let had_issue = Cell::new(false);
                    let lookup = self
                        .i_s
                        .current_class()
                        .unwrap()
                        .instance()
                        .lookup(
                            self.i_s,
                            attr.as_code(),
                            InstanceLookupOptions::new(&|_| had_issue.set(true))
                                .without_object()
                                .with_skip_first_self_variables()
                                .with_avoid_inferring_return_types(),
                        )
                        .lookup;
                    if had_issue.get() {
                        return None;
                    } else {
                        return lookup.into_maybe_inferred();
                    }
                }
            }
        }
        let first = self.infer_primary_target_or_atom(primary_target.first());
        Some(
            self.infer_primary_or_primary_t_content(
                &first,
                primary_target.index(),
                second,
                true,
                &mut ResultContext::ValueExpected,
            )
            .save_redirect(self.i_s, self.file, primary_target.index()),
        )
    }

    pub fn infer_primary_target_or_atom(&self, t: PrimaryTargetOrAtom) -> Inferred {
        match t {
            PrimaryTargetOrAtom::Atom(atom) => {
                self.infer_atom(atom, &mut ResultContext::ValueExpected)
            }
            PrimaryTargetOrAtom::PrimaryTarget(p) => self
                .infer_primary_target(p, true)
                .unwrap_or_else(|| Inferred::new_any(AnyCause::Internal)),
        }
    }

    pub(super) fn assign_type_alias_name(&self, alias: TypeAlias) {
        let name_def = alias.name_def();
        self.assign_to_name_def_simple(
            name_def,
            NodeRef::new(self.file, name_def.index()),
            &Inferred::from_type(self.i_s.db.python_state.type_alias_type_type()),
            // This is not an actual annotation but generates similar errors, when e.g. multiple
            // annotation assignments are used for the same name
            AssignKind::TypeAlias,
        );
    }

    check_point_cache_with!(pub infer_name_reference, Self::_infer_name_reference, Name);
    fn _infer_name_reference(&self, name: Name) -> Inferred {
        self.infer_name_by_str(name.as_code(), name.index())
    }

    pub(super) fn infer_name_by_str(&self, name_str: &str, save_to_index: NodeIndex) -> Inferred {
        let resolved = self.resolve_name_by_str(name_str, save_to_index, |i_s, node_ref, next| {
            node_ref
                .file
                .inference(i_s)
                .maybe_lookup_narrowed_name(node_ref.node_index, next)
        });
        self.infer_point_resolution(resolved)
    }

    fn infer_point_resolution(&self, pr: PointResolution) -> Inferred {
        match pr {
            PointResolution::NameDef {
                node_ref,
                global_redirect,
            } => {
                if global_redirect {
                    self.infer_module_point_resolution(pr, |issue| {
                        debug!("TODO Add an error around module point resolution {issue:?}");
                        tracing::warn!("Ignored an error around module point resolution");
                    })
                } else {
                    node_ref
                        .file
                        .inference(self.i_s)
                        ._infer_name_def(node_ref.expect_name_def())
                }
            }
            PointResolution::Inferred(inferred) => inferred,
            PointResolution::Param { node_ref, .. } => {
                debug_assert_eq!(node_ref.file_index(), self.file.file_index());
                self.infer_param(node_ref.node_index)
            }
            PointResolution::GlobalOrNonlocalName(node_ref) => {
                if node_ref.file_index() != self.file.file_index() {
                    // This is typically a global in the module scope, which is completely useless.
                    let i_s = &InferenceState::new(self.i_s.db, node_ref.file);
                    let inference = node_ref.file.inference(i_s);
                    if let Err(()) = inference.ensure_module_symbols_flow_analysis() {
                        // It feels weird that we add this to the global node.
                        node_ref.add_issue(
                            self.i_s,
                            IssueKind::CannotDetermineType {
                                for_: node_ref.as_code().into(),
                            },
                        );
                        return Inferred::new_any_from_error();
                    }
                    return inference.infer_point_resolution(pr);
                }
                let g_or_n_ref = node_ref.global_or_nonlocal_ref();
                if g_or_n_ref.point().calculated() {
                    self.check_point_cache(g_or_n_ref.node_index).unwrap()
                } else {
                    let p = node_ref.point();
                    if p.specific() == Specific::AnyDueToError {
                        return Inferred::new_any_from_error();
                    }
                    debug_assert_eq!(p.specific(), Specific::GlobalVariable);
                    self.with_correct_context(true, |inference| {
                        inference.infer_name_by_str(node_ref.as_code(), g_or_n_ref.node_index)
                    })
                }
            }
            PointResolution::ModuleGetattrName(node_ref) => {
                let i_s = &InferenceState::new(self.i_s.db, node_ref.file);
                let inf = node_ref.infer_name_of_definition_by_index(i_s);
                inf.execute(
                    i_s,
                    &KnownArgsWithCustomAddIssue::new(
                        &Inferred::new_any_from_error(),
                        // Errors are reported when checking the file (the signature can only contain
                        // one positional argument)
                        &|_| false,
                    ),
                )
            }
        }
    }

    pub(super) fn infer_module_point_resolution(
        &self,
        pr: PointResolution,
        add_issue: impl Fn(IssueKind),
    ) -> Inferred {
        match pr {
            PointResolution::NameDef {
                node_ref,
                global_redirect,
            } => node_ref
                .file
                .inference(&InferenceState::new(self.i_s.db, node_ref.file))
                .with_correct_context(global_redirect, |inference| {
                    let ensure_flow_analysis = || {
                        if inference.ensure_module_symbols_flow_analysis().is_err()
                            && !inference.maybe_flow_analysis_not_needed_after_all(node_ref)
                        {
                            add_issue(IssueKind::CannotDetermineType {
                                for_: node_ref.as_code().into(),
                            });
                            return Some(Inferred::new_any_from_error());
                        }
                        None
                    };
                    let p = node_ref.name_ref_of_name_def().point();
                    if p.calculated()
                        && p.needs_flow_analysis()
                        // Stub files should not need narrowing in general. However it would be
                        // better to remove this line again.
                        && !self.file.is_stub()
                        && let Some(result) = ensure_flow_analysis()
                    {
                        return result;
                    }
                    let r = FLOW_ANALYSIS.with(|fa| {
                        fa.with_new_empty_without_unfinished_partial_checking(|| {
                            inference.infer_name_def(node_ref.expect_name_def())
                        })
                    });
                    if !r.unfinished_partials.is_empty() {
                        if let Some(result) = ensure_flow_analysis() {
                            return result;
                        }
                        process_unfinished_partials(self.i_s.db, r.unfinished_partials);
                        // In case where the partial is overwritten, we can just return the old Inferred,
                        // because it points to the correct place.
                    }
                    if let Some(ComplexPoint::WidenedType(w)) =
                        r.result.maybe_complex_point(self.i_s.db)
                    {
                        return Inferred::from_type(w.widened.clone());
                    }
                    r.result
                }),

            PointResolution::Inferred(inferred) => inferred,
            _ => self.infer_point_resolution(pr),
        }
    }

    fn maybe_flow_analysis_not_needed_after_all(&self, node_ref: NodeRef) -> bool {
        // In some cases where type definitions are involved flow analysis might not be needed.
        debug_assert_eq!(node_ref.file.file_index, self.file.file_index);
        node_ref
            .expect_name_def()
            .maybe_assignment_definition()
            .is_some_and(|assignment| {
                OtherDefinitionIterator::new(
                    &self.file.points,
                    node_ref.name_ref_of_name_def().node_index,
                )
                .is_single_definition()
                    && self
                        .file
                        .name_resolution_for_types(&InferenceState::new(self.i_s.db, node_ref.file))
                        .is_valid_type_assignment(assignment)
            })
    }

    pub fn check_point_cache(&self, i: NodeIndex) -> Option<Inferred> {
        if !matches!(self.i_s.mode, Mode::Normal) {
            return self
                .file
                .inference(&self.i_s.with_mode(Mode::Normal))
                .check_point_cache(i);
        }
        let resolved = self.resolve_point(i, |i_s, node_ref, next| {
            node_ref
                .file
                .inference(i_s)
                .maybe_lookup_narrowed_name(node_ref.node_index, next)
        })?;
        Some(self.infer_point_resolution(resolved))
    }

    #[inline]
    pub(super) fn with_correct_context<T>(
        &self,
        global_redirect: bool,
        callable: impl FnOnce(&Inference) -> T,
    ) -> T {
        if global_redirect {
            FLOW_ANALYSIS.with(|fa| {
                fa.with_new_empty_and_delay_further(self.i_s.db, || {
                    callable(
                        &self
                            .file
                            .inference(&InferenceState::new(self.i_s.db, self.file)),
                    )
                })
            })
        } else {
            callable(self)
        }
    }

    fn infer_param(&self, node_index: NodeIndex) -> Inferred {
        let name_def = NameDef::by_index(&self.file.tree, node_index);
        // Performance: This could be improved by not needing to lookup all the
        // parents all the time.
        match name_def.function_or_lambda_ancestor().unwrap() {
            FunctionOrLambda::Function(func_node) => {
                let func = Function::new_with_unknown_parent(
                    self.i_s.db,
                    NodeRef::new(self.file, func_node.index()),
                );

                let self_to_inferred = |is_classmethod: bool| {
                    let Some(cls) = self.i_s.current_class() else {
                        recoverable_error!("Expected a class in i_s because we're on a self param");
                        return Inferred::new_any(AnyCause::Internal);
                    };
                    if func.node_ref.node_index < cls.node_ref.node_index {
                        // If the function is defined before the class, the class is defined within
                        // the function and we're inferring it from inside.
                        let mut t = if let Some(cls) = func.class {
                            cls.as_type(self.i_s.db)
                        } else {
                            recoverable_error!(
                                "Expected a class in func because we're on a self param"
                            );
                            Type::Any(AnyCause::Internal)
                        };
                        if is_classmethod {
                            t = Type::Type(Arc::new(t))
                        }
                        Inferred::from_type(t)
                    } else if is_classmethod {
                        Inferred::from_type(self.i_s.db.python_state.type_of_self.clone())
                    } else {
                        Inferred::new_saved(self.file, node_index)
                    }
                };

                let specific = self.point(node_index).specific();
                if let Some(annotation) = name_def.maybe_param_annotation() {
                    self.use_cached_param_annotation(annotation)
                } else {
                    let new_any = |param_index| {
                        if let Some(usage) = func
                            .type_vars(self.i_s.db)
                            .find_untyped_param_type_var(func.as_link(), param_index)
                        {
                            return Type::TypeVar(usage);
                        }
                        if let Some(cls) = func.class
                            && let Some(usage) = cls
                                .type_vars(self.i_s)
                                .find_untyped_param_type_var(cls.as_link(), param_index)
                        {
                            return Type::TypeVar(usage);
                        }
                        Type::Any(AnyCause::Unannotated)
                    };
                    if specific == Specific::MaybeSelfParam {
                        match func.first_param_kind(self.i_s) {
                            FirstParamKind::Self_ => self_to_inferred(false),
                            FirstParamKind::ClassOfSelf => self_to_inferred(true),
                            FirstParamKind::InStaticmethod => Inferred::from_type(new_any(0)),
                        }
                    } else {
                        for (i, param) in func_node.params().iter().enumerate() {
                            if param.name_def().index() == name_def.index() {
                                return match param.kind() {
                                    ParamKind::Star => Inferred::from_type(
                                        self.i_s.db.python_state.tuple_of_unannotated_any.clone(),
                                    ),
                                    ParamKind::StarStar => Inferred::from_type(new_class!(
                                        self.i_s.db.python_state.dict_node_ref().as_link(),
                                        self.i_s.db.python_state.str_type(),
                                        new_any(i)
                                    )),
                                    _ => maybe_infer_pytest_param(
                                        self.i_s.db,
                                        name_def,
                                        func,
                                        func_node,
                                    )
                                    .unwrap_or_else(|| Inferred::from_type(new_any(i))),
                                };
                            }
                        }
                        unreachable!()
                    }
                }
            }
            FunctionOrLambda::Lambda(lambda) => lookup_lambda_param(self.i_s, lambda, node_index),
        }
    }

    pub fn infer_name_of_definition_by_index(&self, node_index: NodeIndex) -> Inferred {
        self.infer_name_of_definition(Name::by_index(&self.file.tree, node_index))
    }

    pub fn infer_name_of_definition(&self, name: Name) -> Inferred {
        let point = self.point(name.index());
        if point.calculated()
            && !point.is_name_of_name_def_like()
            && let Some(inf) = self.check_point_cache(name.index())
        {
            return inf;
        }
        self.infer_name_def(name.name_def().unwrap())
    }

    check_point_cache_with!(pub infer_name_def, Self::_infer_name_def, NameDef);
    fn _infer_name_def(&self, name_def: NameDef) -> Inferred {
        let defining_stmt = name_def.expect_defining_stmt();
        self.cache_defining_stmt(defining_stmt, NodeRef::new(self.file, name_def.index()));
        debug_assert!(self.point(name_def.index()).calculated(), "{name_def:?}",);
        self.infer_name_def(name_def)
    }

    fn cache_defining_stmt(&self, defining_stmt: DefiningStmt, name_def: NodeRef) {
        if std::cfg!(debug_assertions)
            && let Some(class) = self.i_s.current_class()
        {
            debug_assert!(
                matches!(class.generics(), Generics::Self_ { .. } | Generics::None,),
                "{defining_stmt:?} {class:?}",
            )
        }
        debug!(
            "Infer name {} of stmt ({}:#{})",
            name_def.as_code(),
            self.file.qualified_name(self.i_s.db),
            name_def.line_one_based(self.i_s.db),
        );
        match defining_stmt {
            DefiningStmt::FunctionDef(func_def) => {
                Function::new(
                    NodeRef::new(self.file, func_def.index()),
                    self.i_s.current_class(),
                )
                .cache_func_with_name_def(self.i_s, name_def, false);
            }
            DefiningStmt::ClassDef(cls) => cache_class_name(name_def, cls),
            DefiningStmt::Assignment(assignment) => {
                self.ensure_cached_assignment(assignment);
            }
            DefiningStmt::ImportName(import_name) => {
                self.cache_import_name(import_name);
            }
            DefiningStmt::ImportFromAsName(as_name) => {
                self.assign_import_from_only_particular_name_def(
                    as_name,
                    |name_def, pr, redirect_to_link| {
                        self.assign_to_import_from_name(name_def, pr, redirect_to_link)
                    },
                );
            }
            DefiningStmt::Walrus(walrus) => {
                self.infer_walrus(walrus, None);
            }
            DefiningStmt::ForStmt(for_stmt) => {
                name_def.set_point(Point::new_calculating());
                let (star_targets, star_exprs, _, _) = for_stmt.unpack();
                // Performance: We probably do not need to calculate diagnostics just for
                // calculating the names.
                self.cache_for_stmt_names(star_targets, star_exprs, false);
            }
            DefiningStmt::WithItem(w) => {
                self.cache_with_item(w, w.in_async_with_stmt());
            }
            DefiningStmt::TryStmt(try_stmt) => {
                for block in try_stmt.iter_blocks() {
                    match block {
                        TryBlockType::Except(except) => {
                            if let (Some(except_expr), _) = except.unpack() {
                                if let ExceptExpressionContent::WithNameDef(expr, name_def) =
                                    except_expr.unpack()
                                {
                                    let nr = NodeRef::new(self.file, name_def.index());
                                    if nr.point().calculating() {
                                        Inferred::new_cycle()
                                    } else {
                                        nr.set_point(Point::new_calculating());
                                        let inf = self.infer_expression(expr);
                                        Inferred::from_type(instantiate_except(
                                            self.i_s,
                                            &inf.as_cow_type(self.i_s),
                                        ))
                                    }
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
                            if let ExceptExpressionContent::WithNameDef(expr, name_def) =
                                except_expr.unpack()
                            {
                                let nr = NodeRef::new(self.file, name_def.index());
                                if nr.point().calculating() {
                                    Inferred::new_cycle()
                                } else {
                                    nr.set_point(Point::new_calculating());
                                    let inf = self.infer_expression(expr);
                                    Inferred::from_type(self.instantiate_except_star(
                                        name_def,
                                        &inf.as_cow_type(self.i_s),
                                    ))
                                }
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
            DefiningStmt::TypeAlias(type_alias) => self.assign_type_alias_name(type_alias),
            DefiningStmt::DelStmt(del_stmt) => {
                // This should basically only happen for self assignments where the del self is the
                // first defined name in the chain.
                // Apparently assigning any here is enough for everything to be working well.
                // Errors are raised in the proper places anyway, see test
                // `del_stmt_inference_of_self_name`.
                debug!("Assigning Any to del_stmt, because it wasn't properly type checked");
                name_def.set_point(Point::new_calculating());
                self.assign_any_to_del_stmts(del_stmt.targets());
            }
            DefiningStmt::Lambda(_)
            | DefiningStmt::Comprehension(_)
            | DefiningStmt::DictComprehension(_)
            | DefiningStmt::GlobalStmt(_)
            | DefiningStmt::NonlocalStmt(_) => {
                recoverable_error!(
                    "Why do we hit these defining stmts: -> assigning Any to {:?} in {}",
                    name_def,
                    self.file_path()
                );
                self.assign_to_name_def_simple(
                    name_def.expect_name_def(),
                    name_def,
                    &Inferred::new_any_from_error(),
                    AssignKind::Normal,
                )
            }
            DefiningStmt::MatchStmt(_) | DefiningStmt::Error(_) => {
                // This should basically only ever happen on weird error cases where errors are
                // added in other places. We assign Any to make sure
                self.assign_to_name_def_simple(
                    name_def.expect_name_def(),
                    name_def,
                    &Inferred::new_any_from_error(),
                    AssignKind::Normal,
                )
            }
        }
    }

    pub fn instantiate_except_star(&self, name_def: NameDef, t: &Type) -> Type {
        let result = gather_except_star(self.i_s, t);
        // When BaseException is used, we need a BaseExceptionGroup. Otherwise when every exception
        // inherits from Exception, ExceptionGroup is used.
        let is_base_exception_group = has_base_exception(self.i_s.db, &result);
        let group_node_ref = match is_base_exception_group {
            false => self.i_s.db.python_state.exception_group_node_ref(),
            true => self.i_s.db.python_state.base_exception_group_node_ref(),
        };
        if let Some(group_node_ref) = group_node_ref {
            new_class!(group_node_ref.as_link(), result)
        } else {
            self.add_issue(
                name_def.index(),
                IssueKind::StarExceptionWithoutTypingSupport,
            );
            Type::ERROR
        }
    }

    pub fn assign_any_to_del_stmts(&self, del_targets: DelTargets) {
        for d in del_targets.iter() {
            match d {
                DelTarget::Target(target) => {
                    self.assign_any_to_target(target, NodeRef::new(self.file, del_targets.index()))
                }
                DelTarget::DelTargets(del_targets) => self.assign_any_to_del_stmts(del_targets),
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
                base.iter(
                    self.i_s,
                    NodeRef::new(self.file, expr_part.index()),
                    IterCause::Iter,
                )
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
            let found = infer_dict_like(
                i_s,
                result_context,
                false,
                false,
                |matcher, key_t, value_t| {
                    let mut check = |expected_t: &Type, expr, part| {
                        let inf = self.infer_expression_with_context(
                            expr,
                            &mut ResultContext::new_known(expected_t),
                        );
                        let t = inf.as_cow_type(i_s);
                        if expected_t.is_super_type_of(i_s, matcher, &t).bool() {
                            Some(
                                matcher
                                    .replace_type_var_likes_for_unknown_type_vars(
                                        i_s.db, expected_t,
                                    )
                                    .into_owned()
                                    .avoid_implicit_literal(i_s.db),
                            )
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
                },
            );
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
        class: ClassNodeRef,
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
                        |issue| self.maybe_add_issue(comp_expr.index(), issue),
                        |error_types, _: &_| Some(on_mismatch(error_types)),
                    );
                    matcher
                        .replace_type_var_likes_for_unknown_type_vars(i_s.db, &inner_expected)
                        .into_owned()
                })
                .and_then(|result| result.ok())
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
        Inferred::from_type(t.make_generator_type(self.i_s.db, is_async, || Type::None))
    }

    check_point_cache_with!(pub infer_decorator, Self::_infer_decorator, Decorator);
    fn _infer_decorator(&self, decorator: Decorator) -> Inferred {
        if !self.has_frames() {
            // This is a bit special and might be considered a bug. It might happen because
            // decorators are inferred in a lazy way.
            return FLOW_ANALYSIS.with(|fa| {
                fa.with_frame_that_exports_widened_entries(self.i_s, || {
                    self._infer_decorator(decorator)
                })
            });
        }
        self.file
            .points
            .set(decorator.index(), Point::new_calculating());
        let expr = decorator.named_expression().expression();

        let is_untyped_and_non_mypy_compatible = |inf: &Inferred| {
            if self.i_s.db.project.should_infer_return_types()
                && let Some(node_ref) = inf.maybe_saved_node_ref(self.i_s.db)
                && let Some(func) = node_ref.maybe_function()
            {
                func.return_annotation().is_none()
            } else {
                false
            }
        };
        if let ExpressionContent::ExpressionPart(ExpressionPart::Primary(primary)) = expr.unpack()
            && let PrimaryContent::Execution(exec) = primary.second()
        {
            let base = self.infer_primary_or_atom(primary.first());
            if is_untyped_and_non_mypy_compatible(&base) {
                return Inferred::new_any(AnyCause::UntypedDecorator).save_redirect(
                    self.i_s,
                    self.file,
                    decorator.index(),
                );
            }
            if !self.point(primary.index()).calculated() {
                // Try to find dataclass_transform and if there isn't one use the normal inference
                if base.maybe_saved_specific(self.i_s.db)
                    == Some(Specific::TypingDataclassTransform)
                {
                    self.insert_dataclass_transform(primary, exec);
                } else {
                    self.primary_execute(
                        &base,
                        primary.index(),
                        exec,
                        &mut ResultContext::ValueExpected,
                    )
                    .save_redirect(self.i_s, self.file, primary.index());
                };
                debug_assert!(self.point(primary.index()).calculated());
            }
        }
        let mut i = self.infer_named_expression(decorator.named_expression());
        if is_untyped_and_non_mypy_compatible(&i) {
            i = Inferred::new_any(AnyCause::UntypedDecorator);
        }
        if self.file.points.get(decorator.index()).calculated() {
            // It is possible that the decorator causes flow analysis for the whole file. In this
            // case we simply return and do not save, because it was already saved.
            i
        } else {
            i.save_redirect(self.i_s, self.file, decorator.index())
        }
    }

    pub fn infer_deprecated_reason(&self, decorator: Decorator) -> Arc<Box<str>> {
        let expr = decorator.named_expression().expression();
        if let ExpressionContent::ExpressionPart(ExpressionPart::Primary(primary)) = expr.unpack()
            && let PrimaryContent::Execution(exec) = primary.second()
        {
            let args = SimpleArgs::new(*self.i_s, self.file, primary.index(), exec);
            if let Some(arg) = args.iter(self.i_s.mode).next()
                && let InferredArg::Inferred(inf) = arg.infer(&mut ResultContext::ValueExpected)
                && let Some(s) = inf.maybe_string_literal(self.i_s)
            {
                return Arc::new(s.as_str(self.i_s.db).into());
            }
        }
        Arc::new("<Could not infer deprecated reason>".into())
    }

    pub fn infer_pattern_dotted_name(&self, dotted: DottedPatternName) -> Inferred {
        match dotted.unpack() {
            DottedPatternNameContent::Name(name) => self.infer_name_reference(name),
            DottedPatternNameContent::DottedName(dotted_name, name) => {
                let result = self.infer_pattern_dotted_name(dotted_name);
                let node_ref = NodeRef::new(self.file, dotted.index());
                result
                    .lookup(self.i_s, node_ref, name.as_code(), LookupKind::Normal)
                    .into_inferred()
            }
        }
    }

    pub fn is_no_type_check(&self, decorated: Decorated) -> bool {
        let no_type_check_link = self.i_s.db.python_state.no_type_check_link();
        let mut is_no_type_check = false;
        // We cannot simply run an iter().any(..), because that would not infer some decorators.
        for decorator in decorated.decorators().iter() {
            is_no_type_check |=
                self.infer_decorator(decorator).maybe_saved_link() == Some(no_type_check_link)
        }
        is_no_type_check
    }
}

pub(super) enum ProcessedStrings<'db> {
    Literal(StringLiteral<'db>),
    LiteralString,
    WithFStringVariables,
}

pub fn instantiate_except(i_s: &InferenceState, t: &Type) -> Type {
    match t {
        // No need to check these here, this is done when calculating diagnostics
        Type::Type(t) => match t.as_ref() {
            inner @ Type::Class(..) => inner.clone(),
            _ => Type::ERROR,
        },
        Type::Any(cause) => Type::Any(*cause),
        Type::Tuple(content) => Inferred::gather_simplified_union(i_s, |add| match &content.args {
            TupleArgs::FixedLen(ts) => {
                for t in ts.iter() {
                    add(Inferred::from_type(instantiate_except(i_s, t)))
                }
            }
            TupleArgs::ArbitraryLen(t) => add(Inferred::from_type(instantiate_except(i_s, t))),
            TupleArgs::WithUnpack(w) => match &w.unpack {
                TupleUnpack::TypeVarTuple(_) => add(Inferred::new_any_from_error()),
                TupleUnpack::ArbitraryLen(t) => {
                    for t in w
                        .before
                        .iter()
                        .chain(std::iter::once(t))
                        .chain(w.after.iter())
                    {
                        add(Inferred::from_type(instantiate_except(i_s, t)))
                    }
                }
            },
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
            union.might_have_type_vars,
        )),
        _ => Type::ERROR,
    }
}

fn has_base_exception(db: &Database, t: &Type) -> bool {
    match t {
        Type::Class(c) => !c.class(db).is_exception(db),
        Type::Union(u) => u.iter().any(|t| has_base_exception(db, t)),
        Type::Any(_) => false,
        // Gathering the exceptions already makes sure we do not end up with arbitrary types here.
        Type::Never(_) => true,
        _ => {
            recoverable_error!("Expected there to be only classes/Any as base exceptions");
            false
        }
    }
}

fn gather_except_star(i_s: &InferenceState, t: &Type) -> Type {
    match t {
        Type::Type(t) => match t.as_ref() {
            inner @ Type::Class(c) => {
                let cls = c.class(i_s.db);
                if cls.is_base_exception_group(i_s.db) {
                    // Diagnostics are calculated when calculating diagnostics, not here.
                    Type::ERROR
                } else if cls.is_base_exception(i_s.db) {
                    inner.clone()
                } else {
                    Type::ERROR
                }
            }
            _ => Type::ERROR,
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
            union.might_have_type_vars,
        )),
        _ => Type::ERROR,
    }
}

fn get_generator_return_type(i_s: &InferenceState, had_issue: &impl Fn(), t: &Type) -> Type {
    match t {
        Type::Class(c) => {
            if c.link == i_s.db.python_state.generator_link() {
                c.class(i_s.db).nth_type_argument(i_s.db, 2)
            } else {
                had_issue();
                Type::ERROR
            }
        }
        Type::Any(cause) => Type::Any(*cause),
        Type::Union(union) => Type::simplified_union_from_iterators(
            i_s,
            union
                .iter()
                .map(|t| get_generator_return_type(i_s, had_issue, t)),
        ),
        _ => {
            had_issue();
            Type::ERROR
        }
    }
}

pub(crate) fn first_defined_name(file: &PythonFile, name_index: NodeIndex) -> NodeIndex {
    let mut point = file.points.get(name_index);
    if !point.calculated() || point.maybe_specific() != Some(Specific::NameOfNameDef) {
        // Happens e.g. for the definition of builtins.type (overwritten in python_state.rs)
        // Or definitions of names that look like self (e.g. in testInferAttributeInitializedToEmptyNonSelf)
        return name_index;
    }
    // Here we circle through multi definitions to find the first one.
    // Note that multi definition links loop, i.e. A -> B -> C -> A.
    loop {
        debug_assert!(point.calculated());
        debug_assert_eq!(point.specific(), Specific::NameOfNameDef);
        let next = point.node_index();
        point = file.points.get(next);
        if point.specific() == Specific::FirstNameOfNameDef {
            return next;
        }
    }
}

pub(crate) fn first_defined_name_of_multi_def(
    file: &PythonFile,
    name_index: NodeIndex,
) -> Option<NodeIndex> {
    // Returns the first definition, if the name_index is a later definition.
    let first = first_defined_name(file, name_index);
    (first != name_index).then_some(first)
}

pub(crate) fn await_(
    i_s: &InferenceState,
    inf: Inferred,
    from: NodeRef,
    no_lookup_cause: &'static str,
    expect_not_none: bool,
) -> Inferred {
    let t = get_generator_return_type(
        i_s,
        &|| {
            from.add_issue(
                i_s,
                IssueKind::IncompatibleTypes {
                    cause: "\"await\"",
                    got: inf.format_short(i_s),
                    expected: "Awaitable[Any]".into(),
                },
            )
        },
        inf.type_lookup_and_execute(
            i_s,
            from.file,
            "__await__",
            &NoArgs::new(from),
            &mut ResultContext::Await,
            &|t| {
                from.add_issue(
                    i_s,
                    IssueKind::IncompatibleTypes {
                        cause: no_lookup_cause,
                        got: t.format_short(i_s.db),
                        expected: "Awaitable[Any]".into(),
                    },
                );
            },
        )
        .as_cow_type(i_s)
        .as_ref(),
    );
    if matches!(t, Type::Never(_)) {
        FLOW_ANALYSIS.with(|fa| fa.mark_current_frame_unreachable())
    }
    if expect_not_none && matches!(t, Type::None) {
        from.add_issue(i_s, IssueKind::DoesNotReturnAValue("Function".into()));
        if i_s.db.mypy_compatible() {
            return Inferred::new_any_from_error();
        }
    }
    Inferred::from_type(t)
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
pub(crate) enum AssignKind {
    Normal, // a = 1
    Walrus,
    Annotation { specific: Option<Specific> }, // `a: int = 1` or `a = 1 # type: int
    TypeAlias,
    Import,
    AugAssign, // a += 1
    Pattern,   // case foo:
}

impl AssignKind {
    fn is_normal_assignment(self) -> bool {
        matches!(self, Self::Normal | Self::Walrus | Self::Pattern)
    }
}

pub(crate) enum StarImportResult {
    Link(PointLink),
    AnyDueToError,
}

impl StarImportResult {
    pub fn as_inferred(&self, i_s: &InferenceState) -> Inferred {
        match self {
            Self::Link(link) => {
                let node_ref = NodeRef::from_link(i_s.db, *link);
                node_ref.infer_name_of_definition_by_index(i_s)
            }
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
    context_params: &mut Arc<[CallableParam]>,
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
                            might_have_type_vars: true,
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
                            if let Some(n) = &p2.name
                                && n.as_str(i_s.db) == p.name_def().as_code()
                                && let Some(t) = p2.type_.maybe_type()
                            {
                                return Inferred::from_type(t.clone());
                            }
                        }
                        if p.kind() == ParamKind::PositionalOrKeyword
                            && let Some(p2) = c_params.get(i)
                            && let ParamType::PositionalOnly(t) = &p2.type_
                        {
                            return Inferred::from_type(t.clone());
                        }
                        // TODO here we should do proper matching for lambda params.
                        Inferred::new_any(AnyCause::FromError)
                    }
                    CallableParams::Any(cause) => Inferred::new_any(*cause),
                };
            } else {
                return Inferred::new_any(AnyCause::Todo);
            }
        }
    }
    unreachable!()
}
