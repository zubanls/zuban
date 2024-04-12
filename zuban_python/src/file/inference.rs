use std::{cell::Cell, rc::Rc};

use parsa_python_ast::*;

use super::{
    diagnostics::await_aiter_and_next, on_argument_type_error, utils::infer_dict_like, File,
    PythonFile, FLOW_ANALYSIS,
};
use crate::{
    arguments::{KnownArgs, NoArgs, SimpleArgs},
    database::{
        ComplexPoint, Database, FileIndex, Locality, Point, PointLink, PointType, Specific,
    },
    debug,
    diagnostics::IssueType,
    getitem::SliceType,
    imports::{find_ancestor, global_import, python_import, ImportResult},
    inference_state::InferenceState,
    inferred::{add_attribute_error, specific_to_type, Inferred, UnionValue},
    matching::{
        matches_simple_params, CouldBeALiteral, FormatData, Generics, IteratorContent, LookupKind,
        LookupResult, Matcher, OnTypeError, ResultContext, TupleLenInfos,
    },
    new_class,
    node_ref::NodeRef,
    type_::{
        AnyCause, CallableContent, CallableParam, CallableParams, FunctionKind, Literal,
        LiteralKind, Namespace, ParamType, StarParamType, StarStarParamType, StringSlice, Tuple,
        TupleArgs, TupleUnpack, Type, UnionEntry, UnionType, Variance, WithUnpack,
    },
    type_helpers::{
        lookup_in_namespace, Class, FirstParamKind, Function, GeneratorType, Instance, Module,
        TypeOrClass,
    },
    utils::debug_indent,
};

pub struct Inference<'db: 'file, 'file, 'i_s> {
    pub(super) file: &'file PythonFile,
    pub(super) file_index: FileIndex,
    pub(super) i_s: &'i_s InferenceState<'db, 'i_s>,
}

macro_rules! check_point_cache_with {
    ($vis:vis $name:ident, $func:path, $ast:ident $(, $result_context:ident )?) => {
        $vis fn $name(&mut self, node: $ast $(, $result_context : &mut ResultContext)?) -> $crate::inferred::Inferred {
            debug_indent(|| {
                if let Some(inferred) = self.check_point_cache(node.index()) {
                    debug!(
                        "{} {:?} (#{}, {}:{}) from cache: {}",
                        stringify!($name),
                        node.short_debug(),
                        self.file.byte_to_line_column(node.start()).0,
                        self.file.file_index(),
                        node.index(),
                        {
                            let point = self.file.points.get(node.index());
                            match point.type_() {
                                PointType::Specific => format!("{:?}", point.specific()),
                                PointType::Redirect => format!("Redirect {}:{}", point.file_index(), point.node_index()),
                                _ => format!("{:?}", point.type_()),
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
                        self.file.file_index(),
                        node.index(),
                    );
                    $func(self, node $(, $result_context)?)
                }
            })
        }
    }
}

impl<'db, 'file, 'i_s> Inference<'db, 'file, 'i_s> {
    fn cache_simple_stmts_name(&mut self, simple_stmts: SimpleStmts, name_def: NodeRef) {
        debug!(
            "Infer stmt (#{}, {}:{}): {:?}",
            self.file.byte_to_line_column(simple_stmts.start()).0,
            self.file.file_index(),
            simple_stmts.index(),
            simple_stmts.short_debug().trim()
        );
        name_def.set_point(Point::new_calculating());
        for simple_stmt in simple_stmts.iter() {
            match simple_stmt.unpack() {
                SimpleStmtContent::Assignment(assignment) => {
                    self.cache_assignment_nodes(assignment);
                }
                SimpleStmtContent::ImportFrom(import_from) => {
                    self.cache_import_from(import_from);
                }
                SimpleStmtContent::ImportName(import_name) => {
                    self.cache_import_name(import_name);
                }
                _ => unreachable!("Found {simple_stmt:?}"),
            }
        }
    }

    fn cache_stmt_name(&mut self, stmt: Stmt, name_def: NodeRef) {
        debug!(
            "Infer stmt (#{}, {}:{}): {:?}",
            self.file.byte_to_line_column(stmt.start()).0,
            self.file.file_index(),
            stmt.index(),
            stmt.short_debug().trim()
        );
        match stmt.unpack() {
            StmtContent::ForStmt(for_stmt) => {
                name_def.set_point(Point::new_calculating());
                let (star_targets, star_exprs, _, _) = for_stmt.unpack();
                // Performance: We probably do not need to calculate diagnostics just for
                // calculating the names.
                self.cache_for_stmt_names(star_targets, star_exprs, false);
                // TODO do the async case as well
            }
            StmtContent::ClassDef(cls) => self.cache_class(name_def, cls),
            StmtContent::Decorated(decorated) => match decorated.decoratee() {
                Decoratee::ClassDef(cls) => self.cache_class(name_def, cls),
                _ => unreachable!(),
            },
            StmtContent::TryStmt(try_stmt) => {
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
            _ => unreachable!("Found type {:?}", stmt.short_debug()),
        }
    }

    pub fn cache_class(&mut self, name_def: NodeRef, class_node: ClassDef) {
        if !name_def.point().calculated() {
            let definition = NodeRef::new(self.file, class_node.index());
            let ComplexPoint::Class(cls_storage) = definition.complex().unwrap() else {
                unreachable!()
            };

            let class = Class::new(definition, cls_storage, Generics::NotDefinedYet, None);
            // Make sure the type vars are properly pre-calculated
            class.ensure_calculated_class_infos(self.i_s, name_def);
        }
    }

    pub(super) fn cache_import_name(&mut self, imp: ImportName) {
        if self.file.points.get(imp.index()).calculated() {
            return;
        }

        for dotted_as_name in imp.iter_dotted_as_names() {
            match dotted_as_name.unpack() {
                DottedAsNameContent::Simple(name_def, rest) => {
                    let result = self.global_import(name_def.name(), Some(name_def));
                    self.check_import_type(name_def);
                    if let Some(rest) = rest {
                        if result.is_some() {
                            self.infer_import_dotted_name(rest, result);
                        }
                    }
                }
                DottedAsNameContent::WithAs(dotted_name, as_name_def) => {
                    let result = self.infer_import_dotted_name(dotted_name, None);
                    debug_assert!(!self.file.points.get(as_name_def.index()).calculated());
                    let point = match result {
                        Some(ImportResult::File(file_index)) => {
                            Point::new_file_reference(file_index, Locality::Todo)
                        }
                        Some(ImportResult::Namespace(namespace)) => {
                            self.save_namespace(as_name_def.index(), namespace.clone());
                            continue;
                        }
                        None => {
                            Point::new_simple_specific(Specific::ModuleNotFound, Locality::Todo)
                        }
                    };
                    self.file.points.set(as_name_def.index(), point);
                    self.check_import_type(as_name_def);
                }
            }
        }

        self.file
            .points
            .set(imp.index(), Point::new_node_analysis(Locality::Todo));
    }

    fn check_import_type(&mut self, name_def: NameDefinition) {
        // Check stuff like
        //     foo: str
        //     import foo
        if let Some(original_name_index) = first_defined_name(self.file, name_def.name().index()) {
            let from = NodeRef::new(self.file, name_def.index());
            let import_inferred = self.infer_name_definition(name_def);
            self.infer_name_of_definition_by_index(original_name_index)
                .as_cow_type(self.i_s)
                .error_if_not_matches(
                    self.i_s,
                    &import_inferred,
                    |issue| from.add_issue(self.i_s, issue),
                    |got, expected| {
                        Some(IssueType::IncompatibleImportAssignment {
                            name: name_def.as_code().into(),
                            got,
                            expected,
                        })
                    },
                )
        }
    }

    pub(super) fn cache_import_from(&mut self, imp: ImportFrom) {
        if self.file.points.get(imp.index()).calculated() {
            return;
        }

        let (level, dotted_name) = imp.level_with_dotted_name();
        let maybe_level_file = (level > 0)
            .then(|| {
                find_ancestor(self.i_s.db, self.file, level).or_else(|| {
                    self.add_issue(imp.index(), IssueType::NoParentModule);
                    None
                })
            })
            .flatten();
        let from_first_part = match dotted_name {
            Some(dotted_name) => self.infer_import_dotted_name(dotted_name, maybe_level_file),
            None => maybe_level_file,
        };

        match imp.unpack_targets() {
            ImportFromTargets::Star(keyword) => {
                // Nothing to do here, was calculated earlier
                let point = match from_first_part {
                    Some(ImportResult::File(file_index)) => {
                        Point::new_file_reference(file_index, Locality::Todo)
                    }
                    Some(ImportResult::Namespace { .. }) => todo!(),
                    None => Point::new_simple_specific(Specific::ModuleNotFound, Locality::Todo),
                };
                self.file.points.set(keyword.index(), point);
            }
            ImportFromTargets::Iterator(targets) => {
                // as names should have been calculated earlier
                for target in targets {
                    let (import_name, name_def) = target.unpack();

                    let point = match &from_first_part {
                        Some(imp) => match self.lookup_import_from_target(imp, import_name) {
                            LookupResult::GotoName { name: link, .. } => {
                                link.into_redirect_point(Locality::Todo)
                            }
                            LookupResult::FileReference(file_index) => {
                                Point::new_file_reference(file_index, Locality::Todo)
                            }
                            LookupResult::UnknownName(inf) => {
                                inf.save_redirect(self.i_s, self.file, name_def.index());
                                continue;
                            }
                            LookupResult::None => {
                                self.add_issue(
                                    import_name.index(),
                                    IssueType::ImportAttributeError {
                                        module_name: Box::from(imp.qualified_name(self.i_s.db)),
                                        name: Box::from(import_name.as_str()),
                                    },
                                );
                                Point::new_simple_specific(Specific::ModuleNotFound, Locality::Todo)
                            }
                        },
                        // Means one of the imports before failed.
                        None => {
                            Point::new_simple_specific(Specific::ModuleNotFound, Locality::Todo)
                        }
                    };

                    self.file.points.set(name_def.index(), point);
                    self.check_import_type(name_def);
                }
            }
        }
        self.file
            .points
            .set(imp.index(), Point::new_node_analysis(Locality::Todo));
    }

    fn lookup_import_from_target(
        &mut self,
        from_first_part: &ImportResult,
        import_name: Name,
    ) -> LookupResult {
        let name = import_name.as_str();
        match from_first_part {
            ImportResult::File(file_index) => {
                let import_file = self.i_s.db.loaded_python_file(*file_index);
                Module::new(import_file).lookup_with_is_import(
                    self.i_s,
                    |issue| NodeRef::new(self.file, import_name.index()).add_issue(self.i_s, issue),
                    import_name.as_str(),
                    true,
                )
            }
            ImportResult::Namespace(namespace) => {
                lookup_in_namespace(self.i_s.db, self.file_index, namespace, name)
            }
        }
    }

    fn global_import(&self, name: Name, name_def: Option<NameDefinition>) -> Option<ImportResult> {
        let result = global_import(self.i_s.db, self.file.file_index(), name.as_str());
        if let Some(result) = &result {
            debug!("Global import {name:?}: {:?}", result.path(self.i_s.db),);
        }
        let point = match &result {
            Some(ImportResult::File(file_index)) => {
                Point::new_file_reference(*file_index, Locality::DirectExtern)
            }
            Some(ImportResult::Namespace(namespace)) => {
                if let Some(name_def) = name_def {
                    self.save_namespace(name_def.index(), namespace.clone())
                }
                return result;
            }
            None => {
                self.add_issue(
                    name.index(),
                    IssueType::ModuleNotFound {
                        module_name: Box::from(name.as_str()),
                    },
                );
                Point::new_simple_specific(Specific::ModuleNotFound, Locality::Todo)
            }
        };
        if let Some(name_def) = name_def {
            self.file.points.set(name_def.index(), point);
        }
        result
    }

    fn save_namespace(&self, index: NodeIndex, namespace: Rc<Namespace>) {
        Inferred::from_type(Type::Namespace(namespace)).save_redirect(self.i_s, self.file, index);
    }

    fn infer_import_dotted_name(
        &mut self,
        dotted: DottedName,
        base: Option<ImportResult>,
    ) -> Option<ImportResult> {
        let file_index = self.file_index;
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
                        && module.file.is_stub(i_s.db)
                        && module
                            .lookup(
                                i_s,
                                |issue| NodeRef::new(self.file, name.index()).add_issue(i_s, issue),
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
                    &namespace.path,
                    &namespace.content,
                    name.as_str(),
                ),
            };
            if let Some(imported) = &result {
                debug!(
                    "Imported {:?} for {:?}",
                    imported.path(i_s.db),
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
                self_.add_issue(name.index(), IssueType::ModuleNotFound { module_name });
            }
            result
        };
        match dotted.unpack() {
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
        }
    }

    fn inferred_context_for_simple_assignment(
        &mut self,
        targets: AssignmentTargetIterator,
    ) -> Option<Inferred> {
        for target in targets {
            match target {
                Target::IndexExpression(t) => {
                    let base = self.infer_primary_target_or_atom(t.first());
                    let PrimaryContent::GetItem(slice) = t.second() else {
                        unreachable!();
                    };
                    let result = base
                        .as_cow_type(self.i_s)
                        .setitem_context(self.i_s, &SliceType::new(self.file, t.index(), slice));
                    if result.is_some() {
                        return result;
                    }
                }
                Target::NameExpression(primary_target, _) => {
                    debug!("TODO enable context for named expr");
                    continue;
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

    fn set_calculating_on_target(&mut self, target: Target) {
        match target {
            Target::Name(name_def) => {
                self.file
                    .points
                    .set(name_def.index(), Point::new_calculating());
            }
            Target::NameExpression(primary_target, name_def_node) => (),
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
        let on_type_error = |got, expected| {
            // In cases of stubs when an ellipsis is given, it's not an error.
            if self.file.is_stub(self.i_s.db) {
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
            Some(IssueType::IncompatibleAssignment { got, expected })
        };
        expected.error_if_not_matches(
            self.i_s,
            &right,
            |issue| self.add_issue(right_side.index(), issue),
            on_type_error,
        );
    }

    pub fn check_right_side_against_annotation(
        &mut self,
        expected: &Type,
        right_side: AssignmentRightSide,
    ) {
        let right =
            self.infer_assignment_right_side(right_side, &mut ResultContext::Known(expected));
        self.check_right_side_against_expected(expected, right, right_side)
    }

    pub fn assign_for_annotation(
        &mut self,
        annotation: Annotation,
        target: Target,
        node_ref: NodeRef,
    ) {
        let inf_annot = self.use_cached_annotation(annotation);
        self.assign_single_target(
            target,
            node_ref,
            &inf_annot,
            AssignKind::Annotation,
            |index, _| {
                self.file.points.set(
                    index,
                    Point::new_redirect(self.file.file_index(), annotation.index(), Locality::Todo),
                );
            },
        )
    }

    pub fn cache_assignment_nodes(&mut self, assignment: Assignment) {
        let node_ref = NodeRef::new(self.file, assignment.index());
        if node_ref.point().calculated() {
            return;
        }
        let right_side = match assignment.unpack() {
            AssignmentContent::Normal(targets, right_side) => {
                for target in targets {
                    self.set_calculating_on_target(target);
                }
                Some(right_side)
            }
            AssignmentContent::WithAnnotation(target, _, right_side) => {
                self.set_calculating_on_target(target);
                right_side
            }
            AssignmentContent::AugAssign(target, aug_assign, right_side) => Some(right_side),
        };
        match assignment.unpack() {
            AssignmentContent::Normal(targets, right_side) => {
                let type_comment_result = self.check_for_type_comment(assignment);

                let assign_kind = match type_comment_result.is_some() {
                    true => AssignKind::Annotation,
                    false => AssignKind::Normal,
                };
                let right = if let Some(type_comment) = type_comment_result {
                    let right = self.infer_assignment_right_side(
                        right_side,
                        &mut ResultContext::Known(&type_comment.type_),
                    );
                    // It is very weird, but somehow type comments in Mypy are allowed to have the
                    // form of `x = None  # type: int` in classes, even with strict-optional. It's
                    // even weirder that the form `x: int = None` is not allowed.
                    if !(self.i_s.current_class().is_some()
                        && matches!(right.as_cow_type(self.i_s).as_ref(), Type::None))
                    {
                        self.check_right_side_against_expected(
                            &type_comment.type_,
                            right,
                            right_side,
                        )
                    }
                    type_comment.inferred
                } else {
                    let inf = self.inferred_context_for_simple_assignment(targets.clone());
                    let return_type = inf.as_ref().map(|inf| inf.as_cow_type(self.i_s));
                    let mut result_context = match &return_type {
                        Some(t) => ResultContext::Known(t),
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
                match self.file.points.get(annotation.index()).maybe_specific() {
                    Some(Specific::TypingTypeAlias) => {
                        let inf = self.compute_explicit_type_assignment(assignment);
                        self.assign_single_target(
                            target,
                            node_ref,
                            &inf,
                            AssignKind::Annotation,
                            |index, inf| {
                                inf.clone().save_redirect(self.i_s, self.file, index);
                            },
                        );
                    }
                    Some(Specific::TypingFinal) => {
                        let (right, index) = if let Some(right_side) = right_side {
                            (
                                self.infer_assignment_right_side(
                                    right_side,
                                    &mut ResultContext::Unknown,
                                ),
                                right_side.index(),
                            )
                        } else {
                            self.add_issue(
                                annotation.index(),
                                IssueType::FinalWithoutInitializerAndType,
                            );
                            (Inferred::new_any_from_error(), annotation.index())
                        };
                        self.assign_single_target(
                            target,
                            NodeRef::new(self.file, index),
                            &right,
                            AssignKind::Annotation,
                            |index, right| {
                                right.clone().save_redirect(self.i_s, self.file, index);
                            },
                        );
                    }
                    _ => {
                        if let Some(right_side) = right_side {
                            let t = self.use_cached_annotation_type(annotation);
                            self.check_right_side_against_annotation(&t, right_side);
                        }
                        let n = match right_side {
                            Some(right_side) => NodeRef::new(self.file, right_side.index()),
                            None => NodeRef::new(self.file, annotation.index()),
                        };
                        self.assign_for_annotation(annotation, target, n)
                    }
                }
            }
            AssignmentContent::AugAssign(target, aug_assign, right_side) => {
                let (inplace_method, op_infos) = aug_assign.magic_methods();
                let right =
                    self.infer_assignment_right_side(right_side, &mut ResultContext::Unknown);
                let Some(left) = self.infer_target(target, true) else {
                    todo!()
                };
                let had_lookup_error = Cell::new(false);
                let mut result = left.type_lookup_and_execute(
                    self.i_s,
                    node_ref,
                    inplace_method,
                    &KnownArgs::new(&right, node_ref),
                    &|type_| had_lookup_error.set(true),
                );
                let had_error = Cell::new(false);
                if had_lookup_error.get() {
                    result =
                        self.infer_detailed_operation(right_side.index(), op_infos, left, &right)
                }

                let AssignmentContent::AugAssign(target, ..) = assignment.unpack() else {
                    unreachable!()
                };
                let n = NodeRef::new(self.file, right_side.index());
                self.assign_single_target(target, n, &result, AssignKind::AugAssign, |index, _| {
                    // There is no need to save this, because it's never used
                })
            }
        }
        self.file
            .points
            .set(assignment.index(), Point::new_node_analysis(Locality::Todo));
    }

    fn infer_assignment_right_side(
        &mut self,
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

    pub fn infer_yield_expr(
        &mut self,
        yield_expr: YieldExpr,
        result_context: &mut ResultContext,
    ) -> Inferred {
        let i_s = self.i_s;
        let from = NodeRef::new(self.file, yield_expr.index());
        let Some(current_function) = self.i_s.current_function() else {
            // The name binder already added an issue here.
            return Inferred::new_any_from_error()
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
                let inf = self.infer_star_expressions(s, &mut ResultContext::Unknown);
                Inferred::from_type(generator.yield_type)
                    .as_cow_type(i_s)
                    .error_if_not_matches(
                        i_s,
                        &inf,
                        |issue| from.add_issue(i_s, issue),
                        |got, expected| {
                            Some(IssueType::IncompatibleTypes {
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
                let iter_result = expr_result.type_lookup_and_execute(
                    i_s,
                    from,
                    "__iter__",
                    &NoArgs::new(from),
                    &|_| {
                        from.add_issue(
                            i_s,
                            IssueType::YieldFromCannotBeApplied {
                                to: expr_result.format_short(i_s),
                            },
                        )
                    },
                );
                let yields = iter_result.type_lookup_and_execute(
                    i_s,
                    from,
                    "__next__",
                    &NoArgs::new(from),
                    &|_| todo!(),
                );
                generator.yield_type.error_if_not_matches(
                    i_s,
                    &yields,
                    |issue| from.add_issue(i_s, issue),
                    |got, expected| {
                        Some(IssueType::IncompatibleTypes {
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
                    } else {
                        if result_context.expect_not_none(i_s) {
                            from.add_issue(i_s, IssueType::DoesNotReturnAValue("Function".into()));
                            Inferred::new_any_from_error()
                        } else {
                            Inferred::new_none()
                        }
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
                    from.add_issue(i_s, IssueType::YieldValueExpected);
                }
            }
        }
        if let Some(send_type) = generator.send_type {
            Inferred::from_type(send_type)
        } else {
            Inferred::new_none()
        }
    }

    fn infer_target(&mut self, target: Target, from_aug_assign: bool) -> Option<Inferred> {
        match target {
            Target::Name(name_def) => self.infer_name_target(name_def, from_aug_assign),
            Target::NameExpression(primary_target, _) => {
                Some(self.infer_primary_target(primary_target))
            }
            Target::IndexExpression(t) if from_aug_assign => Some(self.infer_primary_target(t)),
            Target::Tuple(targets) => {
                Some(Inferred::from_type(Type::Tuple(Tuple::new_fixed_length(
                    targets
                        .map(|target| {
                            self.infer_target(target, from_aug_assign)
                                .map(|i| i.as_type(self.i_s))
                                .unwrap_or(Type::Any(AnyCause::Todo))
                        })
                        .collect(),
                ))))
            }
            _ => None,
        }
    }

    fn infer_name_target(
        &mut self,
        name_def: NameDefinition,
        from_aug_assign: bool,
    ) -> Option<Inferred> {
        if name_def.as_code() == "__slots__" {
            return None;
        }
        let check_base_class = |name_def: NameDefinition| {
            self.i_s.current_class().and_then(|cls| {
                if cls.is_calculating_class_infos() {
                    return None;
                }
                cls.lookup_without_descriptors_and_custom_add_issue_ignore_self(
                    self.i_s,
                    name_def.as_code(),
                    |_| todo!(),
                )
                .lookup
                .into_maybe_inferred()
            })
        };
        first_defined_name(self.file, name_def.name_index())
            .map(|first_index| {
                // The first definition is always responsible for how a name is defined.
                // So we try to look up active narrowings first or we try to lookup the first
                // name.
                if from_aug_assign {
                    if let Some(result) = self
                        .maybe_lookup_narrowed_name(PointLink::new(self.file_index, first_index))
                    {
                        return result;
                    }
                }
                // TODO check base class!
                self.infer_name_of_definition_by_index(first_index)
            })
            .or_else(|| check_base_class(name_def))
    }

    fn assign_single_target(
        &mut self,
        target: Target,
        from: NodeRef,
        value: &Inferred,
        assign_kind: AssignKind,
        save: impl FnOnce(NodeIndex, &Inferred),
    ) {
        let i_s = self.i_s;
        match target {
            Target::Name(name_def) => {
                let current_index = name_def.name_index();
                if let Some(first_index) = first_defined_name(self.file, current_index) {
                    if current_index == first_index {
                        /*
                        if matches!(value.as_cow_type(i_s).as_ref(), Type::None) {
                            self.file.points.set(name_def.index(), Point::new_simple_specific(Specific::PartialNone, Locality::Todo));
                            return
                        }
                        */
                    } else {
                        let original_inf = self.infer_name_of_definition_by_index(first_index);
                        let original_t = original_inf.as_cow_type(i_s);
                        let check_for_error = || {
                            original_t.error_if_not_matches(
                                i_s,
                                value,
                                |issue| from.add_issue(i_s, issue),
                                |got, expected| {
                                    Some(IssueType::IncompatibleAssignment { got, expected })
                                },
                            );
                        };
                        if matches!(assign_kind, AssignKind::Normal) {
                            if !self.narrow_or_widen_name_target(
                                first_index,
                                &original_t,
                                &value.as_cow_type(i_s),
                            ) {
                                check_for_error()
                            }
                        } else {
                            check_for_error()
                        }
                        return;
                    }
                    save(name_def.index(), value);
                } else if value.maybe_saved_specific(i_s.db) == Some(Specific::None)
                    && assign_kind == AssignKind::Normal
                    && i_s.db.project.flags.local_partial_types
                    && !i_s.current_class().is_some_and(|c| {
                        c.lookup_without_descriptors_and_custom_add_issue_ignore_self(
                            self.i_s,
                            name_def.as_code(),
                            |_| todo!(),
                        )
                        .lookup
                        .is_some()
                    })
                {
                    self.add_issue(
                        name_def.index(),
                        IssueType::NeedTypeAnnotation {
                            for_: name_def.as_code().into(),
                            hint: "Optional[<type>]",
                        },
                    );
                    // Save Optional[Any]
                    save(
                        name_def.index(),
                        &Inferred::from_type(
                            Type::Any(AnyCause::FromError).union_with_details(Type::None, true),
                        ),
                    );
                } else {
                    save(name_def.index(), value);
                }
            }
            Target::NameExpression(primary_target, name_definition) => {
                let base = self.infer_primary_target_or_atom(primary_target.first());
                if base.maybe_saved_specific(i_s.db) == Some(Specific::MaybeSelfParam) {
                    // TODO we should probably check if we are in a staticmethod/classmethod
                    let PrimaryContent::Attribute(name) = primary_target.second() else {
                        unreachable!();
                    };
                    // TODO The class should ALWAYS exist, this is just a bug at the moment.
                    if let Some(class) = i_s.current_class() {
                        class.check_self_definition(
                            i_s,
                            |issue| from.add_issue(i_s, issue),
                            name.as_str(),
                        );
                    }
                } else {
                    if matches!(assign_kind, AssignKind::Annotation) {
                        self.add_issue(primary_target.index(), IssueType::InvalidTypeDeclaration);
                    }
                    if matches!(assign_kind, AssignKind::Normal) {
                        self.save_narrowed_primary_target(
                            primary_target,
                            &value.as_cow_type(self.i_s),
                        );
                    }
                    let base = base.as_cow_type(i_s);
                    let node_ref = NodeRef::new(self.file, primary_target.index());
                    for t in base.iter_with_unpacked_unions(i_s.db) {
                        if let Some(cls) = t.maybe_class(i_s.db) {
                            Instance::new(cls, None).check_set_descriptor(
                                i_s,
                                node_ref,
                                name_definition.name(),
                                value,
                            );
                            continue;
                        }
                        let property_is_read_only = |class_name| {
                            from.add_issue(
                                i_s,
                                IssueType::PropertyIsReadOnly {
                                    class_name,
                                    property_name: name_definition.as_code().into(),
                                },
                            )
                        };
                        match t {
                            Type::Dataclass(d) => {
                                if d.options.frozen {
                                    property_is_read_only(d.class(i_s.db).name().into())
                                }
                                Instance::new(d.class(i_s.db), None).check_set_descriptor(
                                    i_s,
                                    node_ref,
                                    name_definition.name(),
                                    value,
                                );
                                continue;
                            }
                            Type::NamedTuple(nt) => {
                                if nt.search_param(i_s.db, name_definition.as_code()).is_some() {
                                    property_is_read_only(nt.name(i_s.db).into());
                                    continue;
                                }
                            }
                            _ => (),
                        }

                        let inf = t
                            .maybe_type_of_class(i_s.db)
                            .and_then(|c| {
                                // We need to handle class descriptors separately, because
                                // there the __get__ descriptor should not be applied.
                                c.lookup_without_descriptors(
                                    i_s,
                                    node_ref,
                                    name_definition.as_code(),
                                )
                                .lookup
                                .into_maybe_inferred()
                                .map(|inf| {
                                    if inf.as_cow_type(i_s).is_func_or_overload_not_any_callable() {
                                        from.add_issue(i_s, IssueType::CannotAssignToAMethod);
                                    }
                                    inf
                                })
                            })
                            .unwrap_or_else(|| {
                                t.lookup(
                                    i_s,
                                    node_ref.file_index(),
                                    name_definition.as_code(),
                                    LookupKind::Normal,
                                    &mut ResultContext::Unknown,
                                    &|issue| node_ref.add_issue(i_s, issue),
                                    &|t| {
                                        add_attribute_error(
                                            i_s,
                                            node_ref,
                                            &base,
                                            t,
                                            name_definition.as_code(),
                                        )
                                    },
                                )
                                .into_inferred()
                            });
                        inf.as_cow_type(i_s).error_if_not_matches(
                            i_s,
                            value,
                            |issue| from.add_issue(i_s, issue),
                            |got, expected| {
                                Some(IssueType::IncompatibleAssignment { got, expected })
                            },
                        );
                    }
                }
                // This mostly needs to be saved for self names
                save(name_definition.index(), value);
            }
            Target::IndexExpression(primary_target) => {
                let base = self.infer_primary_target_or_atom(primary_target.first());
                if matches!(assign_kind, AssignKind::Annotation) {
                    self.add_issue(primary_target.index(), IssueType::UnexpectedTypeDeclaration);
                }
                let PrimaryContent::GetItem(slice_type) = primary_target.second() else {
                    unreachable!();
                };
                base.type_check_set_item(
                    i_s,
                    SliceType::new(self.file, primary_target.index(), slice_type),
                    value,
                );
                //self.narrow_primary_target_from_assignment(primary_target, &value.as_cow_type(self.i_s))
            }
            Target::Tuple(_) | Target::Starred(_) => unreachable!(),
        }
    }

    pub(super) fn assign_targets(
        &mut self,
        target: Target,
        value: Inferred,
        value_node_ref: NodeRef,
        assign_kind: AssignKind,
    ) {
        match target {
            Target::Tuple(targets) => {
                // TODO what about never? The loop will never be executed.
                for union_part in value
                    .as_cow_type(self.i_s)
                    .iter_with_unpacked_unions(self.i_s.db)
                {
                    if union_part == &self.i_s.db.python_state.str_type() {
                        value_node_ref.add_issue(self.i_s, IssueType::UnpackingAStringIsDisallowed)
                    }
                    let value_iterator = union_part.iter(self.i_s, value_node_ref);
                    match value_iterator {
                        IteratorContent::Union(iterators) => {
                            for it in iterators {
                                self.assign_tuple_target(
                                    targets.clone(),
                                    it,
                                    value_node_ref,
                                    assign_kind,
                                )
                            }
                        }
                        _ => self.assign_tuple_target(
                            targets.clone(),
                            value_iterator,
                            value_node_ref,
                            assign_kind,
                        ),
                    }
                }
            }
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
                        NodeRef::new(self.file, index).accumulate_types(self.i_s, value)
                    },
                )
            }
        };
    }

    fn assign_tuple_target(
        &mut self,
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
                            IssueType::TooFewValuesToUnpack { actual, expected }
                        } else {
                            IssueType::TooManyValuesToUnpack { actual, expected }
                        },
                    );
                    true
                }
                (WithStar { before, after }, FixedLen(actual)) if before + after > actual => {
                    value_node_ref.add_issue(
                        self.i_s,
                        IssueType::TooFewValuesToUnpack {
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
                        IssueType::TooManyAssignmentTargetsForVariadicUnpack,
                    );
                    true
                }
                (FixedLen(expected), WithStar { before, after }) => {
                    value_node_ref.add_issue(
                        self.i_s,
                        IssueType::VariadicTupleUnpackingRequiresStarTarget,
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
                IssueType::MultipleStarredExpressionsInAssignment,
            );
        }

        // 3. Abort if necessary.
        if had_issue {
            for target in targets {
                self.assign_targets(
                    target,
                    Inferred::new_any_from_error(),
                    value_node_ref,
                    assign_kind,
                );
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
        &mut self,
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
                self.add_issue(expr.index(), IssueType::StarredExpressionOnlyNoTarget);
                Inferred::new_any_from_error()
            }
            StarExpressionContent::Tuple(tuple) => self
                .infer_tuple_iterator(tuple.iter(), result_context)
                .save_redirect(self.i_s, self.file, tuple.index()),
        }
    }

    pub fn infer_named_expression(&mut self, named_expr: NamedExpression) -> Inferred {
        self.infer_named_expression_with_context(named_expr, &mut ResultContext::Unknown)
    }

    pub fn infer_named_expression_with_context(
        &mut self,
        named_expr: NamedExpression,
        result_context: &mut ResultContext,
    ) -> Inferred {
        match named_expr.unpack() {
            NamedExpressionContent::Expression(expr) => {
                self.infer_expression_with_context(named_expr.expression(), result_context)
            }
            NamedExpressionContent::Walrus(walrus) => {
                let (name_def, expr) = walrus.unpack();
                self.infer_expression_with_context(named_expr.expression(), result_context)
                    .save_redirect(self.i_s, self.file, name_def.index())
            }
        }
    }

    pub fn infer_expression(&mut self, expr: Expression) -> Inferred {
        self.infer_expression_with_context(expr, &mut ResultContext::Unknown)
    }

    check_point_cache_with!(
        pub infer_expression_with_context,
        Self::infer_expression_without_cache,
        Expression,
        result_context
    );
    fn infer_expression_without_cache(
        &mut self,
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
        if self.i_s.db.project.flags.disallow_any_expr && !self.file.is_stub(self.i_s.db) {
            let t = inferred.as_cow_type(self.i_s);
            if t.has_any(self.i_s) {
                self.add_issue(
                    expr.index(),
                    IssueType::DisallowedAnyExpr {
                        type_: t.format_short(self.i_s.db),
                    },
                );
            }
        }
        inferred
    }

    pub fn infer_expression_part(&mut self, node: ExpressionPart) -> Inferred {
        self.infer_expression_part_with_context(node, &mut ResultContext::Unknown)
    }

    pub fn infer_expression_part_with_context(
        &mut self,
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
                        if matches!(atom.unpack(), AtomContent::List(_)) {
                            if self
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
                }
                self.infer_operation(op)
            }
            ExpressionPart::Power(power) => self.infer_operation(power.as_operation()),
            ExpressionPart::ShiftExpr(shift) => self.infer_operation(shift.as_operation()),
            ExpressionPart::BitwiseOr(or) => self.infer_operation(or.as_operation()),
            ExpressionPart::BitwiseAnd(and) => self.infer_operation(and.as_operation()),
            ExpressionPart::BitwiseXor(xor) => self.infer_operation(xor.as_operation()),
            ExpressionPart::Disjunction(or) => self.flow_analysis_for_disjunction(or),
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
                    node_ref,
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
                            IssueType::UnsupportedOperandForUnary { operand, got },
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
                        from.add_issue(self.i_s, IssueType::AwaitOutsideCoroutine);
                        Inferred::new_any_from_error()
                    }
                } else {
                    from.add_issue(self.i_s, IssueType::AwaitOutsideFunction);
                    Inferred::new_any_from_error()
                }
            }
        }
    }

    pub fn infer_comparison_part(
        &mut self,
        cmp: ComparisonContent,
        left_inf: Inferred,
        right_inf: &Inferred,
    ) -> Inferred {
        match cmp {
            ComparisonContent::Equals(first, op, second)
            | ComparisonContent::NotEquals(first, op, second) => {
                let from = NodeRef::new(self.file, op.index());
                // TODO this does not implement __ne__ for NotEquals
                left_inf.type_lookup_and_execute(
                    self.i_s,
                    from,
                    "__eq__",
                    &KnownArgs::new(&right_inf, from),
                    &|_| todo!(),
                )
            }
            ComparisonContent::Is(first, _, second)
            | ComparisonContent::IsNot(first, _, second) => {
                Inferred::from_type(self.i_s.db.python_state.bool_type())
            }
            ComparisonContent::In(first, op, second)
            | ComparisonContent::NotIn(first, op, second) => {
                let from = NodeRef::new(self.file, op.index());
                self.infer_in_operator(from, &left_inf, right_inf)
            }
            ComparisonContent::Ordering(op) => {
                self.infer_detailed_operation(op.index, op.infos, left_inf, &right_inf)
            }
        }
    }

    pub fn infer_in_operator(
        &mut self,
        from: NodeRef,
        left_inf: &Inferred,
        right_inf: &Inferred,
    ) -> Inferred {
        right_inf.run_after_lookup_on_each_union_member(
            self.i_s,
            from,
            "__contains__",
            LookupKind::OnlyType,
            &mut |r_type, lookup_result| {
                if let Some(method) = lookup_result.lookup.into_maybe_inferred() {
                    method.execute_with_details(
                        self.i_s,
                        &KnownArgs::new(&left_inf, from),
                        &mut ResultContext::Unknown,
                        OnTypeError::new(&|i_s, _, _, types| {
                            let right = r_type.format_short(i_s.db);
                            from.add_issue(
                                i_s,
                                IssueType::UnsupportedOperand {
                                    operand: Box::from("in"),
                                    left: types.got.as_string(i_s.db).into(),
                                    right,
                                },
                            );
                        }),
                    );
                } else {
                    r_type
                        .lookup(
                            self.i_s,
                            from.file_index(),
                            "__iter__",
                            LookupKind::OnlyType,
                            &mut ResultContext::Unknown,
                            &|issue| from.add_issue(self.i_s, issue),
                            &|_| {
                                let right = right_inf.format_short(self.i_s);
                                from.add_issue(self.i_s, IssueType::UnsupportedIn { right })
                            },
                        )
                        .into_inferred()
                        .execute(self.i_s, &NoArgs::new(from))
                        .type_lookup_and_execute(
                            self.i_s,
                            from,
                            "__next__",
                            &NoArgs::new(from),
                            &|_| todo!(),
                        )
                        .as_cow_type(self.i_s)
                        .error_if_not_matches(
                            self.i_s,
                            &left_inf,
                            |issue| from.add_issue(self.i_s, issue),
                            |got, _| {
                                Some(IssueType::UnsupportedOperand {
                                    operand: Box::from("in"),
                                    left: got,
                                    right: r_type.format_short(self.i_s.db),
                                })
                            },
                        );
                }
            },
        );
        Inferred::from_type(self.i_s.db.python_state.bool_type())
    }

    fn infer_lambda(&mut self, lambda: Lambda, result_context: &mut ResultContext) -> Inferred {
        let check_defaults = |inference: &mut Inference| {
            let (params, expr) = lambda.unpack();
            for param in params {
                if let Some(default) = param.default() {
                    inference.infer_expression(default);
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
                StringSlice::from_name(self.file.file_index(), param.name_definition().name())
                    .into(),
            ),
            has_default: param.default().is_some(),
        };
        result_context
            .with_type_if_exists_and_replace_type_var_likes(self.i_s, |type_| {
                if let Type::Callable(c) = type_ {
                    let i_s = self.i_s.with_lambda_callable(c);
                    let (params, expr) = lambda.unpack();
                    let mut inference = self.file.inference(&i_s);
                    check_defaults(&mut inference);
                    let result = inference.infer_expression_without_cache(
                        expr,
                        &mut ResultContext::Known(&c.return_type),
                    );
                    let mut c = (**c).clone();
                    let params = params.map(to_callable_param);
                    match &c.params {
                        CallableParams::Simple(expected_params) => {
                            let params: Vec<_> = params.collect();
                            if !matches_simple_params(
                                self.i_s,
                                &mut Matcher::default(),
                                expected_params.iter(),
                                params.iter().peekable(),
                                Variance::Invariant,
                            )
                            .bool()
                            {
                                self.add_issue(lambda.index(), IssueType::CannotInferLambdaParams);
                                c.params = CallableParams::Simple(params.into());
                            }
                        }
                        _ => {
                            c.params = CallableParams::Simple(params.collect());
                        }
                    }
                    c.return_type = result.as_type(&i_s);
                    Some(Inferred::from_type(Type::Callable(Rc::new(c))))
                } else {
                    None
                }
            })
            .flatten()
            .unwrap_or_else(|| {
                let (params, expr) = lambda.unpack();
                check_defaults(self);
                let result =
                    self.infer_expression_without_cache(expr, &mut ResultContext::ExpectUnused);
                let c = CallableContent {
                    name: None,
                    class_name: None,
                    defined_at: PointLink::new(self.file.file_index(), lambda.index()),
                    kind: FunctionKind::Function {
                        had_first_self_or_class_annotation: true,
                    },
                    type_vars: self.i_s.db.python_state.empty_type_var_likes.clone(),
                    params: CallableParams::Simple(params.map(to_callable_param).collect()),
                    return_type: result.as_type(self.i_s),
                };
                Inferred::from_type(Type::Callable(Rc::new(c)))
            })
    }

    fn infer_operation(&mut self, op: Operation) -> Inferred {
        let left = self.infer_expression_part(op.left);
        let right = self.infer_expression_part(op.right);
        self.infer_detailed_operation(op.index, op.infos, left, &right)
    }

    fn infer_detailed_operation(
        &mut self,
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
                from,
                op_infos.magic_method,
                LookupKind::OnlyType,
                &mut |l_type, lookup_result| {
                    let left_op_method = lookup_result.lookup.into_maybe_inferred();
                    for r_type in right.as_cow_type(i_s).iter_with_unpacked_unions(i_s.db) {
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

                        let run = |first: &Inferred, second_type: &Type| {
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
                            (!local_error.get()).then_some(result)
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
                                IssueType::UnsupportedLeftOperand {
                                    operand: Box::from(op_infos.operand),
                                    left: l_type.format_short(i_s.db),
                                }
                            } else {
                                IssueType::UnsupportedOperand {
                                    operand: Box::from(op_infos.operand),
                                    left: l_type.format_short(i_s.db),
                                    right: r_type.format_short(i_s.db),
                                }
                            };
                            from.add_issue(i_s, issue);
                            Inferred::new_any_from_error()
                        }))
                    }
                },
            )
        });
        if had_error {
            let note = match (left.is_union(self.i_s), right.is_union(self.i_s)) {
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
            from.add_issue(self.i_s, IssueType::Note(note));
        }
        debug!(
            "Operation between {} and {} results in {}",
            left.format_short(i_s),
            right.format_short(i_s),
            result.format_short(i_s)
        );
        result
    }

    pub fn infer_primary(
        &mut self,
        primary: Primary,
        result_context: &mut ResultContext,
    ) -> Inferred {
        if let Some(inf) = self.maybe_lookup_narrowed_primary(primary) {
            return inf;
        }
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
        &mut self,
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
                .save_name(self.i_s, self.file, name)
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

    pub fn infer_primary_or_atom(&mut self, p: PrimaryOrAtom) -> Inferred {
        match p {
            PrimaryOrAtom::Primary(primary) => {
                self.infer_primary(primary, &mut ResultContext::Unknown)
            }
            PrimaryOrAtom::Atom(atom) => self.infer_atom(atom, &mut ResultContext::Unknown),
        }
    }

    check_point_cache_with!(pub infer_atom, Self::_infer_atom, Atom, result_context);
    fn _infer_atom(&mut self, atom: Atom, result_context: &mut ResultContext) -> Inferred {
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
            let point = Point::new_simple_specific(specific, Locality::Todo);
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
                return check_literal(result_context, i_s, b.index(), Specific::BytesLiteral)
            }
            NoneLiteral => Specific::None,
            Bool(b) => return check_literal(result_context, i_s, b.index(), Specific::BoolLiteral),
            Ellipsis => Specific::Ellipsis,
            List(list) => {
                if let Some(result) = self.infer_list_literal_from_context(list, result_context) {
                    return result.save_redirect(i_s, self.file, atom.index());
                }
                let result = match list.unpack() {
                    elements @ StarLikeExpressionIterator::Elements(_) => {
                        self.create_list_or_set_generics(elements)
                    }
                    StarLikeExpressionIterator::Empty => Type::Any(AnyCause::Todo), // TODO shouldn't this be Never?
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
                if let elements @ StarLikeExpressionIterator::Elements(_) = set.unpack() {
                    return Inferred::from_type(new_class!(
                        i_s.db.python_state.set_node_ref().as_link(),
                        self.create_list_or_set_generics(elements),
                    ))
                    .save_redirect(i_s, self.file, atom.index());
                } else {
                    todo!()
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
        let point = Point::new_simple_specific(specific, Locality::Todo);
        Inferred::new_and_save(self.file, atom.index(), point)
    }

    fn infer_tuple_iterator<'x>(
        &mut self,
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
                inference: &mut Inference,
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

        let is_definition = matches!(result_context, ResultContext::AssignmentNewDefinition);
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
                        return;
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
                                &mut ResultContext::Known(expected),
                            )
                            .as_type(self.i_s);
                        gatherer.add(t)
                    }
                    StarLikeExpression::Expression(e) => {
                        let t = self
                            .infer_expression_with_context(e, &mut ResultContext::Known(expected))
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

    check_point_cache_with!(
        infer_primary_target,
        Self::_infer_primary_target,
        PrimaryTarget
    );
    fn _infer_primary_target(&mut self, primary_target: PrimaryTarget) -> Inferred {
        let first = self.infer_primary_target_or_atom(primary_target.first());
        self.infer_primary_or_primary_t_content(
            &first,
            primary_target.index(),
            primary_target.second(),
            true,
            &mut ResultContext::Unknown,
        )
        .save_redirect(self.i_s, self.file, primary_target.index())
    }

    pub fn infer_primary_target_or_atom(&mut self, t: PrimaryTargetOrAtom) -> Inferred {
        match t {
            PrimaryTargetOrAtom::Atom(atom) => self.infer_atom(atom, &mut ResultContext::Unknown),
            PrimaryTargetOrAtom::PrimaryTarget(p) => self.infer_primary_target(p),
        }
    }

    check_point_cache_with!(pub infer_name_reference, Self::_infer_name_reference, Name);
    fn _infer_name_reference(&mut self, name: Name) -> Inferred {
        // If it's not inferred already through the name binder, it's either a star import, a
        // builtin or really missing.
        let name_str = name.as_str();
        if let Some(point_link) = self.lookup_from_star_import(name_str, true) {
            self.file.points.set(
                name.index(),
                Point::new_redirect(point_link.file, point_link.node_index, Locality::Todo),
            );
            return self.infer_name_reference(name);
        }
        let builtins = self.i_s.db.python_state.builtins();
        let point = match name_str {
            "reveal_type" => {
                Point::new_simple_specific(Specific::RevealTypeFunction, Locality::Stmt)
            }
            "__builtins__" => Point::new_file_reference(builtins.file_index(), Locality::Todo),
            _ => {
                if let Some(link) = builtins.lookup_global(name.as_str()) {
                    debug_assert!(link.file != self.file_index || link.node_index != name.index());
                    link.into_point_redirect()
                } else {
                    // The builtin module should really not have any issues.
                    debug_assert!(self.file_index != builtins.file_index(), "{:?}", name);
                    if let Some(inf) = self
                        .i_s
                        .db
                        .python_state
                        .module_instance()
                        .type_lookup(
                            self.i_s,
                            |issue| {
                                NodeRef::new(self.file, name.index()).add_issue(self.i_s, issue)
                            },
                            name.as_code(),
                        )
                        .save_name(self.i_s, self.file, name)
                    {
                        return inf;
                    }
                    // TODO check star imports
                    self.add_issue(
                        name.index(),
                        IssueType::NameError {
                            name: Box::from(name.as_str()),
                        },
                    );
                    if self
                        .i_s
                        .db
                        .python_state
                        .typing()
                        .lookup_global(name_str)
                        .is_some()
                    {
                        // TODO what about underscore or other vars?
                        self.add_issue(
                            name.index(),
                            IssueType::Note(
                                format!(
                                    "Did you forget to import it from \"typing\"? \
                             (Suggestion: \"from typing import {name_str}\")",
                                )
                                .into(),
                            ),
                        );
                    }
                    Point::new_simple_specific(Specific::AnyDueToError, Locality::Todo)
                }
            }
        };
        self.file.points.set(name.index(), point);
        debug_assert!(self.file.points.get(name.index()).calculated());
        self.infer_name_reference(name)
    }

    pub fn lookup_from_star_import(&mut self, name: &str, check_local: bool) -> Option<PointLink> {
        if !name.starts_with('_') {
            for star_import in self.file.star_imports.borrow().iter() {
                // TODO these feel a bit weird and do not include parent functions (when in a
                // closure)
                if !(star_import.scope == 0
                    || check_local
                        && self
                            .i_s
                            .current_function()
                            .map(|f| f.node_ref.node_index == star_import.scope)
                            .unwrap_or_else(|| {
                                self.i_s
                                    .current_class()
                                    .is_some_and(|c| c.node_ref.node_index == star_import.scope)
                            }))
                {
                    continue;
                }
                if let Some(other_file) = star_import.to_file(self) {
                    if let Some(symbol) = other_file.symbol_table.lookup_symbol(name) {
                        return Some(PointLink::new(other_file.file_index(), symbol));
                    }
                    if let Some(l) = other_file
                        .inference(self.i_s)
                        .lookup_from_star_import(name, false)
                    {
                        return Some(l);
                    }
                }
            }
        }
        if let Some(super_file) = &self.file.super_file {
            if let Some(func) = self.i_s.current_function() {
                debug!("TODO lookup in func of sub file")
            } else if let Some(class) = self.i_s.current_class() {
                debug!("TODO lookup in class of sub file")
            }

            let super_file = self.i_s.db.loaded_python_file(*super_file);
            if let Some(symbol) = super_file.symbol_table.lookup_symbol(name) {
                return Some(PointLink::new(super_file.file_index(), symbol));
            }
            super_file
                .inference(self.i_s)
                .lookup_from_star_import(name, false)
        } else {
            None
        }
    }

    pub fn check_point_cache(&mut self, node_index: NodeIndex) -> Option<Inferred> {
        let point = self.file.points.get(node_index);
        point
            .calculated()
            .then(|| match point.type_() {
                PointType::Redirect => {
                    let file_index = point.file_index();
                    let next_node_index = point.node_index();
                    if point.needs_flow_analysis() {
                        debug_assert!(Name::maybe_by_index(&self.file.tree, node_index).is_some());
                        if let Some(result) = self
                            .maybe_lookup_narrowed_name(PointLink::new(file_index, next_node_index))
                        {
                            return result;
                        }
                    }
                    debug_assert!(
                        file_index != self.file.file_index() || next_node_index != node_index,
                        "{file_index}:{node_index}"
                    );
                    let infer = |inference: &mut Inference| {
                        let point = inference.file.points.get(next_node_index);
                        inference
                            .check_point_cache(next_node_index)
                            .unwrap_or_else(|| {
                                let name =
                                    Name::maybe_by_index(&inference.file.tree, next_node_index);
                                if let Some(name) = name {
                                    inference.infer_name_of_definition(name)
                                } else if let Some(expr) = Expression::maybe_by_index(
                                    &inference.file.tree,
                                    next_node_index,
                                ) {
                                    inference.infer_expression_without_cache(
                                        expr,
                                        &mut ResultContext::Unknown,
                                    )
                                } else if let Some(annotation) = Annotation::maybe_by_index(
                                    &inference.file.tree,
                                    next_node_index,
                                ) {
                                    todo!()
                                    // inference.cache_annotation(annotation)
                                } else {
                                    todo!(
                                        "{}",
                                        NodeRef::new(inference.file, next_node_index)
                                            .debug_info(self.i_s.db)
                                    )
                                }
                            })
                    };
                    if file_index == self.file_index {
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
                PointType::Specific => match point.specific() {
                    specific @ (Specific::Param | Specific::MaybeSelfParam) => {
                        let name_def = NameDefinition::by_index(&self.file.tree, node_index);
                        // Performance: This could be improved by not needing to lookup all the
                        // parents all the time.
                        match name_def.function_or_lambda_ancestor().unwrap() {
                            FunctionOrLambda::Function(func_node) => {
                                let func = Function::new(
                                    NodeRef::new(self.file, func_node.index()),
                                    self.i_s.current_class().copied(),
                                );
                                func.type_vars(self.i_s);

                                if let Some(annotation) = name_def.maybe_param_annotation() {
                                    self.use_cached_param_annotation(annotation)
                                } else if let Some((function, args)) = self.i_s.current_execution()
                                {
                                    if specific == Specific::MaybeSelfParam {
                                        match func.first_param_kind(self.i_s) {
                                            FirstParamKind::Self_ => {
                                                Inferred::new_saved(self.file, node_index)
                                            }
                                            FirstParamKind::ClassOfSelf => Inferred::from_type(
                                                Type::Type(Rc::new(Type::Self_)),
                                            ),
                                            FirstParamKind::InStaticmethod => todo!(),
                                        }
                                    } else {
                                        for param in func_node.params().iter() {
                                            if param.name_definition().index() == name_def.index() {
                                                return match param.kind() {
                                                    ParamKind::Star => todo!(),
                                                    ParamKind::StarStar => {
                                                        Inferred::from_type(new_class!(
                                                            self.i_s
                                                                .db
                                                                .python_state
                                                                .dict_node_ref()
                                                                .as_link(),
                                                            self.i_s.db.python_state.str_type(),
                                                            Type::Any(AnyCause::Unannotated),
                                                        ))
                                                    }
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
                            FunctionOrLambda::Lambda(lambda) => {
                                for (i, p) in lambda.params().enumerate() {
                                    if p.name_definition().index() == node_index {
                                        if let Some(current_callable) =
                                            self.i_s.current_lambda_callable()
                                        {
                                            return match &current_callable.params {
                                                CallableParams::Simple(ps) => {
                                                    if let Some(p2) = ps.get(i) {
                                                        if let ParamType::PositionalOnly(t) =
                                                            &p2.type_
                                                        {
                                                            if p.kind()
                                                                == ParamKind::PositionalOrKeyword
                                                            {
                                                                Inferred::from_type(t.clone())
                                                            } else {
                                                                todo!()
                                                            }
                                                        } else {
                                                            todo!()
                                                        }
                                                    } else {
                                                        todo!()
                                                    }
                                                }
                                                CallableParams::Any(cause) => {
                                                    Inferred::new_any(*cause)
                                                }
                                                CallableParams::WithParamSpec(_, _) => todo!(),
                                            };
                                        } else {
                                            return Inferred::new_any(AnyCause::Todo);
                                        }
                                    }
                                }
                                unreachable!()
                            }
                        }
                    }
                    Specific::LazyInferredClass => {
                        // TODO this does not analyze decorators
                        let name_def = NameDefinition::by_index(&self.file.tree, node_index);
                        let class = name_def.expect_class_def();
                        // Avoid overwriting multi definitions
                        if self.file.points.get(name_def.name().index()).type_()
                            == PointType::MultiDefinition
                        {
                            todo!()
                        }
                        self.file.points.set(
                            name_def.index(),
                            Point::new_redirect(self.file_index, class.index(), Locality::Todo),
                        );
                        debug_assert!(self.file.points.get(node_index).calculated());
                        todo!();
                        //self.check_point_cache(node_index).unwrap()
                    }
                    _ => Inferred::new_saved(self.file, node_index),
                },
                PointType::MultiDefinition => {
                    // MultiDefinition means we are on a Name that has a NameDefinition as a
                    // parent.
                    let name = Name::by_index(&self.file.tree, node_index);
                    self.infer_name_definition(name.name_definition().unwrap())
                }
                PointType::Complex | PointType::FileReference => {
                    Inferred::new_saved(self.file, node_index)
                }
                PointType::NodeAnalysis => {
                    unreachable!(
                        "Invalid NodeAnalysis, should not happen on node index {node_index:?}"
                    );
                }
            })
            .or_else(|| {
                if point.calculating() {
                    let node_ref = NodeRef::new(self.file, node_index);
                    debug!(
                        "Found a cycle at #{}, {}:{node_index}: {:?}",
                        node_ref.line(),
                        self.file.file_index(),
                        node_ref.as_code()
                    );
                    node_ref.set_point(Point::new_simple_specific(Specific::Cycle, Locality::Todo));
                    Some(Inferred::new_cycle())
                } else {
                    None
                }
            })
    }

    pub fn infer_name_of_definition_by_index(&mut self, node_index: NodeIndex) -> Inferred {
        self.infer_name_of_definition(Name::by_index(&self.file.tree, node_index))
    }

    pub fn infer_name_of_definition(&mut self, name: Name) -> Inferred {
        let point = self.file.points.get(name.index());
        if point.calculated() {
            if let Some(inf) = self.check_point_cache(name.index()) {
                return inf;
            }
        }
        self.infer_name_definition(name.name_definition().unwrap())
    }

    check_point_cache_with!(pub infer_name_definition, Self::_infer_name_definition, NameDefinition);
    fn _infer_name_definition(&mut self, name_def: NameDefinition) -> Inferred {
        let stmt_like = name_def.expect_stmt_like_ancestor();

        if !self.file.points.get(stmt_like.index()).calculated() {
            match stmt_like {
                StmtLike::SimpleStmts(s) => {
                    self.cache_simple_stmts_name(s, NodeRef::new(self.file, name_def.index()));
                }
                StmtLike::Stmt(stmt) => {
                    self.cache_stmt_name(stmt, NodeRef::new(self.file, name_def.index()));
                }
                StmtLike::Walrus(walrus) => {
                    self.infer_expression(walrus.expression()).save_redirect(
                        self.i_s,
                        self.file,
                        name_def.index(),
                    );
                }
                _ => todo!("{stmt_like:?}"),
            }
        }
        debug_assert!(
            self.file.points.get(name_def.index()).calculated(),
            "{name_def:?}",
        );
        self.infer_name_definition(name_def)
    }

    fn infer_for_if_clauses(&mut self, for_if_clauses: ForIfClauses) {
        for clause in for_if_clauses.iter() {
            let mut needs_await = false;
            let (targets, expr_part, comp_ifs) = match clause {
                ForIfClause::Sync(sync) => sync.unpack(),
                ForIfClause::Async(async_) => {
                    needs_await = true;
                    async_.unpack()
                }
            };
            let clause_node_ref = NodeRef::new(self.file, clause.index());
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
            for comp_if in comp_ifs {
                self.infer_expression_part(comp_if.expression_part());
            }
        }
    }

    fn infer_dict_comprehension(
        &mut self,
        dict_comp: DictComprehension,
        result_context: &mut ResultContext,
    ) -> Inferred {
        let i_s = self.i_s;
        let (key_value, for_if_clauses) = dict_comp.unpack();
        self.infer_for_if_clauses(for_if_clauses);

        let to_dict = |key, value| {
            new_class!(
                self.i_s.db.python_state.dict_node_ref().as_link(),
                key,
                value,
            )
        };
        let found = infer_dict_like(i_s, result_context, |matcher, key_t, value_t| {
            let mut check = |expected_t: &Type, expr, part| {
                let inf =
                    self.infer_expression_with_context(expr, &mut ResultContext::Known(expected_t));
                let t = inf.as_cow_type(i_s);
                if expected_t.is_super_type_of(i_s, matcher, &t).bool() {
                    Some(t.into_owned())
                } else {
                    self.add_issue(
                        expr.index(),
                        IssueType::DictComprehensionMismatch {
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
    }

    fn infer_comprehension_expr_with_context(
        &mut self,
        result_context: &mut ResultContext,
        class: NodeRef,
        mut on_mismatch: impl FnMut(Box<str>, Box<str>) -> IssueType,
        comp: Comprehension,
    ) -> Type {
        let i_s = self.i_s;
        let (comp_expr, for_if_clauses) = comp.unpack();
        self.infer_for_if_clauses(for_if_clauses);

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
                    |got, expected, _: &_| Some(on_mismatch(got, expected)),
                );
                matcher.replace_type_var_likes_for_unknown_type_vars(i_s.db, &inner_expected)
            })
            .unwrap_or_else(|| self.infer_named_expression(comp_expr).as_type(i_s))
    }

    fn infer_list_comprehension(
        &mut self,
        comp: Comprehension,
        result_context: &mut ResultContext,
    ) -> Inferred {
        let t = self.infer_comprehension_expr_with_context(
            result_context,
            self.i_s.db.python_state.list_node_ref(),
            |got, expected| IssueType::ListComprehensionMismatch { got, expected },
            comp,
        );
        Inferred::from_type(new_class!(
            self.i_s.db.python_state.list_node_ref().as_link(),
            t,
        ))
    }

    fn infer_set_comprehension(
        &mut self,
        comp: Comprehension,
        result_context: &mut ResultContext,
    ) -> Inferred {
        let t = self.infer_comprehension_expr_with_context(
            result_context,
            self.i_s.db.python_state.set_node_ref(),
            |got, expected| IssueType::SetComprehensionMismatch { got, expected },
            comp,
        );
        Inferred::from_type(new_class!(
            self.i_s.db.python_state.set_node_ref().as_link(),
            t,
        ))
    }

    pub fn infer_generator_comprehension(
        &mut self,
        comp: Comprehension,
        result_context: &mut ResultContext,
    ) -> Inferred {
        let t = self.infer_comprehension_expr_with_context(
            result_context,
            self.i_s.db.python_state.generator_node_ref(),
            |got, expected| IssueType::GeneratorComprehensionMismatch { got, expected },
            comp,
        );
        Inferred::from_type(new_class!(
            self.i_s.db.python_state.generator_link(),
            t,
            Type::None,
            Type::None,
        ))
    }

    pub(crate) fn add_issue(&self, node_index: NodeIndex, issue: IssueType) {
        let from = NodeRef::new(self.file, node_index);
        from.add_issue(self.i_s, issue);
    }
}

fn instantiate_except(i_s: &InferenceState, t: &Type) -> Type {
    match t {
        // No need to check these here, this is done when calculating diagnostics
        Type::Type(t) => match t.as_ref() {
            inner @ Type::Class(..) => inner.clone(),
            _ => todo!(),
        },
        Type::Any(cause) => Type::Any(*cause),
        Type::Tuple(content) => Inferred::gather_simplified_union(i_s, |add| match &content.args {
            TupleArgs::FixedLen(ts) => {
                for t in ts.iter() {
                    add(Inferred::from_type(instantiate_except(i_s, t)))
                }
            }
            TupleArgs::ArbitraryLen(t) => add(Inferred::from_type(instantiate_except(i_s, t))),
            TupleArgs::WithUnpack(_) => todo!(),
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
        _ => todo!("{t:?}"),
    }
}

fn instantiate_except_star(i_s: &InferenceState, t: &Type) -> Type {
    let result = gather_except_star(i_s, t);
    // When BaseException is used, we need a BaseExceptionGroup. Otherwise when every exception
    // inherits from Exception, ExceptionGroup is used.
    let is_base_exception_group = has_base_exception(i_s.db, &result);
    new_class!(
        match is_base_exception_group {
            false => i_s.db.python_state.exception_group_node_ref().as_link(),
            true => i_s
                .db
                .python_state
                .base_exception_group_node_ref()
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
            _ => todo!(),
        },
        Type::Any(cause) => Type::Any(*cause),
        Type::Tuple(content) => Inferred::gather_simplified_union(i_s, |add| match &content.args {
            TupleArgs::FixedLen(ts) => {
                for t in ts.iter() {
                    add(Inferred::from_type(gather_except_star(i_s, t)))
                }
            }
            TupleArgs::ArbitraryLen(t) => add(Inferred::from_type(gather_except_star(i_s, t))),
            TupleArgs::WithUnpack(_) => todo!(),
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
        _ => todo!("{t:?}"),
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

pub fn first_defined_name(file: &PythonFile, name_index: NodeIndex) -> Option<NodeIndex> {
    let point = file.points.get(name_index);
    if !point.calculated() {
        return None;
    }
    if point.type_() != PointType::MultiDefinition {
        // Happens e.g. for the definition of builtins.type
        debug_assert_eq!(point.type_(), PointType::Specific, "{point:?}");
        return None;
    }
    let mut current = point.node_index();
    loop {
        let point = file.points.get(current);
        debug_assert!(point.calculated());
        debug_assert_eq!(point.type_(), PointType::MultiDefinition);
        // Here we circle through multi definitions to find the first one.
        // Note that multi definition links loop, i.e. A -> B -> C -> A.
        let next = point.node_index();
        if next <= current {
            if next == name_index {
                return None;
            }
            debug_assert_ne!(next, current);
            return Some(next);
        }
        current = next;
    }
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
        inf.type_lookup_and_execute(i_s, from, "__await__", &NoArgs::new(from), &|t| {
            from.add_issue(
                i_s,
                IssueType::IncompatibleTypes {
                    cause: no_lookup_cause,
                    got: t.format_short(i_s.db),
                    expected: "Awaitable[Any]".into(),
                },
            );
        })
        .as_cow_type(i_s)
        .as_ref(),
    );
    if matches!(t, Type::Never) {
        FLOW_ANALYSIS.with(|fa| fa.mark_current_frame_unreachable())
    }
    if expect_not_none && matches!(t, Type::None) {
        from.add_issue(i_s, IssueType::DoesNotReturnAValue("Function".into()));
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

#[derive(Copy, Clone, PartialEq)]
pub enum AssignKind {
    Annotation, // `a: int = 1` or `a = 1 # type: int
    Normal,     // a = 1
    AugAssign,  // a += 1
}
