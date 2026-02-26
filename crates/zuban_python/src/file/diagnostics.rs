use std::{
    borrow::Cow,
    cell::Cell,
    collections::{HashMap, HashSet},
    sync::Arc,
};

use config::TypeCheckerFlags;
use parsa_python_cst::*;

use super::{
    ClassNodeRef, FuncNodeRef, OtherDefinitionIterator, first_defined_name,
    flow_analysis::FLOW_ANALYSIS, inference::await_, on_argument_type_error,
};
use crate::{
    RunCause,
    arguments::{CombinedArgs, InitSubclassArgs, KnownArgs, NoArgs, SimpleArgs},
    database::{
        ClassKind, ComplexPoint, Database, Locality, MetaclassState, OverloadImplementation,
        ParentScope, Point, PointLink, Specific,
    },
    debug,
    diagnostics::{Issue, IssueKind},
    file::{File, Inference, inference::AssignKind},
    format_data::FormatData,
    imports::ImportResult,
    inference_state::InferenceState,
    inferred::{AttributeKind, Inferred, infer_class_method},
    match_::Match,
    matching::{ErrorStrs, Generics, LookupKind, Matcher, OnTypeError, ReplaceSelfInMatcher},
    node_ref::NodeRef,
    params::{Param, WrappedParamType, WrappedStar, matches_params},
    recoverable_error,
    result_context::ResultContext,
    type_::{
        AnyCause, CallableContent, CallableParams, ClassGenerics, DbString, FunctionKind,
        FunctionOverload, GenericItem, GenericsList, IterCause, Literal, LiteralKind, LookupResult,
        NeverCause, ParamType, ReplaceTypeVarLikes, TupleArgs, Type, TypeVarKind, TypeVarLike,
        TypeVarLikes, TypeVarVariance, Variance, dataclass_post_init_func,
        ensure_calculated_dataclass, format_callable_params, merge_class_type_vars,
    },
    type_helpers::{
        Callable, Class, ClassLookupOptions, FirstParamKind, FirstParamProperties, Function,
        Instance, InstanceLookupOptions, LookupDetails, TypeOrClass, cache_class_name,
        check_type_var_variance_validity_for_type, is_private,
    },
    utils::debug_indent,
};

const IGNORED_INHERITANCE_NAMES: [&str; 5] = [
    "__init__",
    "__new__",
    "__init_subclass__",
    "__slots__",
    "__class_getitem__",
];

lazy_static::lazy_static! {
    static ref FORWARD_OP_METHODS: HashSet<&'static str> = HashSet::from([
        "__add__",
        "__sub__",
        "__mul__",
        "__truediv__",
        "__mod__",
        "__divmod__",
        "__floordiv__",
        "__pow__",
        "__matmul__",
        "__and__",
        "__or__",
        "__xor__",
        "__lshift__",
        "__rshift__",
        "__eq__",
        "__ne__",
        "__lt__",
        "__ge__",
        "__gt__",
        "__le__",
    ]);
    static ref REVERSE_OP_METHODS: HashSet<&'static str> = HashSet::from([
        "radd",
        "rsub",
        "rmul",
        "rtruediv",
        "rmod",
        "rdivmod",
        "rfloordiv",
        "rpow",
        "rmatmul",
        "rand",
        "ror",
        "rxor",
        "rlshift",
        "rrshift",
        "eq",
        "ne",
        "lt",
        "ge",
        "gt",
        "le",
    ]);
    pub static ref OVERLAPPING_REVERSE_TO_NORMAL_METHODS: HashMap<&'static str, &'static str> = HashMap::from([
        ("radd", "__add__"),
        ("rsub", "__sub__"),
        ("rmul", "__mul__"),
        ("rtruediv", "__truediv__"),
        ("rmod", "__mod__"),
        ("rdivmod", "__divmod__"),
        ("rfloordiv", "__floordiv__"),
        ("rpow", "__pow__"),
        ("rmatmul", "__matmul__"),
        ("rand", "__and__"),
        ("ror", "__or__"),
        ("rxor", "__xor__"),
        ("rlshift", "__lshift__"),
        ("rrshift", "__rshift__"),
        ("lt", "__gt__"),
        ("ge", "__le__"),
        ("gt", "__lt__"),
        ("le", "__ge__"),
    ]);
    pub static ref INPLACE_TO_NORMAL_METHODS: HashMap<&'static str, &'static str> = HashMap::from([
        ("iadd", "__add__"),
        ("isub", "__sub__"),
        ("imul", "__mul__"),
        ("itruediv", "__truediv__"),
        ("imod", "__mod__"),
        ("ifloordiv", "__floordiv__"),
        ("ipow", "__pow__"),
        ("imatmul", "__matmul__"),
        ("iand", "__and__"),
        ("ior", "__or__"),
        ("ixor", "__xor__"),
        ("ilshift", "__lshift__"),
        ("irshift", "__rshift__"),
    ]);
}

impl Inference<'_, '_, '_> {
    pub fn calculate_module_diagnostics(&self) -> Result<(), ()> {
        let result = self.ensure_module_symbols_flow_analysis();
        self.file.process_delayed_diagnostics(self.i_s.db);
        result
    }

    pub fn ensure_module_symbols_flow_analysis(&self) -> Result<(), ()> {
        diagnostics_for_scope(NodeRef::new(self.file, 0), || {
            FLOW_ANALYSIS.with(|fa| {
                fa.with_new_empty_for_file(self.i_s.db, self.file, || {
                    let file_path = self.file.file_path(self.i_s.db);
                    let _panic_context = utils::panic_context::enter(file_path.to_string());
                    debug!(
                        "Diagnostics for module {file_path} ({})",
                        self.file.file_index(),
                    );
                    debug_assert!(self.i_s.is_file_context(), "{:?}", self.i_s);
                    let _indent = debug_indent();
                    fa.with_frame_that_exports_widened_entries(self.i_s, || {
                        self.calc_stmts_diagnostics(
                            self.file.tree.root().iter_stmt_likes(),
                            None,
                            None,
                        );
                    });
                })
            });
            // Unsafe is fine here, because it only copies existing values. If we used
            // ensure_calculated_types here, the complex values might be increased in size and we
            // therefore need to clone all type vars first.
            let check_type_var_likes: Vec<_> = unsafe { self.file.complex_points.iter() }
                .filter_map(|complex_point| {
                    if let ComplexPoint::TypeVarLike(tvl) = complex_point {
                        // TypeVar likes are reference counted and can be cloned without an issue.
                        Some(tvl.clone())
                    } else {
                        None
                    }
                })
                .collect();
            for tvl in check_type_var_likes {
                tvl.ensure_calculated_types(self.i_s.db)
            }

            if let Some(name_ref) = self.file.lookup_symbol("__getattribute__") {
                name_ref.add_issue(self.i_s, IssueKind::GetattributeInvalidAtModuleLevel);
            }
            if let Some(name_ref) = self.file.lookup_symbol("__getattr__") {
                let actual = name_ref.infer_name_of_definition_by_index(self.i_s);
                let actual = actual.as_cow_type(self.i_s);
                let Type::Callable(callable) = &self.i_s.db.python_state.valid_getattr_supertype
                else {
                    unreachable!();
                };

                if !Type::Callable(Arc::new(callable.remove_first_positional_param().unwrap()))
                    .is_simple_super_type_of(self.i_s, &actual)
                    .bool()
                {
                    name_ref.add_issue(
                        self.i_s,
                        IssueKind::InvalidSpecialMethodSignature {
                            type_: actual.format_short(self.i_s.db),
                            special_method: "__getattr__",
                        },
                    );
                }
            }
        })
    }

    fn check_assignment(&self, assignment: Assignment, class: Option<Class>) {
        self.ensure_cached_assignment(assignment);

        // Check if protocol assignment is invalid
        if class.is_some_and(|cls| {
            cls.is_protocol(self.i_s.db)
                && match assignment.unpack() {
                    AssignmentContent::WithAnnotation(_, annotation, _) => {
                        if self.point(annotation.index()).maybe_specific()
                            == Some(Specific::AnnotationOrTypeCommentFinal)
                        {
                            self.add_issue(
                                annotation.index(),
                                IssueKind::ProtocolMemberCannotBeFinal,
                            );
                        }
                        false
                    }
                    AssignmentContent::Normal(mut targets, _) => {
                        let first_target = targets.next().unwrap();
                        match first_target {
                            Target::Name(n)
                                if targets.next().is_none() && n.as_code() == "__slots__" =>
                            {
                                false
                            }
                            Target::Name(n)
                                if self.check_point_cache(n.index()).is_some_and(|inf| {
                                    matches!(
                                        inf.maybe_complex_point(self.i_s.db),
                                        Some(ComplexPoint::TypeVarLike(_))
                                    )
                                }) =>
                            {
                                false
                            }
                            _ => self.check_for_type_comment(assignment).is_none(),
                        }
                    }
                    AssignmentContent::AugAssign(..) => true,
                }
        }) {
            self.add_issue(
                assignment.index(),
                IssueKind::ProtocolMembersMustHaveExplicitlyDeclaredTypes,
            );
        }
    }

    fn check_import_from(
        &self,
        import_from: ImportFrom,
        class: Option<Class>,
        func: Option<&Function>,
    ) {
        self.cache_import_from(import_from);
        if class.is_some() && func.is_none() {
            match import_from.unpack_targets() {
                ImportFromTargets::Star(_) => {
                    if let Some(ImportResult::File(file)) = self
                        .file
                        .import_from_first_part(self.i_s.db, import_from)
                        .as_deref()
                    {
                        let imported = self.i_s.db.loaded_python_file(*file);
                        if imported.has_unsupported_class_scoped_import(self.i_s.db) {
                            self.add_issue(
                                import_from.index(),
                                IssueKind::UnsupportedClassScopedImport,
                            );
                        }
                    }
                }
                ImportFromTargets::Iterator(iter) => {
                    for target in iter {
                        let name_def = target.name_def();
                        let name_index = name_def.name_index();
                        if first_defined_name(self.file, name_index) != name_index {
                            // Apparently Mypy only checks the first name...
                            continue;
                        }
                        if self
                            .infer_name_def(name_def)
                            .as_cow_type(self.i_s)
                            .is_func_or_overload()
                        {
                            let from = NodeRef::new(self.file, name_def.index());
                            from.add_issue(self.i_s, IssueKind::UnsupportedClassScopedImport);
                            from.set_point(Point::new_specific(
                                Specific::AnyDueToError,
                                from.point().locality(),
                            ))
                        }
                    }
                }
            }
        }
    }

    fn check_valid_raise_type(&self, expr: Expression, allow_none: bool) {
        let inf = self.infer_expression(expr);
        let t = inf.as_cow_type(self.i_s);
        // First check if it's a `raise NotImplemented` (which is invalid)
        if t.maybe_class(self.i_s.db)
            .is_some_and(|c| c.node_ref == self.i_s.db.python_state.notimplemented_type_node_ref())
        {
            NodeRef::new(self.file, expr.index()).add_issue(
                self.i_s,
                IssueKind::BaseExceptionExpectedForRaise {
                    did_you_mean: Some("NotImplementedError".into()),
                },
            );
            return;
        }

        if !valid_raise_type(
            self.i_s,
            NodeRef::new(self.file, expr.index()),
            &t,
            allow_none,
        ) {
            NodeRef::new(self.file, expr.index()).add_issue(
                self.i_s,
                IssueKind::BaseExceptionExpectedForRaise { did_you_mean: None },
            );
        }
    }

    fn add_unreachable_error(&self, start_position: CodeIndex, end_position: CodeIndex) {
        if self.flags().warn_unreachable {
            FLOW_ANALYSIS.with(|fa| {
                fa.report_unreachable_if_not_reported_before(|| {
                    self.file.add_issue(
                        self.i_s,
                        Issue::from_start_stop(
                            start_position,
                            end_position,
                            IssueKind::UnreachableStatement,
                        ),
                    );
                })
            });
        }
    }

    fn calc_stmts_diagnostics(
        &self,
        stmts: StmtLikeIterator,
        class: Option<Class>,
        func: Option<&Function>,
    ) {
        for stmt_like in stmts {
            let point = self.point(stmt_like.parent_index);
            if point.calculated() {
                debug_assert_eq!(point.specific(), Specific::Analyzed);
                continue;
            }
            if self.is_unreachable() {
                if self.stmt_is_allowed_when_unreachable(stmt_like.node) {
                    continue;
                } else {
                    let start = self.file.tree.node_start_position(stmt_like.parent_index);
                    let end = self
                        .file
                        .tree
                        .node_end_position_without_whitespace(stmt_like.parent_index);
                    self.add_unreachable_error(start, end);
                    /*
                    if self.flags().mypy_compatible {
                        // Mypy does not analyze frames that are not reachable. However for normal interaction
                        // in an IDE you typically want to analyze those parts of code, even if they are
                        // unreachable.
                        break;
                    }
                    */
                    if self.i_s.db.run_cause == RunCause::LanguageServer {
                        self.i_s.avoid_errors_within(|avoid_errors_i_s| {
                            self.file
                                .inference(avoid_errors_i_s)
                                .handle_stmt_like(stmt_like, class, func);
                        });
                        continue;
                    }
                    return;
                }
            }
            self.handle_stmt_like(stmt_like, class, func)
        }
    }

    fn handle_stmt_like(
        &self,
        stmt_like: StmtLikeIteratorItem,
        class: Option<Class>,
        func: Option<&Function>,
    ) {
        match stmt_like.node {
            StmtLikeContent::Assignment(assignment) => self.check_assignment(assignment, class),
            StmtLikeContent::StarExpressions(star_exprs) => {
                self.infer_star_expressions(star_exprs, &mut ResultContext::ExpectUnused);
            }
            StmtLikeContent::ReturnStmt(return_stmt) => {
                self.calc_return_stmt_diagnostics(func, return_stmt);
                // If we are not within a function we should not mark the frame unreachable,
                // because it is valid within a function
                if func.is_some() {
                    self.mark_current_frame_unreachable()
                }
            }
            StmtLikeContent::YieldExpr(yield_expr) => {
                self.infer_yield_expr(yield_expr, &mut ResultContext::ExpectUnused);
            }
            StmtLikeContent::RaiseStmt(raise_stmt) => {
                if let Some((expr, from_expr)) = raise_stmt.unpack() {
                    self.check_valid_raise_type(expr, false);
                    if let Some(from_expr) = from_expr {
                        self.check_valid_raise_type(from_expr, true)
                    }
                }
                self.mark_current_frame_unreachable()
            }
            StmtLikeContent::ImportFrom(import_from) => {
                self.check_import_from(import_from, class, func)
            }
            StmtLikeContent::ImportName(import_name) => {
                self.cache_import_name(import_name);
            }
            StmtLikeContent::PassStmt(_) => {}
            StmtLikeContent::GlobalStmt(global) => {
                if self.i_s.in_module_context() {
                    // TODO actually use a future assignment to it to determine the type.
                    for name_def in global.iter_name_defs() {
                        self.set_point(
                            name_def.index(),
                            Point::new_specific(Specific::AnyDueToError, Locality::File),
                        );
                    }
                    self.add_issue(global.index(), IssueKind::GlobalAtModuleLevel);
                }
            }
            StmtLikeContent::NonlocalStmt(_) => {}
            StmtLikeContent::AssertStmt(assert_stmt) => {
                self.flow_analysis_for_assert(assert_stmt);
            }
            StmtLikeContent::BreakStmt(b) => self.flow_analysis_for_break_stmt(b),
            StmtLikeContent::ContinueStmt(c) => self.flow_analysis_for_continue_stmt(c),
            StmtLikeContent::DelStmt(d) => {
                self.set_calculating_on_del_targets(d.targets());
                self.flow_analysis_for_del_stmt(d.targets());
            }
            StmtLikeContent::TypeAlias(type_alias) => {
                self.ensure_compute_type_alias_from_syntax(type_alias);
                self.assign_type_alias_name(type_alias);
            }
            StmtLikeContent::FunctionDef(f) => self.maybe_delay_func_diagnostics(f, class, func),
            StmtLikeContent::ClassDef(class) => self.bind_class_names(class),
            StmtLikeContent::Decorated(decorated) => match decorated.decoratee() {
                Decoratee::FunctionDef(f) => {
                    self.ensure_cached_decorators(decorated);
                    self.maybe_delay_func_diagnostics(f, class, func)
                }
                Decoratee::ClassDef(class) => self.bind_class_names(class),
                Decoratee::AsyncFunctionDef(f) => {
                    self.ensure_cached_decorators(decorated);
                    self.maybe_delay_func_diagnostics(f, class, func)
                }
            },
            StmtLikeContent::IfStmt(if_stmt) => {
                self.flow_analysis_for_if_stmt(if_stmt, class, func)
            }
            StmtLikeContent::ForStmt(for_stmt) => {
                self.flow_analysis_for_for_stmt(for_stmt, class, func, false)
            }
            StmtLikeContent::TryStmt(try_stmt) => {
                self.flow_analysis_for_try_stmt(try_stmt, class, func)
            }
            StmtLikeContent::WhileStmt(while_stmt) => {
                self.flow_analysis_for_while_stmt(while_stmt, class, func)
            }
            StmtLikeContent::WithStmt(with_stmt) => {
                self.calc_with_stmt(with_stmt, class, func, false)
            }
            StmtLikeContent::MatchStmt(match_stmt) => {
                self.flow_analysis_for_match_stmt(match_stmt, class, func)
            }
            StmtLikeContent::AsyncStmt(async_stmt) => match async_stmt.unpack() {
                AsyncStmtContent::FunctionDef(f) => {
                    self.maybe_delay_func_diagnostics(f, class, func)
                }
                AsyncStmtContent::ForStmt(for_stmt) => {
                    self.flow_analysis_for_for_stmt(for_stmt, class, func, true)
                }
                AsyncStmtContent::WithStmt(with_stmt) => {
                    self.calc_with_stmt(with_stmt, class, func, true)
                }
            },
            StmtLikeContent::BrokenScope(broken) => {
                // For now process these as part of the current scope, since this is part of
                // the parser's error recovery
                self.calc_stmts_diagnostics(broken.iter_stmt_likes(), class, func)
            }
            StmtLikeContent::Error(_) | StmtLikeContent::Newline => {}
        };
        self.set_point(
            stmt_like.parent_index,
            Point::new_specific(Specific::Analyzed, Locality::Todo),
        );
    }

    pub fn set_calculating_on_del_targets(&self, del_targets: DelTargets) {
        for del_target in del_targets.iter() {
            match del_target {
                DelTarget::Target(target) => self.set_calculating_on_target(target),
                DelTarget::DelTargets(del_targets) => {
                    self.set_calculating_on_del_targets(del_targets)
                }
            }
        }
    }

    fn stmt_is_allowed_when_unreachable(&self, s: StmtLikeContent) -> bool {
        // In Mypy this is called is_noop_for_reachability
        match s {
            StmtLikeContent::RaiseStmt(_) | StmtLikeContent::PassStmt(_) => true,
            StmtLikeContent::AssertStmt(assert_stmt) => {
                match assert_stmt.unpack().0.maybe_unpacked_atom() {
                    Some(AtomContent::Bool(b)) if b.as_code() == "False" => true,
                    Some(AtomContent::Int(i)) if i.parse() == 0.into() => true,
                    _ => false,
                }
            }
            StmtLikeContent::StarExpressions(star_expr) => {
                star_expr.maybe_simple_expression().is_some_and(|expr| {
                    let ExpressionContent::ExpressionPart(ExpressionPart::Primary(primary)) =
                        expr.unpack()
                    else {
                        return false;
                    };
                    matches!(primary.second(), PrimaryContent::Execution(_))
                        && self
                            .i_s
                            .avoid_errors_within(|i_s| {
                                matches!(
                                    self.file
                                        .inference(i_s)
                                        .infer_primary(primary, &mut ResultContext::Unknown)
                                        .as_cow_type(self.i_s)
                                        .as_ref(),
                                    Type::Never(NeverCause::Explicit)
                                )
                            })
                            .0
                })
            }
            _ => false,
        }
    }

    fn calc_with_stmt(
        &self,
        with_stmt: WithStmt,
        class: Option<Class>,
        func: Option<&Function>,
        is_async: bool,
    ) {
        let (with_items, block) = with_stmt.unpack();
        let mut exceptions_maybe_suppressed = false;
        for with_item in with_items.iter() {
            let exit_result = self.cache_with_item(with_item, is_async);
            // Mypy comments about this:
            // Based on the return type, determine if this context manager 'swallows'
            // exceptions or not. We determine this using a heuristic based on the
            // return type of the __exit__ method -- see the discussion in
            // https://github.com/python/mypy/issues/7214 and the section about context managers
            // in https://github.com/python/typeshed/blob/main/CONTRIBUTING.md#conventions
            // for more details.
            exceptions_maybe_suppressed |= match exit_result.as_cow_type(self.i_s).as_ref() {
                Type::Class(c) if c.link == self.i_s.db.python_state.bool_link() => true,
                Type::Literal(l) if matches!(l.kind, LiteralKind::Bool(true)) => true,
                _ => false,
            };
        }
        if exceptions_maybe_suppressed {
            // We create a new frame to swallow unreachability.
            self.flow_analysis_for_with_stmt_when_exceptions_maybe_suppressed(|| {
                self.calc_block_diagnostics(block, class, func);
            })
        } else {
            self.calc_block_diagnostics(block, class, func);
        }
    }

    fn calc_untyped_block_diagnostics(&self, block: Block, from_type_var_value: bool) {
        let check_class = |class: ClassDef| {
            // Classes need to be initialized, otherwise there can be issues when they are
            // references e.g. in annotations in untyped code.
            cache_class_name(NodeRef::new(self.file, class.name_def().index()), class);
            NodeRef::new(self.file, class.index()).ensure_cached_class_infos(self.i_s);
            self.calc_untyped_block_diagnostics(class.block(), from_type_var_value)
        };
        let check_func = |func: FunctionDef| {
            self.calc_untyped_block_diagnostics(func.body(), from_type_var_value)
        };
        let check_for = |for_stmt: ForStmt| {
            let (_, _, block, else_block) = for_stmt.unpack();
            self.calc_untyped_block_diagnostics(block, from_type_var_value);
            if let Some(else_block) = else_block {
                self.calc_untyped_block_diagnostics(else_block.block(), from_type_var_value)
            }
        };
        let check_with = |with_stmt: WithStmt| {
            self.calc_untyped_block_diagnostics(with_stmt.unpack().1, from_type_var_value)
        };
        'outer: for stmt_like in block.iter_stmt_likes() {
            match stmt_like.node {
                StmtLikeContent::StarExpressions(star_exprs) => {
                    let Some(expr) = star_exprs.maybe_simple_expression() else {
                        continue;
                    };
                    let ExpressionContent::ExpressionPart(ExpressionPart::Primary(p)) =
                        expr.unpack()
                    else {
                        continue;
                    };
                    let PrimaryOrAtom::Atom(atom) = p.first() else {
                        continue;
                    };
                    let AtomContent::Name(n) = atom.unpack() else {
                        continue;
                    };
                    if n.as_code() == "reveal_type" && !self.point(n.index()).calculated() {
                        self.infer_name_reference(n);
                        let PrimaryContent::Execution(_) = p.second() else {
                            continue;
                        };
                        let n = NodeRef::new(self.file, p.index());
                        if !from_type_var_value {
                            n.add_issue(
                                self.i_s,
                                IssueKind::Note("Revealed type is \"Any\"".into()),
                            );
                            n.add_issue(
                                self.i_s,
                                IssueKind::Note(
                                    "'reveal_type' always outputs 'Any' in unchecked functions"
                                        .into(),
                                ),
                            );
                        }
                    }
                }
                StmtLikeContent::Assignment(a) => {
                    let from = NodeRef::new(self.file, a.index());
                    let add_annotation_in_untyped_issue = || {
                        if !from_type_var_value {
                            from.add_issue(self.i_s, IssueKind::AnnotationInUntypedFunction);
                        }
                    };
                    match a.unpack() {
                        AssignmentContent::Normal(targets, _) => {
                            if let Some(type_comment) = self.check_for_type_comment(a) {
                                add_annotation_in_untyped_issue();
                                for target in targets {
                                    if let Target::Name(n) | Target::NameExpression(_, n) = target {
                                        type_comment.inferred.clone().save_redirect(
                                            self.i_s,
                                            self.file,
                                            n.index(),
                                        );
                                    } else {
                                        self.assign_any_to_untyped_target(target)
                                    }
                                }
                            } else {
                                for target in targets {
                                    self.assign_any_to_untyped_target(target)
                                }
                            }
                        }
                        AssignmentContent::WithAnnotation(target, annotation, right_side) => {
                            // TODO what about self.x: Final?
                            /*
                            if matches!(
                                value.maybe_complex_point(self.i_s.db),
                                Some(ComplexPoint::IndirectFinal(_))
                            ) {
                                value.clone().save_redirect(self.i_s, self.file, index);
                            }
                            */
                            self.ensure_cached_annotation(annotation, right_side.is_some());
                            if let Target::Name(n) | Target::NameExpression(_, n) = target {
                                self.set_point(
                                    n.index(),
                                    Point::new_redirect(
                                        self.file.file_index,
                                        annotation.index(),
                                        Locality::Todo,
                                    ),
                                );
                            }
                            add_annotation_in_untyped_issue()
                        }
                        AssignmentContent::AugAssign(target, _, _) => {
                            self.assign_any_to_untyped_target(target)
                        }
                    };
                }
                StmtLikeContent::ImportFrom(i) => self.cache_import_from(i),
                StmtLikeContent::ImportName(i) => self.cache_import_name(i),
                StmtLikeContent::ClassDef(class) => check_class(class),
                StmtLikeContent::FunctionDef(func) => check_func(func),
                StmtLikeContent::Decorated(dec) => match dec.decoratee() {
                    Decoratee::ClassDef(c) => check_class(c),
                    Decoratee::FunctionDef(f) | Decoratee::AsyncFunctionDef(f) => check_func(f),
                },
                StmtLikeContent::AsyncStmt(async_stmt) => match async_stmt.unpack() {
                    AsyncStmtContent::FunctionDef(f) => check_func(f),
                    AsyncStmtContent::ForStmt(for_stmt) => check_for(for_stmt),
                    AsyncStmtContent::WithStmt(w) => check_with(w),
                },
                StmtLikeContent::IfStmt(if_stmt) => {
                    for b in if_stmt.iter_blocks() {
                        let name_binder_check = self
                            .point(b.first_leaf_index())
                            .maybe_calculated_and_specific();
                        let block = match b {
                            IfBlockType::If(_, block) => block,
                            IfBlockType::Else(e) => e.block(),
                        };
                        match name_binder_check {
                            Some(
                                Specific::IfBranchAlwaysReachableInTypeCheckingBlock
                                | Specific::IfBranchAlwaysReachableInNameBinder,
                            ) => self.calc_untyped_block_diagnostics(block, from_type_var_value),
                            Some(Specific::IfBranchAlwaysUnreachableInNameBinder) => {
                                continue 'outer;
                            }
                            Some(Specific::IfBranchAfterAlwaysReachableInNameBinder) => {
                                continue 'outer;
                            }
                            _ => self.calc_untyped_block_diagnostics(block, from_type_var_value),
                        }
                    }
                }
                StmtLikeContent::WhileStmt(while_stmt) => {
                    let (_, block, else_block) = while_stmt.unpack();
                    self.calc_untyped_block_diagnostics(block, from_type_var_value);
                    if let Some(else_block) = else_block {
                        self.calc_untyped_block_diagnostics(else_block.block(), from_type_var_value)
                    }
                }
                StmtLikeContent::ForStmt(for_stmt) => check_for(for_stmt),
                StmtLikeContent::TryStmt(try_stmt) => {
                    for b in try_stmt.iter_blocks() {
                        let block = match b {
                            TryBlockType::Try(b) => b,
                            TryBlockType::Except(e) => e.unpack().1,
                            TryBlockType::ExceptStar(e) => e.unpack().1,
                            TryBlockType::Else(e) => e.block(),
                            TryBlockType::Finally(f) => f.block(),
                        };
                        self.calc_untyped_block_diagnostics(block, from_type_var_value)
                    }
                }
                StmtLikeContent::WithStmt(w) => check_with(w),
                StmtLikeContent::MatchStmt(match_stmt) => {
                    for case_block in match_stmt.unpack().1 {
                        self.calc_untyped_block_diagnostics(
                            case_block.unpack().2,
                            from_type_var_value,
                        )
                    }
                }
                _ => (),
            }
        }
    }

    fn assign_any_to_untyped_target(&self, target: Target) {
        match target {
            Target::NameExpression(_, n) => {
                // Assign any to potential self assignments
                Inferred::new_any_from_error().save_redirect(self.i_s, self.file, n.index());
            }
            Target::Tuple(targets) => {
                for target in targets {
                    self.assign_any_to_untyped_target(target)
                }
            }
            Target::Starred(s) => self.assign_any_to_untyped_target(s.as_target()),
            Target::Name(_) | Target::IndexExpression(_) => (),
        }
    }

    fn check_type_params_redefinitions(&self, parent_scope: ParentScope, type_params: TypeParams) {
        for (i, type_param) in type_params.iter().enumerate() {
            for other in type_params.iter().skip(i + 1) {
                let name_def = type_param.name_def();
                if name_def.as_code() == other.name_def().as_code() {
                    self.add_issue(
                        name_def.index(),
                        IssueKind::AlreadyDefinedTypeParameter {
                            name: name_def.as_code().into(),
                        },
                    );
                }
            }
        }
        self.check_parent_type_params_redefinitions(parent_scope, type_params)
    }

    fn check_parent_type_params_redefinitions(
        &self,
        parent_scope: ParentScope,
        type_params: TypeParams,
    ) {
        let type_vars = match parent_scope {
            ParentScope::Module => return,
            ParentScope::Function(index) => {
                let func = FuncNodeRef::new(self.file, index);
                self.check_parent_type_params_redefinitions(func.parent_scope(), type_params);
                func.type_vars(self.i_s.db)
            }
            ParentScope::Class(index) => {
                let class = ClassNodeRef::new(self.file, index);
                let storage = class.class_storage();
                self.check_parent_type_params_redefinitions(storage.parent_scope, type_params);
                class.type_vars(self.i_s)
            }
        };
        for type_param in type_params.iter() {
            for parent_type_var in type_vars.iter() {
                let name_def = type_param.name_def();
                if name_def.as_code() == parent_type_var.name(self.i_s.db) {
                    self.add_issue(
                        name_def.index(),
                        IssueKind::AlreadyDefinedTypeParameter {
                            name: name_def.as_code().into(),
                        },
                    );
                }
            }
        }
    }

    pub(crate) fn calc_block_diagnostics(
        &self,
        block: Block,
        class: Option<Class>,
        func: Option<&Function>,
    ) {
        self.calc_stmts_diagnostics(block.iter_stmt_likes(), class, func)
    }

    pub fn calculate_class_block_diagnostics(&self, c: Class, block: Block) -> Result<(), ()> {
        diagnostics_for_scope(NodeRef::new(self.file, block.index()), || {
            FLOW_ANALYSIS.with(|fa| {
                fa.with_class_frame(self.i_s, || {
                    self.calc_block_diagnostics(block, Some(c), None);
                });
                fa.add_delayed_class_diagnostics(c.as_link())
            })
        })
    }

    fn bind_class_names(&self, class: ClassDef) {
        debug!(
            "Diagnostics for class {} ({}({}:{}):#{})",
            class.name().as_code(),
            self.file_path(),
            self.file.file_index,
            class.index(),
            NodeRef::new(self.file, class.index()).line_one_based(self.i_s.db)
        );
        let _indent = debug_indent();

        let (type_params, arguments, block) = class.unpack();
        cache_class_name(NodeRef::new(self.file, class.name_def().index()), class);
        let class_node_ref = ClassNodeRef::new(self.file, class.index());
        class_node_ref.ensure_cached_class_infos(self.i_s);
        let db = self.i_s.db;

        if let Some(decorated) = class.maybe_decorated() {
            // TODO we pretty much just ignore the fact that a decorated class can also be an enum.
            let mut inferred = Inferred::from_saved_node_ref(class_node_ref.into());
            for decorator in decorated.decorators().iter_reverse() {
                let decorate = self.infer_decorator(decorator);
                inferred = decorate.execute(
                    self.i_s,
                    &KnownArgs::new(&inferred, NodeRef::new(self.file, decorator.index())),
                );
            }
            // TODO for now don't save class decorators, because they are really not used in mypy.
            // let saved = inferred.save_redirect(i_s, name_def.file, name_def.node_index);
        }

        let class_infos = class_node_ref.use_cached_class_infos(db);
        let c = Class::with_self_generics(db, class_node_ref);
        self.check_class_keyword_params(c, arguments);

        if let Some(type_params) = type_params {
            self.check_type_params_redefinitions(c.class_storage.parent_scope, type_params);
            // We have to delay type variance inference, because we only know it after all the
            // functions have been dealt with.
            FLOW_ANALYSIS.with(|fa| fa.add_delayed_type_params_variance_inference(class_node_ref))
        }

        if matches!(class_infos.kind, ClassKind::TypedDict) {
            // TypedDicts are special, because they really only contain annotations and no methods.
            // We skip all of this logic, because there's custom logic for TypedDicts.
            return;
        }
        if let MetaclassState::Some(link) = class_infos.metaclass
            && link == db.python_state.enum_meta_link()
            && let Some(t) = class_infos.undefined_generics_type.get()
            && let Type::Enum(enum_) = t.as_ref()
        {
            // Precalculate the enum values here.
            // We need to calculate here, because otherwise the normal class
            // calculation will do it for us, which will infer different values.
            for member in enum_.members.iter() {
                if member.value.is_some() {
                    member.infer_value(self.i_s, enum_);
                }
            }
        }
        if let Some(t) = class_infos.undefined_generics_type.get()
            && let Type::Dataclass(dc) = t.as_ref()
        {
            ensure_calculated_dataclass(dc, db);
        }

        let i_s = self.i_s.with_class_context(&c);
        let result = self
            .file
            .inference(&i_s)
            .calculate_class_block_diagnostics(c, block);
        if !result.is_ok() {
            recoverable_error!(
                "Calculating the class block failed for: {} line #{} in {}",
                class.name().as_code(),
                class_node_ref.line_one_based(i_s.db),
                self.file_path()
            );
        }
    }

    pub fn ensure_class_diagnostics(&self, class_node_ref: ClassNodeRef) {
        let class = class_node_ref.maybe_class().unwrap();
        let db = self.i_s.db;
        let (type_params, arguments, _) = class.unpack();
        let c = Class::with_self_generics(db, class_node_ref);
        let class_infos = class_node_ref.use_cached_class_infos(db);

        let type_vars = class_node_ref.use_cached_type_vars(db);
        type_vars.add_error_if_default_after_type_var_tuple(|issue| {
            c.add_issue_on_name(db, issue);
        });

        if let Some(t) = class_infos.undefined_generics_type.get() {
            match t.as_ref() {
                Type::Dataclass(d) => {
                    ensure_calculated_dataclass(d, db);
                    if d.options.slots && c.lookup_symbol(self.i_s, "__slots__").is_some() {
                        c.add_issue_on_name(
                            db,
                            IssueKind::DataclassPlusExplicitSlots {
                                class_name: c.name().into(),
                            },
                        );
                    }
                }
                Type::Enum(e) => {
                    if let Some(expected) =
                        c.lookup_symbol(self.i_s, "_value_").into_maybe_inferred()
                        // The customized __init__ can set the _value_.
                        && !e.has_customized_dunder_init(self.i_s)
                    {
                        for member in e.members.iter() {
                            if let Some(value) = member.value {
                                let actual = member.infer_value(self.i_s, e);
                                if !expected
                                    .as_cow_type(self.i_s)
                                    .is_simple_super_type_of(
                                        self.i_s,
                                        &actual.as_cow_type(self.i_s),
                                    )
                                    .bool()
                                {
                                    NodeRef::from_link(db, value).add_type_issue(
                                        db,
                                        IssueKind::EnumValueMustMatchUnderscoreValue {
                                            actual: actual.format_short(self.i_s),
                                            expected: expected.format_short(self.i_s),
                                        },
                                    );
                                }
                            }
                        }
                    }
                }
                _ => (),
            }
        }

        if let MetaclassState::Some(link) = class_infos.metaclass
            && link == db.python_state.enum_meta_link()
        {
            // Check if __new__ was correctly used in combination with enums (1)
            // Also check if mixins appear after enums (2)
            let mut had_new = 0;
            let mut enum_spotted: Option<Class> = None;
            for base in c.bases(db) {
                if let TypeOrClass::Class(c) = &base {
                    let is_enum = c.use_cached_class_infos(db).kind == ClassKind::Enum;
                    let has_mixin_enum_new = if is_enum {
                        c.bases(db).any(|inner| match inner {
                            TypeOrClass::Class(inner) => {
                                inner.use_cached_class_infos(db).kind != ClassKind::Enum
                                    && inner.has_customized_enum_new(self.i_s)
                            }
                            TypeOrClass::Type(_) => false,
                        })
                    } else {
                        c.has_customized_enum_new(self.i_s)
                    };
                    // (1)
                    if has_mixin_enum_new {
                        had_new += 1;
                        if had_new > 1 {
                            class_node_ref.add_issue_on_name(
                                db,
                                IssueKind::EnumMultipleMixinNew {
                                    extra: c.qualified_name(db).into(),
                                },
                            );
                        }
                    }
                    // (2)
                    match enum_spotted {
                        Some(after) if !is_enum => {
                            class_node_ref.add_issue_on_name(
                                db,
                                IssueKind::EnumMixinNotAllowedAfterEnum {
                                    after: after.qualified_name(db).into(),
                                },
                            );
                        }
                        _ => {
                            if is_enum {
                                enum_spotted = Some(*c);
                            }
                        }
                    }
                }
            }
        }

        let add_issue_to_arguments =
            |issue| NodeRef::new(self.file, arguments.unwrap().index()).add_issue(self.i_s, issue);
        for base in class_infos.base_types() {
            check_type_var_variance_for_base(
                self.i_s,
                c.node_ref.as_link(),
                type_vars,
                base,
                add_issue_to_arguments,
            );
        }
        check_multiple_inheritance(
            self.i_s,
            || class_infos.base_types(),
            // Don't check symbols if they are part of the instance that we are currently using.
            |name| {
                c.lookup_symbol(self.i_s, name)
                    .into_maybe_inferred()
                    .is_none()
            },
            add_issue_to_arguments,
        );

        let i_s = self.i_s.with_class_context(&c);
        for (name, index) in c.class_storage.class_symbol_table.iter() {
            self.file
                .inference(&i_s)
                .check_function_override(c, *index, name)
        }
        if let Some(node_index) = c
            .class_storage
            .class_symbol_table
            .lookup_symbol("__slots__")
        {
            let inf = self.infer_name_of_definition_by_index(node_index);
            let t = inf.as_cow_type(&i_s);
            if !t
                .is_simple_sub_type_of(&i_s, &i_s.db.python_state.iterable_of_str)
                .bool()
            {
                NodeRef::new(self.file, node_index).add_issue(
                    &i_s,
                    IssueKind::InvalidSlotsDefinition {
                        actual: t.format_short(i_s.db),
                    },
                );
            }
        }
        if let Some(node_index) = c
            .class_storage
            .class_symbol_table
            .lookup_symbol("__match_args__")
        {
            let inf = self.infer_name_of_definition_by_index(node_index);
            let t = inf.as_type(&i_s).ensure_dunder_match_args_with_literals(
                db,
                Some(PointLink::new(self.file.file_index, node_index)),
            );
            let is_ok = match t {
                Type::Tuple(tup) => {
                    if let TupleArgs::FixedLen(tup_entries) = &tup.args {
                        tup_entries.iter().all(|t| {
                            matches!(t, Type::Literal(literal)
                                     if matches!(&literal.kind, LiteralKind::String(_)))
                        })
                    } else {
                        tup.args.maybe_any().is_some()
                    }
                }
                Type::Any(_) => true,
                _ => false,
            };
            if !is_ok {
                NodeRef::new(self.file, node_index)
                    .add_issue(&i_s, IssueKind::InvalidDunderMatchArgs);
            }
        }
        match class_infos.kind {
            ClassKind::Protocol => {
                for (name, name_index) in c.class_storage.self_symbol_table.iter() {
                    if c.class_storage
                        .class_symbol_table
                        .lookup_symbol(name)
                        .is_none()
                    {
                        let from = NodeRef::new(self.file, *name_index);
                        // Apparently Mypy raises two issues here.
                        from.add_issue(
                            self.i_s,
                            IssueKind::ProtocolMembersCannotHaveSelfVariableDefinitions,
                        );
                        from.add_issue(
                            self.i_s,
                            IssueKind::AttributeError {
                                object: format!("\"{}\"", c.name()).into(),
                                name: name.into(),
                            },
                        );
                    }
                }
                if type_params.is_none() {
                    check_protocol_type_var_variances(self.i_s, c)
                }
            }
            ClassKind::NamedTuple => {
                if let Some(nt) = class_infos.mro.iter().find_map(|c| match &c.type_ {
                    Type::NamedTuple(nt) if !c.is_direct_base => Some(nt),
                    _ => None,
                }) {
                    for param in nt.params() {
                        if let Some(check_name) = param.name(self.i_s.db)
                            && let Some(in_class_same_name_index) =
                                c.class_storage.class_symbol_table.lookup_symbol(check_name)
                        {
                            NodeRef::new(self.file, in_class_same_name_index).add_type_issue(
                                self.i_s.db,
                                IssueKind::NamedTupleOverwriteInSubclass,
                            );
                        }
                    }
                }
            }
            _ => (),
        }
    }

    fn check_class_keyword_params(&self, c: Class, arguments: Option<Arguments>) {
        let lookup_details = c.lookup(
            self.i_s,
            "__init_subclass__",
            ClassLookupOptions::new(&|issue| {
                debug!("TODO __init_subclass__ error ignored: {issue:?}");
                false
            })
            .with_ignore_self(),
        );
        let db = self.i_s.db;
        let mut checked_keywords = false;
        if c.maybe_dataclass(db).is_none()
            && c.maybe_typed_dict().is_none()
            && c.maybe_metaclass(db).is_none_or(|m| {
                m == db.python_state.bare_type_node_ref().as_link()
                    || m == db.python_state.abc_meta_link()
            })
            && !c.incomplete_mro(db)
            && let Some(init_subclass) = lookup_details.lookup.into_maybe_inferred()
        {
            let details = match arguments {
                Some(args) => ArgumentsDetails::Node(args),
                None => ArgumentsDetails::None,
            };
            let args = SimpleArgs::new(
                // Provide the class scope, because in conformance tests there's once case where a
                // generic is bound to the class.
                self.i_s.with_class_context(&c),
                self.file,
                c.node_index,
                details,
            );
            init_subclass.execute_with_details(
                self.i_s,
                &InitSubclassArgs(args),
                &mut ResultContext::ExpectUnused,
                OnTypeError::new(&on_argument_type_error),
            );
            checked_keywords = true;
        }

        if let Some(arguments) = arguments {
            for argument in arguments.iter() {
                match argument {
                    Argument::Positional(_) => (), // These are checked in ensure_cached_class_infos
                    Argument::Keyword(kwarg) => {
                        if !checked_keywords {
                            let (name, expr) = kwarg.unpack();
                            if name.as_str() != "metaclass" {
                                // Generate diagnostics
                                self.infer_expression(expr);
                                debug!(
                                    "TODO shouldn't we handle this? In \
                                testNewAnalyzerClassKeywordsForward it's ignored..."
                                )
                            }
                        }
                    }
                    Argument::Star(starred) => {
                        NodeRef::new(self.file, starred.index())
                            .add_type_issue(db, IssueKind::InvalidBaseClass);
                    }
                    Argument::StarStar(double_starred) => {
                        if !checked_keywords {
                            NodeRef::new(self.file, double_starred.index())
                                .add_type_issue(db, IssueKind::InvalidBaseClass);
                        }
                    }
                }
            }
        }
    }

    fn check_function_override(&self, c: Class, index: NodeIndex, name: &str) {
        let i_s = self.i_s;
        let Some(func_def) = NodeRef::new(c.node_ref.file, index)
            .expect_name()
            .name_def()
            .unwrap()
            .maybe_name_of_func()
        else {
            return;
        };

        if is_private(name) {
            return;
        }
        let from = NodeRef::new(self.file, index);

        if name == "__post_init__"
            && let Some(dataclass) = c.maybe_dataclass(i_s.db)
        {
            if dataclass.is_dataclass_transform() {
                // For now don't skip dataclass transform. It is a very special case and I
                // don't know how that would look like. If we want to do it well, we would need
                // to test it well.
                return;
            }
            let override_details = Instance::new(c, None).lookup_on_self(
                self.i_s,
                &|issue| from.add_issue(i_s, issue),
                name,
                LookupKind::OnlyType,
            );
            let __post_init__ = dataclass_post_init_func(&dataclass, i_s.db);
            let original_details = LookupDetails {
                class: TypeOrClass::Type(Cow::Owned(Type::Dataclass(dataclass.clone()))),
                lookup: LookupResult::UnknownName(Inferred::from_type(Type::Callable(Arc::new(
                    __post_init__.clone(),
                )))),
                attr_kind: AttributeKind::DefMethod { is_final: false },
                mro_index: None,
            };
            check_override(
                i_s,
                from,
                original_details,
                &override_details,
                name,
                |_| "dataclass".into(),
                Some(&|| {
                    let params = format_callable_params(
                        &FormatData::new_short(i_s.db),
                        false,
                        __post_init__.expect_simple_params().iter(),
                        false,
                    );
                    format!("def __post_init__(self, {params}) -> None")
                }),
            );
            return;
        }

        let should_check_func_override = || {
            func_def.is_typed() || {
                let flags = self.flags();
                flags.check_untyped_defs
                    && (func_def.maybe_decorated().is_none() || flags.check_untyped_overrides)
            }
        };

        // Mypy completely ignores untyped functions.
        if IGNORED_INHERITANCE_NAMES.contains(&name) || !should_check_func_override() {
            let original_details = c.lookup(
                i_s,
                name,
                ClassLookupOptions::new(&|_| false).with_ignore_self(),
            );
            add_error_if_final(i_s, from, name, &original_details);
            return;
        }

        let func_node_ref = FuncNodeRef::new(self.file, func_def.index());
        Function::new_with_unknown_parent(i_s.db, *func_node_ref).cache_func_from_diagnostics(i_s);
        // Calculate if there is an @override decorator
        let mut has_override_decorator = false;
        if let Some(ComplexPoint::FunctionOverload(overload)) = func_node_ref.maybe_complex() {
            has_override_decorator = overload.is_override;
        } else if let Some(decorated) = func_def.maybe_decorated() {
            let decorators = decorated.decorators();
            for decorator in decorators.iter() {
                if let Some(redirect) =
                    NodeRef::new(self.file, decorator.index()).maybe_redirect(i_s.db)
                    && redirect.as_link() == i_s.db.python_state.typing_override_link
                {
                    has_override_decorator = true;
                }
            }
        }
        find_and_check_override(self.i_s, from, c, name, has_override_decorator)
    }

    fn maybe_delay_func_diagnostics(
        &self,
        f: FunctionDef,
        class: Option<Class>,
        in_func: Option<&Function>,
    ) {
        let func = Function::new(NodeRef::new(self.file, f.index()), class);
        // In general we need a few work arounds here, because we try to not infer the full
        // function types here. Otherwise we would have to infer decorators, function returns and
        // other things here already that could easily be done later.
        {
            // We need to make sure that the first name always has a definition inserted so flow
            // analysis works normal.
            let n = f.name_def();
            if first_defined_name(self.file, n.name_index()) == n.name_index() {
                self.add_initial_name_definition(n);
            }

            if self.in_conditional() {
                // Conditionals functions need narrowing and we therefore initialize them here.
                let current_index = f.name().index();
                // Also cache all the functions before this definition to make sure that overloads are
                // loaded correctly
                for n in OtherDefinitionIterator::new(&self.file.points, current_index) {
                    if n < current_index {
                        let name_def = NodeRef::new(self.file, n)
                            .name_def_ref_of_name()
                            .expect_name_def();
                        if let Some(f) = name_def.maybe_name_of_func() {
                            Function::new(NodeRef::new(self.file, f.index()), class)
                                .cache_func_from_diagnostics(self.i_s);
                        }
                    }
                }
                func.cache_func_from_diagnostics(self.i_s);
            }
        }
        FLOW_ANALYSIS.with(|fa| {
            if in_func.is_some() {
                // TODO Currently the delayed func checking works in weird ways where we have to
                // cache the function signature here.
                func.cache_func_from_diagnostics(self.i_s);
                fa.add_delayed_func_with_reused_narrowings_for_nested_function(func.node_ref)
            } else {
                fa.add_delayed_func(func.as_link(), class.map(|c| c.node_ref.as_link()))
            }
        })
    }

    pub fn is_empty_generator_function(&self, func_node: FunctionDef) -> bool {
        let mut iterator = func_node.body().iter_stmt_likes();
        let Some(first) = iterator.next() else {
            return false;
        };
        match first.node {
            StmtLikeContent::ReturnStmt(r) => {
                if let Some(star_exprs) = r.star_expressions()
                    && !star_exprs.is_none_literal()
                {
                    return false;
                }
            }
            StmtLikeContent::RaiseStmt(_) => {}
            _ => return false,
        }
        let Some(second) = iterator.next() else {
            return false;
        };
        if iterator.next().is_some() {
            return false;
        }
        match second.node {
            StmtLikeContent::YieldExpr(y) => match y.unpack() {
                YieldExprContent::StarExpressions(s) => {
                    // Conformance tests have things like `yield ""`.
                    s.is_none_literal() || !self.i_s.db.mypy_compatible()
                }
                YieldExprContent::YieldFrom(_) => false,
                YieldExprContent::None => true,
            },
            _ => false,
        }
    }

    pub(crate) fn ensure_func_diagnostics(&self, function: Function) -> Result<(), ()> {
        function.cache_func_from_diagnostics(self.i_s);
        let func_node = function.node();
        if let Some(decorated) = func_node.maybe_decorated()
            && function.node_ref.point().maybe_specific() != Some(Specific::OverloadUnreachable)
            && self.is_no_type_check(decorated)
        {
            return Ok(());
        }

        debug!(
            "Diagnostics for function {} ({}({}:{}):#{})",
            function.name(),
            self.file_path(),
            self.file.file_index,
            func_node.index(),
            function.node_ref.line_one_based(self.i_s.db)
        );
        let _indent = debug_indent();
        self.calc_func_diagnostics(function)
    }

    pub(crate) fn ensure_calculated_function_body(&self, function: Function) -> Result<(), ()> {
        let func_node = function.node();
        let (name_def, _, params, _, body) = func_node.unpack();
        let body_ref = NodeRef::new(self.file, body.index());
        let point = body_ref.point();
        if point.calculated() {
            return Ok(());
        }
        if body_ref.point().calculating() {
            return Err(());
        }
        body_ref.set_point(Point::new_calculating());
        FLOW_ANALYSIS.with(|fa| {
            let unreachable = fa.with_new_func_frame_and_return_unreachable(self.i_s.db, || {
                if self.is_empty_generator_function(func_node) {
                    fa.enable_reported_unreachable_in_top_frame();
                }
                let flags = self.flags();
                self.file
                    .inference(&self.i_s.with_func_context(&function))
                    .function_diagnostics_with_correct_i_s(function, flags, name_def, params, body);
            });
            let specific = if unreachable {
                Specific::FunctionEndIsUnreachable
            } else {
                Specific::Analyzed
            };
            body_ref.set_point(Point::new_specific(specific, Locality::Todo));
        });
        Ok(())
    }

    fn calc_func_diagnostics(&self, function: Function) -> Result<(), ()> {
        self.ensure_calculated_function_body(function)?;

        let i_s = self.i_s;

        let (name_def, type_params, params, return_annotation, body) = function.node().unpack();

        let mut is_overload_member = false;
        if let Some(ComplexPoint::FunctionOverload(o)) = function.node_ref.maybe_complex() {
            is_overload_member = true;
            if let Some(implementation) = &o.implementation {
                let maybe_remap = |class: Class, c: &mut Cow<CallableContent>| {
                    if c.has_self_type(i_s.db) || !class.use_cached_type_vars(i_s.db).is_empty() {
                        let mut cls = class;
                        cls.generics = Generics::NotDefinedYet {
                            class_ref: class.node_ref,
                        };
                        *c = Cow::Owned(merge_class_type_vars(
                            i_s.db,
                            c,
                            cls,
                            cls,
                            &TypeOrClass::Class(cls),
                        ));
                    }
                };

                let mut c_impl = Cow::Borrowed(&implementation.callable);
                if let Some(class) = function.class {
                    maybe_remap(class, &mut c_impl)
                }
                for (i, c1) in o.iter_functions().enumerate() {
                    let mut c1 = Cow::Borrowed(c1.as_ref());
                    if let Some(class) = function.class {
                        maybe_remap(class, &mut c1)
                    }
                    self.calc_overload_implementation_diagnostics(
                        &c1,
                        &c_impl,
                        implementation,
                        i + 1,
                    )
                }
            }

            for (i, c1) in o.iter_functions().enumerate() {
                for (k, c2) in o.iter_functions().skip(i + 1).enumerate() {
                    if is_overload_unmatchable(i_s, c1, c2) {
                        NodeRef::from_link(i_s.db, c2.defined_at).add_issue(
                            i_s,
                            IssueKind::OverloadUnmatchable {
                                matchable_signature_index: i + 1,
                                unmatchable_signature_index: i + k + 2,
                            },
                        );
                        /*
                        } else if !c1
                            .return_type
                            .is_simple_sub_type_of(i_s, &c2.return_type)
                            .bool()
                            && has_overlapping_params(
                                i_s,
                                &mut Matcher::default(),
                                &c1.params,
                                &c2.params,
                            )
                        {
                            // TODO skipping incompatible return types overload check
                            NodeRef::from_link(i_s.db, c1.defined_at).add_issue(
                                i_s,
                                IssueKind::OverloadIncompatibleReturnTypes {
                                    first_signature_index: i + 1,
                                    second_signature_index: i + k + 2,
                                },
                            );
                            */
                    }
                }
            }
        } else if function.node_ref.point().maybe_specific() == Some(Specific::OverloadUnreachable)
        {
            is_overload_member = !function.is_overload_implementation();
        }

        if let Some(type_params) = type_params {
            self.check_type_params_redefinitions(function.parent_scope(), type_params);
        }

        if !is_overload_member {
            // Check defaults here.
            for param in params.iter() {
                if let Some(annotation) = param.annotation()
                    && let Some(default) = param.default()
                {
                    let t = self.use_cached_param_annotation_type(annotation);
                    let inf = self
                        .infer_expression_with_context(default, &mut ResultContext::new_known(&t));
                    t.error_if_not_matches(
                        i_s,
                        &inf,
                        |issue| self.add_issue(default.index(), issue),
                        |error_types| {
                            let ErrorStrs { expected, got } = error_types.as_boxed_strs(i_s.db);
                            if default.is_ellipsis_literal()
                                && (self.file.is_stub() || function.has_trivial_body(i_s))
                            {
                                // In stubs it is allowed to do stuff like:
                                // def foo(x: int = ...) -> int: ...
                                return None;
                            }
                            Some(IssueKind::IncompatibleDefaultArgument {
                                argument_name: Box::from(param.name_def().as_code()),
                                got,
                                expected,
                            })
                        },
                    );
                }
            }
        }

        let is_protocol = function.class.is_some_and(|cls| cls.is_protocol(i_s.db));
        if is_protocol && function.is_final() && !is_overload_member {
            function.add_issue_onto_start_including_decorator(
                i_s,
                IssueKind::ProtocolMemberCannotBeFinal,
            );
        }

        if NodeRef::new(self.file, body.index()).point().specific()
            != Specific::FunctionEndIsUnreachable
            && !is_overload_member
            && !self.file.is_stub()
            && function.return_annotation().is_some()
            && !(self.flags().allow_empty_bodies && function.has_trivial_body(i_s))
            && !function.is_abstract()
            && !self.in_type_checking_only_block()
        {
            let ret_type = function.expected_return_type_for_return_stmt(i_s);
            let has_trivial_body = function.has_trivial_body(i_s);
            let maybe_async_note = || {
                (has_trivial_body
                    && function
                        .class
                        .and_then(|c| c.maybe_metaclass(i_s.db))
                        .is_some_and(|metaclass| metaclass == i_s.db.python_state.abc_meta_link()))
                .then_some("If the method is meant to be abstract, use @abc.abstractmethod")
            };
            if matches!(ret_type.as_ref(), Type::Never(_)) {
                self.add_issue(
                    name_def.index(),
                    IssueKind::ImplicitReturnInFunctionWithNeverReturn {
                        note: maybe_async_note(),
                    },
                );
            } else {
                let is_valid = ret_type.is_simple_super_type_of(i_s, &Type::None).bool();
                if self.flags().warn_no_return {
                    if (!is_valid
                        || !has_trivial_body
                            && !matches!(ret_type.as_ref(), Type::None | Type::Any(_)))
                        && !is_protocol
                    {
                        self.add_issue(
                            name_def.index(),
                            IssueKind::MissingReturnStatement {
                                code: if has_trivial_body {
                                    "empty-body"
                                } else {
                                    "return"
                                },
                                note: maybe_async_note(),
                            },
                        );
                    }
                } else if !is_valid {
                    if has_trivial_body {
                        if !is_protocol {
                            self.add_issue(
                                name_def.index(),
                                IssueKind::MissingReturnStatement {
                                    code: if has_trivial_body {
                                        "empty-body"
                                    } else {
                                        "return"
                                    },
                                    note: maybe_async_note(),
                                },
                            );
                        }
                    } else {
                        self.add_issue(
                            name_def.index(),
                            IssueKind::IncompatibleImplicitReturn {
                                expected: ret_type.format_short(i_s.db),
                                note: maybe_async_note(),
                            },
                        );
                    }
                }
            }
        }

        let mut params_iterator = params.iter().peekable();
        if let Some(class) = function.class
            && (function.kind(i_s) != FunctionKind::Staticmethod || function.is_dunder_new())
        {
            let mut was_star = false;
            let first_param = params_iterator
                .peek()
                .copied()
                .and_then(|p| match p.kind() {
                    ParamKind::PositionalOnly | ParamKind::PositionalOrKeyword => {
                        params_iterator.next();
                        Some(p)
                    }
                    ParamKind::KeywordOnly | ParamKind::StarStar => None,
                    ParamKind::Star => {
                        was_star = true;
                        None
                    }
                });
            if let Some(first_param) = first_param {
                if let Some(annotation) = first_param.annotation() {
                    let undefined_generics_class = Class::with_undefined_generics(class.node_ref);
                    let mut class_t = undefined_generics_class.as_type(i_s.db);
                    let original_self_t = self.use_cached_param_annotation_type(annotation);
                    let mut new = None;
                    let mut self_t = original_self_t.clone();
                    match self_t.as_ref() {
                        Type::TypeVar(tv) => {
                            if let TypeVarKind::Bound(b) = tv.type_var.kind(i_s.db) {
                                new = Some(b.clone());
                            }
                        }
                        Type::Type(t) => {
                            if let Type::TypeVar(tv) = t.as_ref()
                                && let TypeVarKind::Bound(b) = tv.type_var.kind(i_s.db)
                            {
                                new = Some(Type::Type(Arc::new(b.clone())));
                            }
                        }
                        _ => (),
                    };
                    if let Some(new) = new {
                        self_t = Cow::Owned(new)
                    }
                    let erased = self_t
                        .replace_type_var_likes_and_self(
                            i_s.db,
                            &mut |u| Some(u.as_any_generic_item()),
                            &|| Some(class_t.clone()),
                        )
                        .map(Cow::Owned)
                        .unwrap_or(self_t);
                    let erased_is_protocol = match erased.as_ref() {
                        Type::Class(c) => c.class(i_s.db).is_protocol(i_s.db),
                        Type::Type(t) => {
                            t.maybe_class(i_s.db).is_some_and(|c| c.is_protocol(i_s.db))
                        }
                        _ => false,
                    };
                    if !erased_is_protocol {
                        if function.first_param_kind(i_s) == FirstParamKind::ClassOfSelf {
                            class_t = Type::Type(Arc::new(class_t));
                        };
                        if !erased.is_simple_super_type_of(i_s, &class_t).bool() {
                            let param_name = first_param.name_def().as_code();
                            let issue = if ["self", "cls"].contains(&param_name) {
                                let format_data = &FormatData::new_reveal_type(i_s.db);
                                IssueKind::TypeOfSelfIsNotASupertypeOfItsClass {
                                    self_type: erased.format(format_data),
                                    class: class_t.format(format_data),
                                }
                            } else {
                                IssueKind::SelfArgumentMissing
                            };
                            self.add_issue(annotation.index(), issue);
                        } else {
                            let definition = class.node_ref.as_link();
                            if let Type::Class(c) = original_self_t.as_ref()
                                && c.link == definition
                                && let ClassGenerics::List(gs) = &c.generics
                            {
                                for (i, (generic, type_var_like)) in gs
                                    .iter()
                                    .zip(class.use_cached_type_vars(i_s.db).iter())
                                    .enumerate()
                                {
                                    let mut has_unrelated_type_var = false;
                                    generic.replace_type_var_likes(i_s.db, &mut |usage| {
                                        if usage.in_definition() == definition
                                            && usage.index().as_usize() != i
                                        {
                                            has_unrelated_type_var = true;
                                        }
                                        None
                                    });
                                    if has_unrelated_type_var {
                                        self.add_issue(
                                            annotation.index(),
                                            IssueKind::TypeOfSelfHasTypeVars {
                                                type_var_like: type_var_like.clone(),
                                                class_name: class.name().into(),
                                            },
                                        );
                                    }
                                }
                            }
                        }
                    }
                }
            } else if !was_star {
                function
                    .node_ref
                    .add_issue(i_s, IssueKind::MethodWithoutArguments);
            }
        }

        let flags = self.flags();
        check_for_missing_annotations(i_s, flags, function, name_def, return_annotation);

        for param in params_iterator {
            if let Some(annotation) = param.annotation() {
                let t = self.use_cached_param_annotation_type(annotation);
                if matches!(t.as_ref(), Type::TypeVar(tv) if tv.type_var.variance == TypeVarVariance::Known(Variance::Covariant))
                    && !["__init__", "__new__", "__post_init__"].contains(&name_def.as_code())
                {
                    NodeRef::new(self.file, annotation.index())
                        .add_issue(i_s, IssueKind::TypeVarCovariantInParamType);
                }

                if param.kind() == ParamKind::StarStar
                    && let Type::TypedDict(td) = t.as_ref()
                {
                    let mut overlapping_names = vec![];
                    for member in &td.members(i_s.db).named {
                        for p in params.iter() {
                            let name = member.name.as_str(i_s.db);
                            if matches!(
                                p.kind(),
                                ParamKind::PositionalOrKeyword | ParamKind::KeywordOnly
                            ) && name == p.name_def().as_code()
                            {
                                overlapping_names.push(format!("\"{name}\""));
                                break;
                            }
                        }
                    }
                    if !overlapping_names.is_empty() {
                        function.add_issue_for_declaration(
                            i_s,
                            IssueKind::TypedDictArgumentNameOverlapWithUnpack {
                                names: overlapping_names.join(", ").into(),
                            },
                        );
                    }
                }
            }
        }

        if let Some(return_annotation) = return_annotation {
            let t = self.use_cached_return_annotation_type(return_annotation);
            if matches!(t.as_ref(), Type::TypeVar(tv) if tv.type_var.variance == TypeVarVariance::Known(Variance::Contravariant))
            {
                NodeRef::new(self.file, return_annotation.index())
                    .add_issue(i_s, IssueKind::TypeVarContravariantInReturnType);
            }
            if function.is_generator() {
                let expected = if function.is_async() {
                    &i_s.db.python_state.async_generator_with_any_generics
                } else {
                    &i_s.db.python_state.generator_with_any_generics
                };
                if !t.is_simple_super_type_of(i_s, expected).bool() {
                    if function.is_async() {
                        NodeRef::new(self.file, return_annotation.index())
                            .add_issue(i_s, IssueKind::InvalidAsyncGeneratorReturnType);
                    } else {
                        NodeRef::new(self.file, return_annotation.index())
                            .add_issue(i_s, IssueKind::InvalidGeneratorReturnType);
                    }
                }
            }
        }
        if flags.disallow_any_unimported {
            /*
            for param in params
                .iter()
                .skip((function.class.is_some() && func_kind != FunctionKind::Staticmethod).into())
            {
                if let Some(annotation) = param.annotation() {
                    let _t = self.use_cached_param_annotation_type(annotation);
                    // TODO implement --disallow-any-unimported
                }
            }
            */
        }
        Ok(())
    }

    // This is mostly a helper function to avoid using the wrong InferenceState accidentally.
    #[inline]
    fn function_diagnostics_with_correct_i_s(
        &self,
        function: Function,
        flags: &TypeCheckerFlags,
        name: NameDef,
        params: FunctionDefParameters,
        block: Block,
    ) {
        for param in params.iter() {
            self.add_initial_name_definition(param.name_def());
        }
        let i_s = self.i_s;
        let is_typed = function.is_typed();
        if is_typed || flags.check_untyped_defs {
            // TODO for now we skip checking functions with TypeVar constraints
            if function.type_vars(i_s.db).has_constraints(i_s.db)
                || function
                    .class
                    .is_some_and(|c| c.type_vars(i_s).has_constraints(i_s.db))
            {
                // For now simply assign any everywhere
                self.calc_untyped_block_diagnostics(block, true);
                self.mark_current_frame_unreachable()
            } else {
                self.calc_block_diagnostics(block, None, Some(&function))
            }
            if !is_typed {
                return;
            }
        } else {
            self.calc_untyped_block_diagnostics(block, false);
            return;
        }

        if let Some(return_annotation) = function.return_annotation()
            && i_s.db.mypy_compatible()
            && function.is_dunder_new()
        {
            let mut class = function.class.unwrap();
            // Here we do not want self generics, we actually want Any generics.
            class.generics = Generics::NotDefinedYet {
                class_ref: class.node_ref,
            };
            if let Some(callable) = infer_class_method(
                i_s,
                class,
                class,
                &function.as_callable(i_s, FirstParamProperties::None),
                None,
            ) {
                match &callable.return_type {
                    Type::Class(_) => {
                        let t = &callable.return_type;
                        if !class.as_type(i_s.db).is_simple_super_type_of(i_s, t).bool() {
                            self.add_issue(
                                return_annotation.index(),
                                IssueKind::NewIncompatibleReturnType {
                                    returns: t.format_short(i_s.db),
                                    must_return: class.format_short(i_s.db),
                                },
                            );
                        }
                    }
                    Type::Type(_) | Type::Any(_) | Type::Never(_) => (),
                    Type::Enum(e) if e.class == class.node_ref.as_link() => (),
                    t => {
                        self.add_issue(
                            return_annotation.index(),
                            IssueKind::NewMustReturnAnInstance {
                                got: t.format_short(i_s.db),
                            },
                        );
                    }
                }
            }
        }

        if let Some(magic_name) = name
            .as_code()
            .strip_prefix("__")
            .and_then(|n| n.strip_suffix("__"))
            && function.class.is_some()
        {
            match magic_name {
                "init" | "init_subclass" => {
                    if let Some(return_annotation) = function.return_annotation()
                        && !matches!(
                            function.return_type(i_s).as_ref(),
                            Type::None | Type::Never(_)
                        )
                    {
                        // __init__ and __init_subclass__ must return None
                        NodeRef::new(self.file, return_annotation.expression().index()).add_issue(
                            i_s,
                            IssueKind::MustReturnNone {
                                function_name: function.name().into(),
                            },
                        );
                    }
                }
                "exit" => {
                    // Check the return type of __exit__
                    self.check_magic_exit(function)
                }
                "getattr" => {
                    let func_type = function.as_type(i_s, FirstParamProperties::None);
                    if !self
                        .i_s
                        .db
                        .python_state
                        .valid_getattr_supertype
                        .clone()
                        .is_simple_super_type_of(i_s, &func_type)
                        .bool()
                    {
                        function.add_issue_for_declaration(
                            self.i_s,
                            IssueKind::InvalidSpecialMethodSignature {
                                type_: func_type.format_short(self.i_s.db),
                                special_method: "__getattr__",
                            },
                        );
                    }
                }
                _ => {
                    // Check reverse magic methods like __rmul__
                    self.check_overlapping_op_methods(function, magic_name);
                    self.check_inplace_methods(function, magic_name);
                }
            }
        }
    }

    fn calc_overload_implementation_diagnostics(
        &self,
        overload_item: &CallableContent,
        implementation_callable: &CallableContent,
        implementation: &OverloadImplementation,
        signature_index: usize,
    ) {
        create_matcher_with_independent_type_vars(
            self.i_s.db,
            None,
            implementation_callable,
            overload_item,
            |mut matcher, implementation_callable, overload_item| {
                let match_ = matches_params(
                    self.i_s,
                    &mut matcher,
                    &overload_item.params,
                    &implementation_callable.params,
                );
                if !match_.bool() {
                    implementation
                        .function(self.i_s.db, None)
                        .add_issue_onto_start_including_decorator(
                            self.i_s,
                            IssueKind::OverloadImplementationParamsNotBroadEnough {
                                signature_index,
                            },
                        );
                }
                let implementation_result = &implementation_callable.return_type;
                let item_result = &overload_item.return_type;
                // This is bivariant matching. This is how Mypy allows subtyping.
                if !item_result
                    .is_sub_type_of(self.i_s, &mut matcher, implementation_result)
                    .bool()
                    && !item_result
                        .is_super_type_of(self.i_s, &mut matcher, implementation_result)
                        .bool()
                {
                    implementation
                        .function(self.i_s.db, None)
                        .add_issue_onto_start_including_decorator(
                            self.i_s,
                            IssueKind::OverloadImplementationReturnTypeIncomplete {
                                signature_index,
                            },
                        );
                }
            },
        )
    }

    fn calc_return_stmt_diagnostics(&self, func: Option<&Function>, return_stmt: ReturnStmt) {
        if let Some(func) = func {
            if func.return_annotation().is_some() {
                let i_s = self.i_s;
                let t = func.expected_return_type_for_return_stmt(i_s);
                if func.is_async() && func.is_generator() {
                    if let Some(star_exprs) = return_stmt.star_expressions() {
                        self.add_issue(star_exprs.index(), IssueKind::ReturnInAsyncGenerator);
                    }
                    return;
                }
                if matches!(t.as_ref(), Type::Never(_)) {
                    self.add_issue(
                        return_stmt.index(),
                        IssueKind::ReturnStmtInFunctionWithNeverReturn,
                    );
                    return;
                }
                if let Some(star_exprs) = return_stmt.star_expressions() {
                    let inf =
                        self.infer_star_expressions(star_exprs, &mut ResultContext::new_known(&t));
                    if self.flags().warn_return_any
                        && inf.as_cow_type(i_s).is_any()
                        && t.as_ref() != &i_s.db.python_state.object_type()
                        && !t.is_any_or_any_in_union(i_s.db)
                    {
                        self.add_issue(
                            star_exprs.index(),
                            IssueKind::ReturnedAnyWarning {
                                expected: t.format_short(i_s.db),
                            },
                        );
                    }

                    t.error_if_not_matches(
                        i_s,
                        &inf,
                        |issue| self.add_issue(star_exprs.index(), issue),
                        |error_types| {
                            Some({
                                if matches!(t.as_ref(), Type::None) {
                                    IssueKind::NoReturnValueExpected
                                } else {
                                    let ErrorStrs { expected, got } =
                                        error_types.as_boxed_strs(i_s.db);
                                    IssueKind::IncompatibleReturn { got, expected }
                                }
                            })
                        },
                    );
                } else if !t.is_simple_super_type_of(i_s, &Type::None).bool() {
                    self.add_issue(return_stmt.index(), IssueKind::ReturnValueExpected);
                }
            } else if let Some(star_exprs) = return_stmt.star_expressions() {
                self.infer_star_expressions(star_exprs, &mut ResultContext::Unknown);
            }
        }
    }

    fn ensure_cached_decorators(&self, decorated: Decorated) {
        // For now we don't cache decorators for stubs, because narrowing information should not be
        // relevant.
        if self.file.is_stub() {
            return;
        }
        for decorator in decorated.decorators().iter_reverse() {
            // TODO we should scan for actual properties and not just skip properties ending with
            // setter/deleter.
            if let ExpressionContent::ExpressionPart(ExpressionPart::Primary(prim)) =
                decorator.named_expression().expression().unpack()
                && let PrimaryContent::Attribute(attr) = prim.second()
                && matches!(attr.as_code(), "setter" | "deleter")
            {
                continue;
            }
            self.infer_decorator(decorator);
        }
    }

    pub fn cache_for_stmt_names(
        &self,
        star_targets: StarTargets,
        star_exprs: StarExpressions,
        is_async: bool,
    ) {
        let star_targets_point = self.point(star_targets.index());
        if star_targets_point.calculated() {
            debug_assert_eq!(star_targets_point.specific(), Specific::Analyzed);
            return;
        }
        let inf = self
            .infer_star_expressions(star_exprs, &mut ResultContext::ValueExpected)
            .avoid_implicit_literal(self.i_s);
        let from = NodeRef::new(self.file, star_exprs.index());
        let element = if is_async {
            await_aiter_and_next(self.i_s, inf, from)
        } else {
            inf.iter(self.i_s, from, IterCause::Iter)
                .infer_all(self.i_s)
        };
        debug!("For loop input: {}", element.format_short(self.i_s));
        self.assign_targets(star_targets.as_target(), element, from, AssignKind::Normal);
        self.set_point(
            star_targets.index(),
            Point::new_specific(Specific::Analyzed, Locality::Todo),
        );
    }

    pub fn cache_with_item(&self, with_item: WithItem, is_async: bool) -> Inferred {
        // Returns the result of __exit__.
        if let Some(inferred) = self.check_point_cache(with_item.index()) {
            return inferred;
        }
        let (expr, target) = with_item.unpack();
        let from = NodeRef::new(self.file, expr.index());
        if let Some(target) = &target {
            self.set_calculating_on_target(target.clone());
        }
        let result = self.infer_expression(expr);
        let mut enter_result = result.type_lookup_and_execute_with_attribute_error(
            self.i_s,
            from,
            match is_async {
                false => "__enter__",
                true => "__aenter__",
            },
            &NoArgs::new(from),
            &mut match is_async {
                false => ResultContext::ExpectUnused,
                true => ResultContext::Await,
            },
        );
        if is_async {
            enter_result = await_(
                self.i_s,
                enter_result,
                from,
                r#""async with" for "__aenter__""#,
                false,
            );
        }
        let mut exit_result = result.type_lookup_and_execute_with_attribute_error(
            self.i_s,
            from,
            match is_async {
                false => "__exit__",
                true => "__aexit__",
            },
            &CombinedArgs::new(
                &KnownArgs::new(&Inferred::new_any(AnyCause::Todo), from),
                &CombinedArgs::new(
                    // TODO don't use any here.
                    &KnownArgs::new(&Inferred::new_any(AnyCause::Todo), from),
                    &KnownArgs::new(&Inferred::new_any(AnyCause::Todo), from),
                ),
            ),
            &mut match is_async {
                false => ResultContext::ExpectUnused,
                true => ResultContext::Await,
            },
        );
        if is_async {
            exit_result = await_(
                self.i_s,
                exit_result,
                from,
                r#""async with" for "__aexit__""#,
                false,
            );
        }
        if let Some(target) = target {
            self.assign_targets(
                target,
                enter_result,
                NodeRef::new(self.file, with_item.index()),
                AssignKind::Normal,
            )
        }
        exit_result.save_redirect(self.i_s, self.file, with_item.index())
    }

    fn check_overlapping_op_methods(&self, func: Function, short_reverse_name: &str) {
        let i_s = self.i_s;
        let Some(normal_magic) = OVERLAPPING_REVERSE_TO_NORMAL_METHODS.get(short_reverse_name)
        else {
            return;
        };

        let invalid_signature = || {
            func.add_issue_for_declaration(
                i_s,
                IssueKind::InvalidSignature {
                    signature: func
                        .as_type(i_s, FirstParamProperties::None)
                        .format_short(i_s.db),
                },
            );
        };

        let from = func.node_ref; // TODO this NodeRef shouldn't be used.
        let mut param_iterator = func.iter_params();
        let first_param = param_iterator.next();
        let Some(param) = param_iterator.next().or_else(|| {
            first_param.filter(|first_param| first_param.kind(i_s.db) == ParamKind::Star)
        }) else {
            // If there is param, the signature is invalid and should be checked elsewhere.
            return invalid_signature();
        };
        if param_iterator.any(|param| !param.has_default_or_stars(i_s.db)) {
            return invalid_signature();
        }
        let forward_type = match param.specific(i_s.db) {
            WrappedParamType::PositionalOnly(t)
            | WrappedParamType::PositionalOrKeyword(t)
            | WrappedParamType::Star(WrappedStar::ArbitraryLen(t)) => t,
            _ => return invalid_signature(),
        };
        let Some(forward_type) = forward_type else {
            return; // If the type is Any, we do not need to check.
        };
        forward_type.run_after_lookup_on_each_union_member(
            i_s,
            None,
            from.file,
            normal_magic,
            LookupKind::OnlyType,
            &mut ResultContext::ValueExpected,
            // Theoretically this should not be ignored, but for now I'm not sure if self types are
            // working anyway.
            &|_| false,
            &mut |forward, lookup_details| {
                let check = |callable: &CallableContent| {
                    // Can only overlap if the classes differ. On the same class __radd__ will
                    // never be called if there's a __add__ as well, because in that case __add__
                    // will be preferred.
                    let reverse = func.class.unwrap().as_type(i_s.db);
                    if forward.is_simple_same_type(i_s, &reverse).bool() {
                        return;
                    }

                    // The params must cycle for it to be an unsafe overlap.
                    let Some(reverse_param_type) = callable.first_positional_type() else {
                        // If there is no positional type, the signature is invalid and should be
                        // checked elsewhere.
                        return;
                    };
                    if !reverse
                        .is_simple_sub_type_of(i_s, &reverse_param_type)
                        .bool()
                        && !reverse
                            .is_simple_super_type_of(i_s, &reverse_param_type)
                            .bool()
                    {
                        return;
                    }

                    // I'm not 100% sure why this variance calculation is necessary, but I believe
                    // it's because Python calls the reverse methods before the normal methods when
                    // the right type is a subtype of the left.
                    let variance = match reverse.is_simple_sub_type_of(i_s, forward).bool() {
                        true => Variance::Covariant,
                        false => Variance::Contravariant,
                    };
                    if !callable
                        .return_type
                        .matches(
                            i_s,
                            &mut Matcher::default(),
                            &func.return_type(i_s),
                            variance,
                        )
                        .bool()
                    {
                        from.add_issue(
                            i_s,
                            IssueKind::OperatorSignaturesAreUnsafelyOverlapping {
                                reverse_name: short_reverse_name.into(),
                                reverse_class: func.class.unwrap().format_short(i_s.db),
                                forward_class: forward.format_short(i_s.db),
                            },
                        );
                    }
                };
                match lookup_details.lookup.into_inferred().as_type(i_s) {
                    Type::Callable(c) => check(&c),
                    Type::FunctionOverload(overload) => {
                        for c in overload.iter_functions() {
                            check(c)
                        }
                    }
                    Type::Any(_) | Type::CustomBehavior(_) => (),
                    _ => {
                        from.add_issue(
                            i_s,
                            IssueKind::ForwardOperatorIsNotCallable {
                                forward_name: normal_magic,
                            },
                        );
                    }
                }
            },
        )
    }

    fn check_inplace_methods(&self, func: Function, inplace_magic_name: &str) {
        let i_s = self.i_s;
        let Some(normal_magic_name) = INPLACE_TO_NORMAL_METHODS.get(inplace_magic_name) else {
            return;
        };
        let instance = func.class.unwrap().instance();
        let options = InstanceLookupOptions::new(&|_| false).with_avoid_inferring_return_types();
        let normal_method = instance.lookup(i_s, normal_magic_name, options).lookup;
        if let Some(normal_inf) = normal_method.into_maybe_inferred() {
            let inplace_method = instance.lookup(i_s, func.name(), options).lookup;
            if !normal_inf
                .as_cow_type(i_s)
                .is_simple_super_type_of(i_s, &inplace_method.into_inferred().as_cow_type(i_s))
                .bool()
            {
                func.add_issue_for_declaration(
                    self.i_s,
                    IssueKind::SignaturesAreIncompatible {
                        name1: func.name().into(),
                        name2: normal_magic_name,
                    },
                );
            }
        }
    }

    fn check_magic_exit(&self, function: Function) {
        // Check if __exit__ has the return type bool and raise an error if all returns return
        // False.
        if !function
            .return_type(self.i_s)
            .iter_with_unpacked_unions(self.i_s.db)
            .any(|t| t == &self.i_s.db.python_state.bool_type())
        {
            return;
        }
        let mut had_return = false;
        for return_or_yield in function.iter_return_or_yield() {
            let ReturnOrYield::Return(return_) = return_or_yield else {
                continue;
            };
            had_return = true;
            if let Some(star_expressions) = return_.star_expressions() {
                let inf = self
                    .infer_star_expressions(star_expressions, &mut ResultContext::ValueExpected);
                if !matches!(
                    inf.as_cow_type(self.i_s).as_ref(),
                    Type::Literal(Literal {
                        kind: LiteralKind::Bool(false),
                        ..
                    })
                ) {
                    return;
                }
            }
        }
        if had_return {
            function.add_issue_for_declaration(self.i_s, IssueKind::IncorrectExitReturn);
        }
    }
}

fn valid_raise_type(i_s: &InferenceState, from: NodeRef, t: &Type, allow_none: bool) -> bool {
    let db = i_s.db;
    let check = |cls: Class| cls.incomplete_mro(db) || cls.is_base_exception(db);
    match t {
        Type::Class(c) => check(c.class(db)),
        Type::Dataclass(dc) => check(dc.class(db)),
        Type::Type(inner_t) => {
            let check_type_of_class = |cls: Class| {
                t.execute(
                    i_s,
                    None,
                    &NoArgs::new(from),
                    &mut ResultContext::ValueExpected,
                    OnTypeError::new(&|_, _, _, _| {
                        recoverable_error!(
                            "Type errors should not be possible, because there are no params"
                        )
                    }),
                );
                check(cls)
            };
            match inner_t.as_ref() {
                Type::Class(c) => check_type_of_class(c.class(db)),
                Type::Dataclass(dc) => check_type_of_class(dc.class(db)),
                _ => true,
            }
        }
        Type::TypeVar(tv) => match tv.type_var.kind(i_s.db) {
            TypeVarKind::Bound(b) => valid_raise_type(i_s, from, b, false),
            _ => false,
        },
        Type::Any(_) | Type::Never(_) => true,
        Type::Union(union) => union
            .iter()
            .all(|t| valid_raise_type(i_s, from, t, allow_none)),
        Type::None if allow_none => true,
        _ => false,
    }
}

pub fn await_aiter_and_next(i_s: &InferenceState, base: Inferred, from: NodeRef) -> Inferred {
    await_(
        i_s,
        base.type_lookup_and_execute(
            i_s,
            from.file,
            "__aiter__",
            &NoArgs::new(from),
            &mut ResultContext::Await,
            &|t| {
                from.add_issue(
                    i_s,
                    IssueKind::AsyncNotIterable {
                        type_: t.format_short(i_s.db),
                    },
                );
            },
        )
        .type_lookup_and_execute_with_attribute_error(
            i_s,
            from,
            "__anext__",
            &NoArgs::new(from),
            &mut ResultContext::Await,
        ),
        from,
        r#""async for""#,
        false,
    )
}

fn try_pretty_format(
    notes: &mut Vec<Box<str>>,
    i_s: &InferenceState,
    t: &Type,
    class_lookup_result: LookupResult,
) {
    let prefix = "         ";
    if let Some(inf) = class_lookup_result.into_maybe_inferred() {
        let add_kind_info = |notes: &mut Vec<Box<str>>, kind: &_| match kind {
            FunctionKind::Classmethod { .. } => notes.push(format!("{prefix}@classmethod").into()),
            FunctionKind::Staticmethod => notes.push(format!("{prefix}@staticmethod").into()),
            _ => (),
        };
        match inf.as_cow_type(i_s).as_ref() {
            Type::Callable(c) if !matches!(c.kind, FunctionKind::Property { .. }) => {
                add_kind_info(notes, &c.kind);
                notes.push(
                    format!(
                        "{prefix}{}",
                        c.format_pretty(&FormatData::new_short(i_s.db))
                    )
                    .into(),
                );
                return;
            }
            Type::FunctionOverload(overloads) => {
                for c in overloads.iter_functions() {
                    notes.push(format!("{prefix}@overload").into());
                    add_kind_info(notes, &c.kind);
                    notes.push(
                        format!(
                            "{prefix}{}",
                            c.format_pretty(&FormatData::new_short(i_s.db))
                        )
                        .into(),
                    );
                }
                return;
            }
            _ => (),
        }
    }
    notes.push(format!("{prefix}{}", t.format_short(i_s.db)).into())
}

fn is_overload_unmatchable(
    i_s: &InferenceState,
    c1: &CallableContent,
    c2: &CallableContent,
) -> bool {
    create_matcher_with_independent_type_vars(i_s.db, None, c1, c2, |matcher, c1, c2| {
        let matcher = &mut matcher.with_precise_matching();
        let result = matches_params(i_s, matcher, &c2.params, &c1.params);
        matches!(result, Match::True { with_any: false })
    })
}

fn create_matcher_with_independent_type_vars<T>(
    db: &Database,
    replace_self: Option<ReplaceSelfInMatcher>,
    c1: &CallableContent,
    c2: &CallableContent,
    callback: impl FnOnce(Matcher, &CallableContent, &CallableContent) -> T,
) -> T {
    let c = Callable::new(c1, None);
    let matcher = Matcher::new_reverse_callable_matcher(&c, replace_self);
    if c1.defined_at == c2.defined_at {
        let c2 = c2.change_temporary_matcher_index(db, 1);
        callback(matcher, c1, &c2)
    } else {
        callback(matcher, c1, c2)
    }
}

fn add_error_if_final(
    i_s: &InferenceState,
    from: NodeRef,
    name: &str,
    original_lookup: &LookupDetails,
) {
    if original_lookup.attr_kind.is_final() {
        from.add_issue_onto_start_including_decorator(
            i_s,
            IssueKind::CannotOverrideFinalAttribute {
                name: name.into(),
                base_class: original_lookup.class.name(i_s.db).into(),
            },
        );
    }
}

fn find_and_check_override(
    i_s: &InferenceState,
    from: NodeRef,
    override_class: Class,
    name: &str,
    has_override_decorator: bool,
) {
    let instance = Instance::new(override_class, None);
    let add_lookup_issue = |_issue| {
        // TODO we need to work on this, see testSelfTypeOverrideCompatibility
        false
    };
    let mut original_details = instance.lookup(
        i_s,
        name,
        // NamedTuple / Tuple are special, because they insert an additional type of themselves.
        InstanceLookupOptions::new(&add_lookup_issue)
            .with_skip_first_of_mro(i_s.db, &override_class)
            .with_avoid_inferring_return_types(),
    );
    add_error_if_final(i_s, from, name, &original_details);

    if original_details.lookup.is_some() {
        let override_details = instance.lookup(
            i_s,
            name,
            InstanceLookupOptions::new(&add_lookup_issue).with_avoid_inferring_return_types(),
        );
        if !has_override_decorator
            && from
                .file
                .flags(i_s.db)
                .enabled_error_codes
                .iter()
                .any(|c| c == "explicit-override")
        {
            from.add_issue(
                i_s,
                IssueKind::ExplicitOverrideFlagRequiresOverride {
                    method: name.into(),
                    class: original_details.class.qualified_name(i_s.db).into(),
                },
            );
        }
        while let Some(mro_index) = original_details.mro_index {
            check_override(
                i_s,
                from,
                original_details,
                &override_details,
                name,
                |c| {
                    if let TypeOrClass::Class(c) = c
                        && c.file_index() != from.file_index()
                    {
                        return c.qualified_name(i_s.db).into();
                    }
                    c.name(i_s.db).into()
                },
                None,
            );
            original_details = instance.lookup(
                i_s,
                name,
                // NamedTuple / Tuple are special, because they insert an additional type of themselves.
                InstanceLookupOptions::new(&add_lookup_issue)
                    .with_super_count(mro_index.0 as usize + 1),
            )
        }
    } else if has_override_decorator {
        let issue = IssueKind::MissingBaseForOverride { name: name.into() };
        // For whatever reason, this is how Mypy does it and we don't want to screw up the line
        // numbers
        let lookup = override_class.simple_lookup(i_s, |_| false, name);
        if matches!(
            lookup.into_inferred().as_type(i_s),
            Type::FunctionOverload(_)
        ) {
            from.add_issue_onto_start_including_decorator(i_s, issue);
        } else {
            from.add_issue(i_s, issue);
        }
    }
}

pub(super) fn check_override(
    i_s: &InferenceState,
    from: NodeRef,
    original_lookup_details: LookupDetails,
    override_lookup_details: &LookupDetails,
    name: &str,
    original_class_name: impl Fn(&TypeOrClass) -> Box<str>,
    original_formatter: Option<&dyn Fn() -> String>,
) -> bool {
    let original_inf = original_lookup_details.lookup.into_inferred();
    let original_t = original_inf.as_cow_type(i_s);
    let original_class = original_lookup_details.class;
    let override_inf = override_lookup_details
        .lookup
        .maybe_inferred()
        .unwrap_or_else(|| Cow::Owned(Inferred::new_any(AnyCause::Internal)));
    let override_t = override_inf.as_cow_type(i_s);
    let override_t = override_t.as_ref();
    let TypeOrClass::Class(override_class) = override_lookup_details.class else {
        unreachable!();
    };

    let maybe_func = || match override_t {
        Type::Callable(c) if c.defined_at.file == from.file_index() => {
            let node_ref = NodeRef::from_link(i_s.db, c.defined_at);
            node_ref
                .maybe_function()
                .map(|_| Function::new(node_ref, None))
                .filter(|func| func.node().name_def().name_index() == from.node_index)
        }
        _ => None,
    };

    let self_replacer = || match &original_class {
        TypeOrClass::Type(t) => t.as_ref().clone(),
        TypeOrClass::Class(c) => c.as_type(i_s.db),
    };
    let mut matcher =
        Matcher::new_self_replacer(&self_replacer).with_ignore_positional_param_names();
    let mut match_ = original_t.is_super_type_of(i_s, &mut matcher, override_t);

    // Check property.setter if it's not the same type.
    let base_setter_t = original_lookup_details.attr_kind.property_setter_type();
    let override_setter_t = override_lookup_details.attr_kind.property_setter_type();
    if base_setter_t.is_some() || override_setter_t.is_some() {
        let b_t = base_setter_t.unwrap_or(&original_t);
        let o_t = override_setter_t.unwrap_or(override_t);
        if match_.bool() || o_t != override_t {
            check_property_setter_override(i_s, from, &mut matcher, &original_class, b_t, o_t)
        }
    }

    let mut op_method_wider_note = false;
    if let Type::FunctionOverload(override_overload) = override_t
        && match_.bool()
        && FORWARD_OP_METHODS.contains(name)
        && operator_domain_is_widened(i_s, override_overload, &original_t)
    {
        // Reverse operators lead to weird behavior when overloads widen. If you want to
        // understand why this is an issue, please look at testUnsafeDunderOverlapInSubclass.
        op_method_wider_note = true;
        match_ = Match::new_false();
    }
    use AttributeKind::*;
    match (
        &original_lookup_details.attr_kind,
        &override_lookup_details.attr_kind,
    ) {
        (
            original,
            AttributeKind::Property {
                setter_type: None, ..
            },
        ) if original.is_writable() => {
            if let AttributeKind::Property { .. } = original {
                // This happens when @cached_property is overwritten with @property. This is
                // allowed in Mypy (probably due to a logic error).
                if !i_s.db.mypy_compatible() || !original.is_cached_property() {
                    from.add_issue_onto_start_including_decorator(
                        i_s,
                        IssueKind::ReadOnlyPropertyCannotOverwriteReadWriteProperty,
                    );
                }
            // TODO we should not need to check if we are in a frozen dataclass, the attr kind
            // should never be writable in the first place!
            } else if !original_class.is_frozen_dataclass() {
                from.add_issue(
                    i_s,
                    IssueKind::ReadOnlyPropertyCannotOverwriteWritableAttribute,
                );
            }
        }
        (Classmethod { .. } | Staticmethod { .. }, DefMethod { .. }) => {
            // Some method types may be overridden, because they still work the same way on class
            // and instance, others not.
            match_ = Match::new_false();
        }
        (ClassVar, AnnotatedAttribute) => {
            from.add_issue(
                i_s,
                IssueKind::CannotOverrideClassVariableWithInstanceVariable {
                    base_class: original_class_name(&original_class),
                },
            );
        }
        (AnnotatedAttribute, ClassVar) => {
            from.add_issue(
                i_s,
                IssueKind::CannotOverrideInstanceVariableWithClassVariable {
                    base_class: original_class_name(&original_class),
                },
            );
        }
        _ => (),
    }
    let mut added_liskov_note = false;
    let matched = match_.bool();
    if matched {
        if original_lookup_details.attr_kind.is_writable()
            && override_lookup_details.attr_kind.is_final()
            && (!i_s.db.mypy_compatible()
                || !original_lookup_details.attr_kind.is_cached_property())
        {
            let issue = IssueKind::CannotOverrideWritableWithFinalAttribute { name: name.into() };
            if let Some(func) = maybe_func() {
                func.add_issue_onto_start_including_decorator(i_s, issue);
            } else {
                from.add_issue(i_s, issue);
            }
        }
    } else {
        let db = i_s.db;
        let mut emitted = false;
        // Mypy helps the user a bit by formatting different error messages for similar
        // signatures. Try to make this as similar as possible to Mypy.
        match override_func_infos(override_t, &original_t, &override_lookup_details.attr_kind) {
            Some(OverrideFuncInfos::CallablesSameParamLen(got_c, expected_c)) => {
                // First check params
                let CallableParams::Simple(params1) = &got_c.params else {
                    unreachable!()
                };
                let CallableParams::Simple(params2) = &expected_c.params else {
                    unreachable!()
                };
                for (i, (param1, mut param2)) in params1.iter().zip(params2.iter()).enumerate() {
                    if !param1.similar_kind_and_keyword_if_kw_param(db, param2) {
                        if matches!(&param1.type_, ParamType::KeywordOnly(_)) {
                            let search = params2.iter().find(|p2| {
                                param1.name.as_ref().zip(p2.name.as_ref()).is_some_and(
                                    |(n1, n2)| {
                                        n1.as_str(db) == n2.as_str(db)
                                            && matches!(
                                                &p2.type_,
                                                ParamType::PositionalOrKeyword(_)
                                                    | ParamType::KeywordOnly(_)
                                            )
                                    },
                                )
                            });
                            if let Some(p) = search {
                                param2 = p
                            } else {
                                continue;
                            }
                        } else {
                            continue;
                        }
                    }
                    let Some(t1) = param1.type_.maybe_type() else {
                        continue;
                    };
                    let Some(t2) = param2.type_.maybe_type() else {
                        continue;
                    };
                    let t1 = got_c.erase_func_type_vars_for_type(db, t1);
                    if !t1.is_simple_super_type_of(i_s, t2).bool() {
                        let supertype = original_class_name(&original_class);
                        let issue = IssueKind::ArgumentIncompatibleWithSupertype {
                            message: format!(
                                r#"Argument {} of "{name}" is incompatible with supertype "{supertype}"; supertype defines the argument type as "{}""#,
                                i + 1,
                                t2.format_short(db),
                            ).into(),
                            eq_class: (name == "__eq__").then(|| override_class.name().into()),
                            add_liskov_note: name != "__post_init__" && !added_liskov_note,
                        };
                        added_liskov_note = true;
                        match &param1.name {
                            Some(DbString::StringSlice(s)) if maybe_func().is_some() => {
                                from.file
                                    .add_issue(i_s, Issue::from_start_stop(s.start, s.end, issue));
                            }
                            _ => {
                                from.add_issue(i_s, issue);
                            }
                        }
                        emitted = true;
                    }
                }

                // Then the return type
                let got_ret = got_c.erase_func_type_vars_for_type(db, &got_c.return_type);
                let expected_ret =
                    expected_c.erase_func_type_vars_for_type(db, &expected_c.return_type);
                if !got_c
                    .return_type
                    .is_simple_sub_type_of(i_s, &expected_c.return_type)
                    .bool()
                {
                    let supertype = original_class_name(&original_class);
                    let mut async_note = None;
                    if is_async_iterator_without_async(i_s, &expected_ret, &got_ret) {
                        async_note = Some(format!(r#"Consider declaring "{name}" in supertype "{supertype}" without "async""#).into())
                    }

                    let issue = IssueKind::ReturnTypeIncompatibleWithSupertype {
                        message: format!(
                            r#"Return type "{}" of "{name}" incompatible with return type "{}" in supertype "{supertype}""#,
                            got_ret.format_short(db),
                            expected_ret.format_short(db),
                        ),
                        async_note,
                    };
                    if let Some(func) = maybe_func() {
                        func.add_issue_for_declaration(i_s, issue);
                    } else {
                        from.add_issue(i_s, issue);
                    }
                    emitted = true
                }
            }
            Some(OverrideFuncInfos::Mixed) => (),
            Some(OverrideFuncInfos::BothOverloads(got, expected)) => {
                let mut previous_match_right_index = 0;
                'outer: for c1 in expected.iter_functions() {
                    for (right_index, c2) in got.iter_functions().enumerate() {
                        let m = Matcher::default().matches_callable(i_s, c1, c2);
                        if m.bool() {
                            if previous_match_right_index <= right_index {
                                previous_match_right_index = right_index;
                                continue 'outer;
                            } else {
                                emitted = true;
                                from.add_issue_onto_start_including_decorator(
                                    i_s,
                                    IssueKind::OverloadOrderMustMatchSupertype {
                                        name: name.into(),
                                        base_class: original_class_name(&original_class),
                                    },
                                );
                                break 'outer;
                            }
                        }
                    }
                    break;
                }
            }
            None => {
                emitted = true;
                from.add_issue(
                    i_s,
                    IssueKind::IncompatibleAssignmentInSubclass {
                        got: override_t.format_short(i_s.db),
                        expected: original_t.format_short(i_s.db),
                        base_class: original_class_name(&original_class),
                    },
                );
            }
        }
        if !emitted {
            let mut notes = vec![];
            notes.push("     Superclass:".into());
            if let Some(original_formatter) = original_formatter {
                notes.push(format!("         {}", original_formatter()).into());
            } else {
                try_pretty_format(
                    &mut notes,
                    &i_s.with_class_context(&match original_class {
                        TypeOrClass::Class(c) => c,
                        TypeOrClass::Type(_) => override_class,
                    }),
                    &original_t,
                    override_class
                        .lookup(
                            i_s,
                            name,
                            ClassLookupOptions::new(&|_| false).with_super_count(
                                original_lookup_details
                                    .mro_index
                                    .map(|m| m.0 as usize)
                                    .unwrap_or(0),
                            ),
                        )
                        .lookup,
                );
            }
            notes.push("     Subclass:".into());
            if override_lookup_details.attr_kind == AttributeKind::Attribute
                || override_lookup_details.attr_kind == AttributeKind::AnnotatedAttribute
                || override_lookup_details.attr_kind == AttributeKind::ClassVar
                || override_lookup_details.attr_kind == AttributeKind::Final
            {
                // TODO remove this hack again and use try_pretty_format
                notes.push(format!("         {}", override_t.format_short(i_s.db)).into())
            } else {
                try_pretty_format(
                    &mut notes,
                    &i_s.with_class_context(&override_class),
                    override_t,
                    override_class.simple_lookup(i_s, |_| false, name),
                );
            }

            if op_method_wider_note {
                notes.push(
                    "Overloaded operator methods can't have wider argument types in overrides"
                        .into(),
                )
            }

            let issue = IssueKind::SignatureIncompatibleWithSupertype {
                name: name.into(),
                base_class: original_class_name(&original_class),
                notes: notes.into(),
            };
            if let Some(func) = maybe_func() {
                func.add_issue_for_declaration(i_s, issue);

            // This condition is so weird, but we try to be close to Mypy
            } else if matches!(override_t, Type::FunctionOverload(_))
                || matches!(
                    override_lookup_details.attr_kind,
                    AttributeKind::Property {
                        setter_type: Some(_),
                        ..
                    }
                )
            {
                from.add_issue_onto_start_including_decorator(i_s, issue)
            } else {
                from.add_issue(i_s, issue);
            }
        }
    }
    matched
}

fn check_property_setter_override(
    i_s: &InferenceState,
    from: NodeRef,
    matcher: &mut Matcher,
    base_class: &TypeOrClass,
    base_t: &Type,
    override_t: &Type,
) {
    if !base_t.is_sub_type_of(i_s, matcher, override_t).bool() {
        let mut notes = vec![
            format!(
                r#" (base class "{}" defined the type as "{}","#,
                base_class.name(i_s.db),
                base_t.format_short(i_s.db)
            ),
            format!(
                r#" override has type "{}")"#,
                override_t.format_short(i_s.db),
            ),
        ];
        if base_t.is_super_type_of(i_s, matcher, override_t).bool() {
            notes.push(" Setter types should behave contravariantly".into());
        }
        from.add_issue_and_prefer_on_setter_decorator(
            i_s,
            IssueKind::IncompatiblePropertySetterOverride { notes },
        );
    }
}

fn is_async_iterator_without_async(
    i_s: &InferenceState,
    original: &Type,
    override_: &Type,
) -> bool {
    let db = i_s.db;
    match override_ {
        Type::Class(c) if c.link == db.python_state.async_iterator_link() => match original {
            Type::Class(c) if c.link == db.python_state.coroutine_link() => {
                let check = c.class(db).nth_type_argument(db, 2);
                override_.is_simple_same_type(i_s, &check).bool()
            }
            _ => false,
        },
        _ => false,
    }
}

enum OverrideFuncInfos<'t1, 't2> {
    CallablesSameParamLen(&'t1 CallableContent, &'t2 CallableContent),
    BothOverloads(&'t1 FunctionOverload, &'t2 FunctionOverload),
    Mixed,
}

fn override_func_infos<'t1, 't2>(
    override_t: &'t1 Type,
    base_t: &'t2 Type,
    override_kind: &AttributeKind,
) -> Option<OverrideFuncInfos<'t1, 't2>> {
    match (override_t, base_t) {
        (Type::Callable(c1), Type::Callable(c2)) => Some(match (&c1.params, &c2.params) {
            (CallableParams::Simple(p1), CallableParams::Simple(p2)) if p1.len() == p2.len() => {
                OverrideFuncInfos::CallablesSameParamLen(c1, c2)
            }
            _ => OverrideFuncInfos::Mixed,
        }),
        (Type::FunctionOverload(o1), Type::FunctionOverload(o2)) => {
            Some(OverrideFuncInfos::BothOverloads(o1, o2))
        }
        _ => {
            if matches!(override_kind, AttributeKind::Property { .. }) {
                return Some(OverrideFuncInfos::Mixed);
            }
            (override_t.is_func_or_overload() || base_t.is_func_or_overload())
                .then_some(OverrideFuncInfos::Mixed)
        }
    }
}

fn operator_domain_is_widened(
    i_s: &InferenceState,
    override_overload: &FunctionOverload,
    original: &Type,
) -> bool {
    override_overload.iter_functions().any(|overload_func| {
        let widens_callable = |original: &Arc<CallableContent>| {
            let Some(original_domain) = original.first_positional_type() else {
                return false;
            };
            if let Some(override_domain) = overload_func.first_positional_type() {
                !original_domain
                    .is_simple_super_type_of(i_s, &override_domain)
                    .bool()
            } else {
                false
            }
        };
        match original {
            Type::Callable(c) => widens_callable(c),
            Type::FunctionOverload(o) => o.iter_functions().all(widens_callable),
            _ => {
                recoverable_error!(
                    "Why would an overload ever be {:?}",
                    original.format_short(i_s.db)
                );
                false
            }
        }
    })
}

fn check_protocol_type_var_variances(i_s: &InferenceState, class: Class) {
    for (i, tv_like) in class.type_vars(i_s).iter().enumerate() {
        let TypeVarLike::TypeVar(tv) = tv_like else {
            continue;
        };
        let TypeVarVariance::Known(tv_variance) = tv.variance else {
            continue;
        };
        let replace_protocol = |is_upper: bool| {
            Type::new_class(
                class.node_ref.as_link(),
                ClassGenerics::List(GenericsList::new_generics(
                    class
                        .type_vars(i_s)
                        .iter()
                        .enumerate()
                        .map(|(j, tv_like)| {
                            if i == j {
                                GenericItem::TypeArg(if is_upper {
                                    i_s.db.python_state.object_type()
                                } else {
                                    Type::Never(NeverCause::Other)
                                })
                            } else {
                                tv_like.as_any_generic_item()
                            }
                        })
                        .collect(),
                )),
            )
        };
        let p_upper_bound = replace_protocol(true);
        let p_lower_bound = replace_protocol(false);

        let match_protocol = |t1: &Type, t2| {
            t1.maybe_class(i_s.db)
                .unwrap()
                .check_protocol_match(i_s, &mut Matcher::default(), t2)
                .bool()
        };
        let mut expected_variance = Variance::Invariant;
        if match_protocol(&p_upper_bound, &p_lower_bound) {
            expected_variance = Variance::Covariant
        } else if match_protocol(&p_lower_bound, &p_upper_bound) {
            expected_variance = Variance::Contravariant
        }
        if tv_variance != expected_variance {
            NodeRef::new(class.node_ref.file, class.node().name().index()).add_issue(
                i_s,
                IssueKind::ProtocolWrongVariance {
                    type_var_name: tv.name(i_s.db).into(),
                    actual_variance: tv_variance,
                    expected_variance,
                },
            );
        }
    }
}

pub fn check_multiple_inheritance<'x, BASES: Iterator<Item = &'x Type>>(
    i_s: &InferenceState,
    bases: impl Fn() -> BASES,
    should_check: impl Fn(&str) -> bool,
    mut add_issue: impl FnMut(IssueKind) -> bool,
) {
    let db = i_s.db;
    let should_infer_untyped_params = db.project.should_infer_untyped_params();
    for (i, base1) in bases().enumerate() {
        let cls1 = match base1.maybe_class(db) {
            Some(c) => c,
            None => {
                debug!("TODO check complex base types");
                continue;
            }
        };

        let instance1 = Instance::new(cls1, None);
        for base2 in bases().skip(i + 1) {
            let instance2 = match base2.maybe_class(db) {
                Some(c) => Instance::new(c, None),
                None => continue,
            };
            instance1.run_on_symbols(|name| {
                if let Some(inner) = name.strip_prefix("__") {
                    if inner.strip_suffix("__").is_some() {
                        if IGNORED_INHERITANCE_NAMES.contains(&name) {
                            return;
                        }
                    } else {
                        // This is a private name
                        return;
                    }
                }
                if !should_check(name) {
                    return;
                }
                let had_lookup_issue = Cell::new(false);
                let inst2_lookup = instance2.lookup(
                    i_s,
                    name,
                    // Everything can inherit from object and it should therefore be fine to ignore
                    // it.
                    InstanceLookupOptions::new(&|issue| {
                        debug!("Multi inheritance bind issue(inst2) on name {name}: {issue:?}");
                        had_lookup_issue.set(true);
                        false
                    })
                    .with_avoid_inferring_return_types()
                    .without_object(),
                );
                let mut add_multi_inheritance_issue = || {
                    add_issue(IssueKind::MultipleInheritanceIncompatibility {
                        name: name.into(),
                        class1: cls1.name().into(),
                        class2: instance2.class.name().into(),
                    });
                };
                if had_lookup_issue.get() {
                    add_multi_inheritance_issue();
                    return;
                }
                if let Some(inf) = inst2_lookup.lookup.into_maybe_inferred() {
                    let mut second = inf.as_cow_type(i_s);
                    let inst1_lookup = instance1.lookup(
                        i_s,
                        name,
                        InstanceLookupOptions::new(&|issue| {
                            debug!("Multi inheritance bind issue(inst1) on name {name}: {issue:?}");
                            had_lookup_issue.set(true);
                            false
                        })
                        .with_avoid_inferring_return_types(),
                    );
                    if had_lookup_issue.get() {
                        add_multi_inheritance_issue();
                        return;
                    }
                    if let Some(first) = inst1_lookup.lookup.into_maybe_inferred() {
                        if inst2_lookup.attr_kind.is_final() {
                            add_issue(IssueKind::CannotOverrideFinalAttribute {
                                name: name.into(),
                                base_class: instance2.class.name().into(),
                            });
                            return;
                        }
                        if inst2_lookup.attr_kind.is_writable()
                            && inst1_lookup.attr_kind.is_final()
                            && (!db.mypy_compatible()
                                || !inst2_lookup.attr_kind.is_cached_property())
                        {
                            add_issue(IssueKind::CannotOverrideWritableWithFinalAttribute {
                                name: name.into(),
                            });
                            return;
                        }
                        let mut first = first.as_cow_type(i_s);
                        if should_infer_untyped_params {
                            if let Some(new) = first.replace_unknown_type_params_with_any(db) {
                                first = Cow::Owned(new)
                            }
                            if let Some(new) = second.replace_unknown_type_params_with_any(db) {
                                second = Cow::Owned(new)
                            }
                        }
                        if first.is_any() || second.is_any() {
                            // Any can be overwritten with anything
                            return;
                        }
                        if !first
                            .is_sub_type_of(
                                i_s,
                                &mut Matcher::default().with_ignore_positional_param_names(),
                                &second,
                            )
                            .bool()
                        {
                            add_multi_inheritance_issue();
                        } else if !inst1_lookup.attr_kind.is_writable()
                            && inst2_lookup.attr_kind.is_writable()
                        {
                            // This happens when @cached_property is overwritten with @property. This is
                            // allowed in Mypy (probably due to a logic error).
                            if !db.mypy_compatible() || !inst2_lookup.attr_kind.is_cached_property()
                            {
                                add_issue(
                                    IssueKind::CannotOverrideWritableAttributeWithReadOnlyProperty {
                                        name: name.into(),
                                        base_class: instance2.class.name().into(),
                                        other_class: cls1.name().into(),
                                    },
                                );
                            }
                        }
                    }
                }
            });
        }
    }
}

fn check_type_var_variance_for_base(
    i_s: &InferenceState,
    in_definition: PointLink,
    type_vars: &TypeVarLikes,
    base: &Type,
    mut add_issue: impl FnMut(IssueKind) -> bool,
) {
    for (i, check_type_var) in type_vars.iter().enumerate() {
        let TypeVarLike::TypeVar(tv) = check_type_var else {
            continue;
        };
        let TypeVarVariance::Known(tv_variance @ (Variance::Covariant | Variance::Contravariant)) =
            tv.variance
        else {
            continue;
        };
        if let Some(co_contra) =
            check_type_var_variance_validity_for_type(i_s, in_definition, i.into(), base)
        {
            let expected_variance = match (co_contra.co, co_contra.contra) {
                (false, true) => Variance::Contravariant,
                (false, false) => Variance::Invariant,
                (true, false) => Variance::Covariant,
                (true, true) => continue,
            };
            if expected_variance != tv_variance {
                add_issue(IssueKind::TypeVarVarianceIncompatibleWithParentType {
                    type_var_name: check_type_var.name(i_s.db).into(),
                });
            }
        }
    }
}

#[inline]
fn check_for_missing_annotations(
    i_s: &InferenceState,
    flags: &TypeCheckerFlags,
    function: Function,
    name: NameDef,
    return_annotation: Option<ReturnAnnotation>,
) {
    let has_param_annotations = function.has_param_annotations(i_s);
    let has_return_type = return_annotation.is_some()
        || function.class.is_some() && ["__init__", "__init_subclass__"].contains(&name.as_code());
    let has_explicit_annotation = has_return_type || has_param_annotations;
    if flags.disallow_untyped_defs || flags.disallow_incomplete_defs && has_explicit_annotation {
        let has_args = || function.iter_non_self_args(i_s).next().is_some();
        if !has_return_type && !has_param_annotations && has_args() {
            function.add_issue_for_declaration(i_s, IssueKind::FunctionIsUntyped);
        } else {
            if !has_return_type || return_annotation.is_none() && !has_args() {
                function.add_issue_for_declaration(
                    i_s,
                    IssueKind::FunctionMissingReturnAnnotation {
                        hint_return_none: function.might_be_missing_none_return_annotation(i_s),
                    },
                );
            }
            if function.is_missing_param_annotations(i_s) {
                function.add_issue_for_declaration(i_s, IssueKind::FunctionMissingParamAnnotations);
            }
        }
    }
}

fn diagnostics_for_scope(from: NodeRef, callable: impl FnOnce()) -> Result<(), ()> {
    let p = from.point();
    if p.calculated() {
        return Ok(());
    }
    if p.calculating() {
        return Err(());
    }
    from.set_point(Point::new_calculating());
    callable();
    if !from.point().calculated() {
        from.set_point(Point::new_specific(Specific::Analyzed, Locality::Todo));
    }
    Ok(())
}
