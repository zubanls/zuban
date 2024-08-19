use std::{
    borrow::Cow,
    cell::Cell,
    collections::{HashMap, HashSet},
    rc::Rc,
};

use parsa_python_cst::*;

use super::{first_defined_name, flow_analysis::FLOW_ANALYSIS, inference::await_};
use crate::{
    arguments::{CombinedArgs, KnownArgs, NoArgs},
    database::{
        ClassKind, ComplexPoint, Database, Locality, OverloadImplementation, Point, PointKind,
        Specific,
    },
    debug,
    diagnostics::{Issue, IssueKind},
    file::{inference::AssignKind, Inference},
    format_data::FormatData,
    imports::ImportResult,
    inference_state::InferenceState,
    inferred::{infer_class_method, AttributeKind, Inferred},
    matching::{ErrorStrs, Generics, LookupKind, Match, Matcher, OnTypeError, ResultContext},
    node_ref::NodeRef,
    params::{has_overlapping_params, matches_params, Param, WrappedParamType, WrappedStar},
    type_::{
        format_callable_params, AnyCause, CallableContent, CallableParams, ClassGenerics, DbString,
        FunctionKind, FunctionOverload, GenericItem, GenericsList, Literal, LiteralKind,
        LookupResult, NeverCause, ParamType, Type, TypeVarKind, TypeVarLike, Variance,
    },
    type_helpers::{
        cache_class_name, is_private, Class, ClassLookupOptions, FirstParamKind,
        FirstParamProperties, Function, Instance, InstanceLookupOptions, LookupDetails,
        TypeOrClass,
    },
    utils::debug_indent,
};

const ENUM_NAMES_OVERRIDABLE: [&str; 2] = ["value", "name"];
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

impl<'db> Inference<'db, '_, '_> {
    pub fn calculate_diagnostics(&self) -> Result<(), ()> {
        const FIRST_POINT: NodeIndex = 0;
        let first = self.file.points.get(FIRST_POINT);
        if first.calculated() {
            return Ok(());
        }
        if first.calculating() {
            return Err(());
        }
        self.file.points.set(FIRST_POINT, Point::new_calculating());
        FLOW_ANALYSIS.with(|fa| {
            fa.with_new_empty(|| {
                fa.with_new_frame_and_return_unreachable(|| {
                    self.calc_stmts_diagnostics(
                        self.file.tree.root().iter_stmt_likes(),
                        None,
                        None,
                    );
                });
                if self.flags().local_partial_types {
                    fa.check_for_unfinished_partials(self.i_s);
                }
                fa.process_delayed_funcs(self.i_s.db, |func| {
                    let result = self.ensure_func_diagnostics_and_finish_partials(fa, func);
                    debug_assert!(result.is_ok());
                });
                fa.check_for_unfinished_partials(self.i_s);
                fa.debug_assert_is_empty();
            })
        });
        for complex_point in unsafe { self.file.complex_points.iter() } {
            if let ComplexPoint::NewTypeDefinition(n) = complex_point {
                // Make sure types are calculated and the errors are generated.
                n.type_(self.i_s);
            }
        }

        if let Some(link) = self.file.lookup_global("__getattribute__") {
            NodeRef::new(self.file, link.node_index)
                .add_issue(self.i_s, IssueKind::GetattributeInvalidAtModuleLevel)
        }
        if let Some(link) = self.file.lookup_global("__getattr__") {
            let actual = self.infer_name_of_definition_by_index(link.node_index);
            let actual = actual.as_cow_type(self.i_s);
            let Type::Callable(callable) = &self.i_s.db.python_state.valid_getattr_supertype else {
                unreachable!();
            };

            if !Type::Callable(Rc::new(callable.remove_first_positional_param().unwrap()))
                .is_simple_super_type_of(self.i_s, &actual)
                .bool()
            {
                self.add_issue(
                    link.node_index,
                    IssueKind::InvalidSpecialMethodSignature {
                        type_: actual.format_short(self.i_s.db),
                        special_method: "__getattr__",
                    },
                )
            }
        }
        self.file
            .points
            .set(FIRST_POINT, Point::new_node_analysis(Locality::Todo));
        Ok(())
    }

    fn check_assignment(&self, assignment: Assignment, class: Option<Class>) {
        self.cache_assignment(assignment);

        // Check if protocol assignment is invalid
        if class.is_some_and(|cls| {
            cls.is_protocol(self.i_s.db)
                && match assignment.unpack() {
                    AssignmentContent::WithAnnotation(_, annotation, _) => {
                        if self.file.points.get(annotation.index()).maybe_specific()
                            == Some(Specific::AnnotationOrTypeCommentFinal)
                        {
                            self.add_issue(
                                annotation.index(),
                                IssueKind::ProtocolMemberCannotBeFinal,
                            )
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
                    if let Some(ImportResult::File(file)) = self.import_from_first_part(import_from)
                    {
                        let imported = self.i_s.db.loaded_python_file(file);
                        if imported.has_unsupported_class_scoped_import(self.i_s) {
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
        if !valid_raise_type(
            self.i_s,
            NodeRef::new(self.file, expr.index()),
            &self.infer_expression(expr).as_cow_type(self.i_s),
            allow_none,
        ) {
            NodeRef::new(self.file, expr.index())
                .add_issue(self.i_s, IssueKind::BaseExceptionExpectedForRaise);
        }
    }

    fn add_unreachable_error(&self, start_position: CodeIndex, end_position: CodeIndex) {
        if self.flags().warn_unreachable {
            FLOW_ANALYSIS.with(|fa| {
                fa.report_unreachable_if_not_reported_before(|| {
                    self.file.add_issue(
                        self.i_s,
                        Issue {
                            kind: IssueKind::UnreachableStatement,
                            start_position,
                            end_position,
                        },
                    )
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
        // TODO In general all {} blocks are todos
        for stmt_like in stmts {
            let point = self.file.points.get(stmt_like.parent_index);
            if point.calculated() {
                debug_assert_eq!(point.kind(), PointKind::NodeAnalysis);
                continue;
            }
            if self.is_unreachable() {
                if self.stmt_is_allowed_when_unreachable(stmt_like.node) {
                    continue;
                } else {
                    let start = self.file.tree.node_start_position(stmt_like.parent_index);
                    let end = self.file.tree.node_end_position(stmt_like.parent_index);
                    self.add_unreachable_error(start, end);
                    /*
                    if self.flags().mypy_compatible {
                        // Mypy does not analyze frames that are not reachable. However for normal interaction
                        // in an IDE you typically want to analyze those parts of code, even if they are
                        // unreachable.
                        break;
                    }
                    */
                    break;
                }
            }

            match stmt_like.node {
                StmtLikeContent::Assignment(assignment) => self.check_assignment(assignment, class),
                StmtLikeContent::StarExpressions(star_exprs) => {
                    self.infer_star_expressions(star_exprs, &mut ResultContext::ExpectUnused);
                }
                StmtLikeContent::ReturnStmt(return_stmt) => {
                    self.calc_return_stmt_diagnostics(func, return_stmt);
                    self.mark_current_frame_unreachable()
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
                StmtLikeContent::PassStmt(x) => {}
                StmtLikeContent::GlobalStmt(x) => {}
                StmtLikeContent::NonlocalStmt(x) => {}
                StmtLikeContent::AssertStmt(assert_stmt) => {
                    self.flow_analysis_for_assert(assert_stmt);
                }
                StmtLikeContent::BreakStmt(b) => self.flow_analysis_for_break_stmt(b),
                StmtLikeContent::ContinueStmt(c) => self.flow_analysis_for_continue_stmt(c),
                StmtLikeContent::DelStmt(d) => self.flow_analysis_for_del_stmt(d.targets()),
                StmtLikeContent::FunctionDef(f) => {
                    self.maybe_delay_func_diagnostics(f, class, func)
                }
                StmtLikeContent::ClassDef(class) => self.calc_class_diagnostics(class),
                StmtLikeContent::Decorated(decorated) => match decorated.decoratee() {
                    Decoratee::FunctionDef(f) => self.maybe_delay_func_diagnostics(f, class, func),
                    Decoratee::ClassDef(class) => self.calc_class_diagnostics(class),
                    Decoratee::AsyncFunctionDef(f) => {
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
                    debug!("TODO match_stmt diagnostics");
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
                StmtLikeContent::Error(_) | StmtLikeContent::Newline => {}
            };
            self.file.points.set(
                stmt_like.parent_index,
                Point::new_node_analysis(Locality::Todo),
            );
        }
    }

    fn stmt_is_allowed_when_unreachable(&self, s: StmtLikeContent) -> bool {
        // In Mypy this is called is_noop_for_reachability
        match s {
            StmtLikeContent::RaiseStmt(_) | StmtLikeContent::PassStmt(_) => true,
            StmtLikeContent::AssertStmt(assert_stmt) => {
                match assert_stmt.unpack().0.maybe_unpacked_atom() {
                    Some(AtomContent::Bool(b)) if b.as_code() == "False" => true,
                    Some(AtomContent::Int(i)) if i.parse() == Some(0) => true,
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
            let (expr, target) = with_item.unpack();
            let from = NodeRef::new(self.file, expr.index());
            let result = self.infer_expression(expr);
            let mut enter_result = result.type_lookup_and_execute_with_attribute_error(
                self.i_s,
                from,
                match is_async {
                    false => "__enter__",
                    true => "__aenter__",
                },
                &NoArgs::new(from),
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
            if let Some(target) = target {
                self.assign_targets(
                    target,
                    enter_result,
                    NodeRef::new(self.file, with_item.index()),
                    AssignKind::Normal,
                )
            }
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

    fn calc_untyped_block_diagnostics(&self, block: Block) {
        for interesting in block.search_relevant_untyped_nodes() {
            match interesting {
                RelevantUntypedNode::Primary(p) => {
                    let PrimaryOrAtom::Atom(atom) = p.first() else {
                        continue;
                    };
                    let AtomContent::Name(n) = atom.unpack() else {
                        continue;
                    };
                    if n.as_code() == "reveal_type" && !self.file.points.get(n.index()).calculated()
                    {
                        self.infer_name_reference(n);
                        let PrimaryContent::Execution(_) = p.second() else {
                            continue;
                        };
                        let n = NodeRef::new(self.file, p.index());
                        n.add_issue(self.i_s, IssueKind::Note("Revealed type is \"Any\"".into()));
                        n.add_issue(
                            self.i_s,
                            IssueKind::Note(
                                "'reveal_type' always outputs 'Any' in unchecked functions".into(),
                            ),
                        );
                    }
                }
                RelevantUntypedNode::Assignment(a) => {
                    let is_type_definition = match a.unpack() {
                        AssignmentContent::Normal(_, right) => {
                            self.check_for_type_comment(a).is_some()
                        }
                        AssignmentContent::WithAnnotation(_, annotation, _) => true,
                        AssignmentContent::AugAssign(..) => false,
                    };
                    if is_type_definition {
                        NodeRef::new(self.file, a.index())
                            .add_issue(self.i_s, IssueKind::AnnotationInUntypedFunction);
                    }
                }
                RelevantUntypedNode::ImportFrom(i) => self.cache_import_from(i),
                RelevantUntypedNode::ImportName(i) => self.cache_import_name(i),
                RelevantUntypedNode::FunctionDef(func) => {
                    // TODO
                }
                RelevantUntypedNode::ClassDef(class) => {
                    // TODO
                }
            }
        }
    }

    pub fn calc_block_diagnostics(
        &self,
        block: Block,
        class: Option<Class>,
        func: Option<&Function>,
    ) {
        self.calc_stmts_diagnostics(block.iter_stmt_likes(), class, func)
    }

    fn calc_class_diagnostics(&self, class: ClassDef) {
        let (arguments, block) = class.unpack();
        cache_class_name(NodeRef::new(self.file, class.name_def().index()), class);
        let class_node_ref = NodeRef::new(self.file, class.index());
        class_node_ref.ensure_cached_class_infos(self.i_s);
        let db = self.i_s.db;
        let c = Class::with_self_generics(db, class_node_ref);
        let class_infos = c.use_cached_class_infos(db);
        if matches!(class_infos.class_kind, ClassKind::TypedDict) {
            // TypedDicts are special, because they really only contain annotations and no methods.
            // We skip all of this logic, because there's custom logic for TypedDicts.
            return;
        }
        let i_s = self.i_s.with_diagnostic_class_context(&c);
        let inference = self.file.inference(&i_s);
        inference.calc_block_diagnostics(block, Some(c), None);

        check_multiple_inheritance(
            self.i_s,
            || c.bases(db),
            // Don't check symbols if they are part of the instance that we are currently using.
            |name| {
                c.lookup_symbol(self.i_s, name)
                    .into_maybe_inferred()
                    .is_none()
            },
            |issue| NodeRef::new(self.file, arguments.unwrap().index()).add_issue(self.i_s, issue),
        );
        for table in [
            &c.class_storage.class_symbol_table,
            &c.class_storage.self_symbol_table,
        ] {
            for (name, index) in table.iter() {
                if is_private(name) {
                    continue;
                }
                let lookup_infos = c.lookup(
                    &i_s,
                    name,
                    ClassLookupOptions::new(&|issue| ())
                        .without_descriptors()
                        .with_ignore_self(),
                );
                if let Some(original_inf) = lookup_infos.lookup.into_maybe_inferred() {
                    if lookup_infos.attr_kind == AttributeKind::Final {
                        NodeRef::new(self.file, *index).add_issue(
                            &i_s,
                            IssueKind::CannotOverrideFinalAttribute {
                                name: name.into(),
                                base_class: lookup_infos.class.name(i_s.db).into(),
                            },
                        );
                        continue;
                    }
                    let is_final_callable = match original_inf.as_cow_type(&i_s).as_ref() {
                        Type::Callable(c) => c.is_final,
                        Type::FunctionOverload(_) => original_inf
                            .maybe_saved_node_ref(i_s.db)
                            .is_some_and(|node_ref| {
                                if let Some(ComplexPoint::FunctionOverload(o)) = node_ref.complex()
                                {
                                    o.is_final
                                } else {
                                    false
                                }
                            }),
                        _ => false,
                    };
                    if is_final_callable {
                        NodeRef::new(self.file, *index).add_issue_onto_start_including_decorator(
                            &i_s,
                            IssueKind::CannotOverrideFinalAttribute {
                                base_class: lookup_infos.class.name(i_s.db).into(),
                                name: name.into(),
                            },
                        );
                    }
                }

                if IGNORED_INHERITANCE_NAMES.contains(&name) {
                    continue;
                }
                let mut node_ref = NodeRef::new(self.file, *index - NAME_DEF_TO_NAME_DIFFERENCE);
                if name == "__post_init__" {
                    if let Some(dataclass) = c.maybe_dataclass(db) {
                        let override_details = Instance::new(c, None).lookup_on_self(
                            self.i_s,
                            &|issue| todo!(),
                            name,
                            LookupKind::OnlyType,
                        );
                        let __post_init__ = dataclass.expect_calculated_post_init();
                        let original_details = LookupDetails {
                            class: TypeOrClass::Type(Cow::Owned(Type::Dataclass(
                                dataclass.clone(),
                            ))),
                            lookup: LookupResult::UnknownName(Inferred::from_type(Type::Callable(
                                Rc::new(__post_init__.clone()),
                            ))),
                            attr_kind: AttributeKind::DefMethod,
                        };
                        check_override(
                            &i_s,
                            node_ref,
                            original_details,
                            override_details,
                            name,
                            |_, _| "dataclass",
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
                        continue;
                    }
                }

                // Calculate if there is an @override decorator
                let mut has_override_decorator = false;
                if let Some(func_def) = NodeRef::new(self.file, *index).maybe_name_of_function() {
                    if !func_def.is_typed() && !self.flags().check_untyped_defs {
                        // Mypy completely ignores untyped functions.
                        continue;
                    }
                    if let Some(decorated) = func_def.maybe_decorated() {
                        let decorators = decorated.decorators();
                        for decorator in decorators.iter() {
                            if let Some(redirect) =
                                NodeRef::new(self.file, decorator.index()).maybe_redirect(db)
                            {
                                if Some(redirect) == db.python_state.typing_override() {
                                    has_override_decorator = true;
                                }
                                if redirect == db.python_state.typing_overload() {
                                    // In Mypy the error is on the first decorator of an @overload.
                                    node_ref = NodeRef::new(
                                        self.file,
                                        decorators
                                            .iter()
                                            .next()
                                            .unwrap()
                                            .named_expression()
                                            .index(),
                                    );
                                }
                            }
                        }
                    }
                }

                find_and_check_override(self.i_s, node_ref, c, name, has_override_decorator)
            }
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
                )
            }
        }
        if matches!(class_infos.class_kind, ClassKind::Protocol) {
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
                    )
                }
            }
            check_protocol_type_var_variances(self.i_s, c)
        }
    }

    fn maybe_delay_func_diagnostics(
        &self,
        f: FunctionDef,
        class: Option<Class>,
        in_func: Option<&Function>,
    ) {
        let function = Function::new(NodeRef::new(self.file, f.index()), class);
        function.cache_func(self.i_s);
        if let Some(ComplexPoint::TypeInstance(Type::Callable(c))) = function.node_ref.complex() {
            if c.no_type_check {
                return;
            }
        }

        if in_func.is_some() {
            let _ = self.ensure_func_diagnostics(function);
        } else {
            FLOW_ANALYSIS.with(|fa| {
                fa.add_delayed_func(
                    function.node_ref.as_link(),
                    class.map(|c| c.node_ref.as_link()),
                )
            })
        }
    }

    pub fn ensure_func_diagnostics(&self, function: Function) -> Result<(), ()> {
        let func_node = function.node();
        let from = NodeRef::new(self.file, func_node.body().index());
        let p = from.point();
        if p.calculated() {
            return Ok(());
        }
        if p.calculating() {
            return Err(());
        }
        from.set_point(Point::new_calculating());
        debug_indent(|| {
            debug!("Diagnostics for function {}", function.name());
            self.calc_func_diagnostics(function, func_node)
        });
        from.set_point(Point::new_node_analysis(Locality::Todo));
        Ok(())
    }

    fn calc_func_diagnostics(&self, function: Function, func_node: FunctionDef) {
        let i_s = self.i_s;
        let is_protocol = function.class.is_some_and(|cls| cls.is_protocol(i_s.db));
        if is_protocol && function.is_final() {
            function.add_issue_onto_start_including_decorator(
                i_s,
                IssueKind::ProtocolMemberCannotBeFinal,
            )
        }
        FLOW_ANALYSIS.with(|fa| {
            let mut is_overload_member = false;
            let unreachable = fa.with_new_frame_and_return_unreachable(|| {
                if func_node.is_empty_generator_function() {
                    fa.enable_reported_unreachable_in_top_frame();
                }
                is_overload_member = self
                    .calc_function_diagnostics_internal_and_return_is_overload(function, func_node)
            });
            if !unreachable
                && !is_overload_member
                && !self.file.is_stub()
                && function.return_annotation().is_some()
                && !(self.flags().allow_empty_bodies && function.has_trivial_body(i_s))
                && !function.is_abstract()
                && !self.in_type_checking_only_block()
            {
                let ret_type = function.expected_return_type_for_return_stmt(i_s);
                let has_trivial_body = function.has_trivial_body(i_s);
                let maybe_add_async = || {
                    if has_trivial_body
                        && function
                            .class
                            .and_then(|c| c.maybe_metaclass(i_s.db))
                            .is_some_and(|metaclass| {
                                metaclass == i_s.db.python_state.abc_meta_link()
                            })
                    {
                        self.add_issue(
                            func_node.name().index(),
                            IssueKind::Note(
                                "If the method is meant to be abstract, use @abc.abstractmethod"
                                    .into(),
                            ),
                        );
                    }
                };
                if matches!(ret_type.as_ref(), Type::Never(_)) {
                    self.add_issue(
                        func_node.name().index(),
                        IssueKind::ImplicitReturnInFunctionWithNeverReturn,
                    );
                    maybe_add_async()
                } else {
                    let is_valid = ret_type.is_simple_super_type_of(i_s, &Type::None).bool();
                    if self.flags().warn_no_return {
                        if (!is_valid
                            || !has_trivial_body
                                && !matches!(ret_type.as_ref(), Type::None | Type::Any(_)))
                            && !is_protocol
                        {
                            self.add_issue(
                                func_node.name().index(),
                                IssueKind::MissingReturnStatement {
                                    code: if has_trivial_body {
                                        "empty-body"
                                    } else {
                                        "return"
                                    },
                                },
                            );
                            maybe_add_async()
                        }
                    } else if !is_valid {
                        self.add_issue(
                            func_node.name().index(),
                            IssueKind::IncompatibleImplicitReturn {
                                expected: ret_type.format_short(i_s.db),
                            },
                        );
                        maybe_add_async()
                    }
                }
            }
        })
    }

    fn calc_function_diagnostics_internal_and_return_is_overload(
        &self,
        function: Function,
        func_node: FunctionDef,
    ) -> bool {
        let i_s = self.i_s;
        let mut is_overload_member = false;
        if let Some(ComplexPoint::FunctionOverload(o)) = function.node_ref.complex() {
            is_overload_member = true;
            for (i, c1) in o.iter_functions().enumerate() {
                if let Some(implementation) = &o.implementation {
                    let mut c1 = Cow::Borrowed(c1.as_ref());
                    let mut c_impl = Cow::Borrowed(&implementation.callable);
                    if let Some(class) = function.class {
                        let needs_remap = |c: &CallableContent| {
                            matches!(
                                c.kind,
                                FunctionKind::Function {
                                    had_first_self_or_class_annotation: true
                                }
                            )
                        };
                        if needs_remap(&c1) || needs_remap(&c_impl) {
                            let remap = |c: &CallableContent| {
                                let mut matcher = Matcher::new_callable_matcher(c);
                                let first_type = c.first_positional_type()?;
                                if !first_type
                                    .is_super_type_of(
                                        i_s,
                                        &mut matcher,
                                        &Class::with_undefined_generics(class.node_ref)
                                            .as_type(i_s.db),
                                    )
                                    .bool()
                                {
                                    return None;
                                }
                                let c = c.remove_first_positional_param()?;
                                Some(matcher.remove_self_from_callable(i_s, c))
                            };
                            // Try to remove the self signatures and if it doesn't work, we just
                            // don't remove the signatures. We assume that if we cannot remap that
                            // an error was raised in a different place.
                            if let Some((new_c1, new_c2)) = remap(&c1).zip(remap(&c_impl)) {
                                c1 = Cow::Owned(new_c1);
                                c_impl = Cow::Owned(new_c2);
                            }
                        }
                    }
                    self.calc_overload_implementation_diagnostics(
                        &c1,
                        &c_impl,
                        implementation,
                        i + 1,
                    )
                }
                for (k, c2) in o.iter_functions().skip(i + 1).enumerate() {
                    if is_overload_unmatchable(i_s, c1, c2) {
                        NodeRef::from_link(i_s.db, c2.defined_at).add_issue(
                            i_s,
                            IssueKind::OverloadUnmatchable {
                                matchable_signature_index: i + 1,
                                unmatchable_signature_index: i + k + 2,
                            },
                        );
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
                        NodeRef::from_link(i_s.db, c1.defined_at).add_issue(
                            i_s,
                            IssueKind::OverloadIncompatibleReturnTypes {
                                first_signature_index: i + 1,
                                second_signature_index: i + k + 2,
                            },
                        );
                    }
                }
            }
        } else if function.node_ref.point().maybe_specific() == Some(Specific::OverloadUnreachable)
        {
            is_overload_member = !function.is_overload_implementation();
        }

        let func_kind = function.kind();

        let (name, params, return_annotation, block) = func_node.unpack();
        if !is_overload_member {
            // Check defaults here.
            for param in params.iter() {
                if let Some(annotation) = param.annotation() {
                    if let Some(default) = param.default() {
                        let t = self.use_cached_param_annotation_type(annotation);
                        let inf = self
                            .infer_expression_with_context(default, &mut ResultContext::Known(&t));
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
        }
        let flags = self.flags();
        let mut had_missing_annotation = false;
        let mut params_iterator = params.iter().peekable();
        if let Some(class) = function.class {
            if func_kind != FunctionKind::Staticmethod || function.is_dunder_new() {
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
                        let undefined_generics_class =
                            Class::with_undefined_generics(class.node_ref);
                        let mut class_t = undefined_generics_class.as_type(i_s.db);
                        let mut original = self.use_cached_param_annotation_type(annotation);
                        match original.as_ref() {
                            Type::TypeVar(tv) => {
                                if let TypeVarKind::Bound(b) = &tv.type_var.kind {
                                    original = Cow::Owned(b.clone());
                                }
                            }
                            Type::Type(t) => {
                                if let Type::TypeVar(tv) = t.as_ref() {
                                    if let TypeVarKind::Bound(b) = &tv.type_var.kind {
                                        original = Cow::Owned(Type::Type(Rc::new(b.clone())));
                                    }
                                }
                            }
                            _ => (),
                        };
                        let erased = original.replace_type_var_likes_and_self(
                            i_s.db,
                            &mut |u| u.as_any_generic_item(),
                            &|| class_t.clone(),
                        );
                        let erased_is_protocol = match &erased {
                            Type::Class(c) => c.class(i_s.db).is_protocol(i_s.db),
                            Type::Type(t) => {
                                t.maybe_class(i_s.db).is_some_and(|c| c.is_protocol(i_s.db))
                            }
                            _ => false,
                        };
                        if !erased_is_protocol {
                            if function.first_param_kind(i_s) == FirstParamKind::ClassOfSelf {
                                class_t = Type::Type(Rc::new(class_t));
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
                            }
                        }
                    }
                } else if !was_star {
                    function
                        .node_ref
                        .add_issue(i_s, IssueKind::MethodWithoutArguments)
                }
            }
        }
        for param in params_iterator {
            if let Some(annotation) = param.annotation() {
                let t = self.use_cached_param_annotation_type(annotation);
                if matches!(t.as_ref(), Type::TypeVar(tv) if tv.type_var.variance == Variance::Covariant)
                    && !["__init__", "__new__", "__post_init__"].contains(&name.as_code())
                {
                    NodeRef::new(self.file, annotation.index())
                        .add_issue(i_s, IssueKind::TypeVarCovariantInParamType);
                }

                if param.kind() == ParamKind::StarStar {
                    if let Type::TypedDict(td) = t.as_ref() {
                        let mut overlapping_names = vec![];
                        for member in td.members(i_s.db) {
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
            } else if flags.disallow_incomplete_defs {
                had_missing_annotation = true;
            }
        }
        if had_missing_annotation {
            function
                .node_ref
                .add_issue(i_s, IssueKind::FunctionMissingParamAnnotations);
        }

        if let Some(return_annotation) = return_annotation {
            let t = self.use_cached_return_annotation_type(return_annotation);
            if matches!(t.as_ref(), Type::TypeVar(tv) if tv.type_var.variance == Variance::Contravariant)
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
        } else if flags.disallow_incomplete_defs {
            function.add_issue_for_declaration(
                i_s,
                IssueKind::FunctionMissingReturnAnnotation {
                    hint_return_none: false,
                },
            )
        }

        let args = NoArgs::new(function.node_ref);
        let function_i_s = &mut i_s.with_diagnostic_func_and_args(&function);
        let inference = self.file.inference(function_i_s);
        if function.is_typed() || flags.check_untyped_defs {
            inference.calc_block_diagnostics(block, None, Some(&function))
        } else {
            inference.calc_untyped_block_diagnostics(block)
        }
        if flags.disallow_untyped_defs && !flags.disallow_incomplete_defs {
            match (
                function.is_missing_param_annotations(i_s),
                function.return_annotation().is_none(),
            ) {
                (true, true) => {
                    function.add_issue_for_declaration(i_s, IssueKind::FunctionIsDynamic)
                }
                (true, false) => function
                    .add_issue_for_declaration(i_s, IssueKind::FunctionMissingParamAnnotations),
                (false, true) => {
                    function.add_issue_for_declaration(
                        i_s,
                        IssueKind::FunctionMissingReturnAnnotation {
                            hint_return_none: function.might_be_missing_none_return_annotation(i_s),
                        },
                    );
                }
                (false, false) => (),
            }
        }

        if function.is_dunder_new() {
            let mut class = function.class.unwrap();
            // Here we do not want self generics, we actually want Any generics.
            class.generics = Generics::NotDefinedYet;
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
                            function.expect_return_annotation_node_ref().add_issue(
                                i_s,
                                IssueKind::NewIncompatibleReturnType {
                                    returns: t.format_short(i_s.db),
                                    must_return: class.format_short(i_s.db),
                                },
                            )
                        }
                    }
                    Type::Type(_) => (),
                    Type::Any(_) => (),
                    Type::Enum(e) if e.class == class.node_ref.as_link() => (),
                    t => function.expect_return_annotation_node_ref().add_issue(
                        i_s,
                        IssueKind::NewMustReturnAnInstance {
                            got: t.format_short(i_s.db),
                        },
                    ),
                }
            }
        }

        if flags.disallow_any_unimported {
            for param in params
                .iter()
                .skip((function.class.is_some() && func_kind != FunctionKind::Staticmethod).into())
            {
                if let Some(annotation) = param.annotation() {
                    let t = self.use_cached_param_annotation_type(annotation);
                    // TODO implement --disallow-any-unimported
                }
            }
        }

        if let Some(magic_name) = name
            .as_code()
            .strip_prefix("__")
            .and_then(|n| n.strip_suffix("__"))
        {
            if function.class.is_some() {
                match magic_name {
                    "init" | "init_subclass" => {
                        if let Some(return_annotation) = function.return_annotation() {
                            if !matches!(function.return_type(i_s).as_ref(), Type::None) {
                                // __init__ and __init_subclass__ must return None
                                NodeRef::new(self.file, return_annotation.expression().index())
                                    .add_issue(
                                        i_s,
                                        IssueKind::MustReturnNone {
                                            function_name: function.name().into(),
                                        },
                                    )
                            }
                        }
                    }
                    "exit" => {
                        // Check the return type of __exit__
                        self.check_magic_exit(function)
                    }
                    "getattr" => {
                        let func_type = function.as_type(self.i_s, FirstParamProperties::None);
                        if !self
                            .i_s
                            .db
                            .python_state
                            .valid_getattr_supertype
                            .clone()
                            .is_simple_super_type_of(self.i_s, &func_type)
                            .bool()
                        {
                            function.add_issue_for_declaration(
                                self.i_s,
                                IssueKind::InvalidSpecialMethodSignature {
                                    type_: func_type.format_short(self.i_s.db),
                                    special_method: "__getattr__",
                                },
                            )
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
        is_overload_member
    }

    fn calc_overload_implementation_diagnostics(
        &self,
        overload_item: &CallableContent,
        implementation_callable: &CallableContent,
        implementation: &OverloadImplementation,
        signature_index: usize,
    ) {
        let matcher = &mut Matcher::new_reverse_callable_matcher(implementation_callable);
        let implementation_result = &implementation_callable.return_type;
        let item_result = &overload_item.return_type;
        // This is bivariant matching. This is how Mypy allows subtyping.
        if !item_result
            .is_sub_type_of(self.i_s, matcher, implementation_result)
            .bool()
            && !item_result
                .is_super_type_of(self.i_s, matcher, implementation_result)
                .bool()
        {
            implementation
                .function(self.i_s.db, None)
                .add_issue_onto_start_including_decorator(
                    self.i_s,
                    IssueKind::OverloadImplementationReturnTypeIncomplete { signature_index },
                );
        }

        let match_ = matches_params(
            self.i_s,
            matcher,
            &overload_item.params,
            &implementation_callable.params,
        );
        if !match_.bool() {
            implementation
                .function(self.i_s.db, None)
                .add_issue_onto_start_including_decorator(
                    self.i_s,
                    IssueKind::OverloadImplementationArgumentsNotBroadEnough { signature_index },
                );
        }
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
                        self.infer_star_expressions(star_exprs, &mut ResultContext::Known(&t));
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
                        )
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

    pub fn cache_for_stmt_names(
        &self,
        star_targets: StarTargets,
        star_exprs: StarExpressions,
        is_async: bool,
    ) {
        let star_targets_point = self.file.points.get(star_targets.index());
        if star_targets_point.calculated() {
            debug_assert_eq!(star_targets_point.kind(), PointKind::NodeAnalysis);
            return;
        }
        let inf = self.infer_star_expressions(star_exprs, &mut ResultContext::Unknown);
        let from = NodeRef::new(self.file, star_exprs.index());
        let element = if is_async {
            await_aiter_and_next(self.i_s, inf, from)
        } else {
            inf.iter(self.i_s, from).infer_all(self.i_s)
        };
        debug!("For loop input: {}", element.format_short(self.i_s));
        self.assign_targets(star_targets.as_target(), element, from, AssignKind::Normal);
        self.file.points.set(
            star_targets.index(),
            Point::new_node_analysis(Locality::Todo),
        );
    }

    pub fn calc_fstring_diagnostics(&self, fstring: FString) {
        self.calc_fstring_content_diagnostics(fstring.iter_content())
    }

    fn calc_fstring_content_diagnostics<'x>(&self, iter: impl Iterator<Item = FStringContent<'x>>) {
        for content in iter {
            match content {
                FStringContent::FStringExpr(e) => {
                    let (expressions, spec) = e.unpack();
                    self.infer_star_expressions(expressions, &mut ResultContext::Unknown);
                    if let Some(spec) = spec {
                        self.calc_fstring_content_diagnostics(spec.iter_content());
                    }
                }
                FStringContent::FStringString(_) => (),
            }
        }
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
            )
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
            from.file_index(),
            normal_magic,
            LookupKind::OnlyType,
            &mut ResultContext::Unknown,
            &|issue| todo!(),
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
                        )
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
                    _ => from.add_issue(
                        i_s,
                        IssueKind::ForwardOperatorIsNotCallable {
                            forward_name: normal_magic,
                        },
                    ),
                }
            },
        )
    }

    fn check_inplace_methods(&self, func: Function, inplace_magic_name: &str) {
        let i_s = self.i_s;
        let Some(normal_magic_name) = INPLACE_TO_NORMAL_METHODS.get(inplace_magic_name) else {
            return;
        };
        let normal_method = func
            .class
            .unwrap()
            .lookup_without_descriptors(i_s, func.node_ref, normal_magic_name)
            .lookup;
        let inplace_method = func
            .class
            .unwrap()
            .lookup_without_descriptors(i_s, func.node_ref, func.name())
            .lookup;
        if !normal_method
            .into_inferred()
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
            )
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
                let inf =
                    self.infer_star_expressions(star_expressions, &mut ResultContext::Unknown);
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
    let check = |cls: Class| {
        cls.incomplete_mro(db)
            || cls.class_link_in_mro(db, db.python_state.base_exception_node_ref().as_link())
    };
    match t {
        Type::Class(c) => check(c.class(db)),
        Type::Type(t) => match t.as_ref() {
            Type::Class(c) => {
                let cls = c.class(db);
                cls.execute(
                    i_s,
                    &NoArgs::new(from),
                    &mut ResultContext::Unknown,
                    OnTypeError::new(&|_, _, _, _| {
                        unreachable!(
                            "Type errors should not be possible, because there are no params"
                        )
                    }),
                    false,
                );
                check(cls)
            }
            _ => false,
        },
        Type::Any(_) => true,
        Type::Never(_) => todo!(),
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
        base.type_lookup_and_execute(i_s, from.file, "__aiter__", &NoArgs::new(from), &|t| {
            from.add_issue(
                i_s,
                IssueKind::AsyncNotIterable {
                    type_: t.format_short(i_s.db),
                },
            )
        })
        .type_lookup_and_execute_with_attribute_error(
            i_s,
            from,
            "__anext__",
            &NoArgs::new(from),
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
        let add_kind_info = |notes: &mut Vec<Box<str>>, kind| match kind {
            FunctionKind::Classmethod { .. } => notes.push(format!("{prefix}@classmethod").into()),
            FunctionKind::Staticmethod { .. } => {
                notes.push(format!("{prefix}@staticmethod").into())
            }
            _ => (),
        };
        match inf.as_cow_type(i_s).as_ref() {
            Type::Callable(c) if !matches!(c.kind, FunctionKind::Property { .. }) => {
                add_kind_info(notes, c.kind);
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
                    add_kind_info(notes, c.kind);
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
    let mut matcher = Matcher::new_reverse_callable_matcher(c1).without_precise_matching();
    let result = matches_params(i_s, &mut matcher, &c2.params, &c1.params);
    matches!(result, Match::True { with_any: false })
}

fn find_and_check_override(
    i_s: &InferenceState,
    from: NodeRef,
    override_class: Class,
    name: &str,
    has_override_decorator: bool,
) {
    let override_class_infos = override_class.use_cached_class_infos(i_s.db);
    let instance = Instance::new(override_class, None);
    let add_lookup_issue = |issue| {
        // This is issue is only relevant for actual lookups
        if !matches!(issue, IssueKind::NotAcceptingSelfArgument { .. }) {
            from.add_issue(i_s, issue)
        }
    };
    let original_details = instance.lookup(
        i_s,
        name,
        // NamedTuple / Tuple are special, because they insert an additional type of themselves.
        InstanceLookupOptions::new(&add_lookup_issue).with_super_count(
            1 + matches!(
                override_class_infos.class_kind,
                ClassKind::Tuple | ClassKind::NamedTuple
            ) as usize,
        ),
    );
    if original_details.lookup.is_some() {
        let override_details =
            instance.lookup_with_details(i_s, add_lookup_issue, name, LookupKind::Normal);
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
        if let Some(t) = override_class_infos.undefined_generics_type.get() {
            if let Type::Enum(e) = t.as_ref() {
                if e.members.iter().any(|member| member.name(i_s.db) == name)
                    && !ENUM_NAMES_OVERRIDABLE.contains(&name)
                {
                    from.add_issue(
                        i_s,
                        IssueKind::EnumCannotOverrideWritableAttributeWithFinal {
                            name: name.into(),
                        },
                    )
                }
            }
        }
        check_override(
            i_s,
            from,
            original_details,
            override_details,
            name,
            |db, c| c.name(db),
            None,
        );
    } else if has_override_decorator {
        from.add_issue(i_s, IssueKind::MissingBaseForOverride { name: name.into() });
    }
}

fn check_override(
    i_s: &InferenceState,
    from: NodeRef,
    original_lookup_details: LookupDetails,
    override_lookup_details: LookupDetails,
    name: &str,
    original_class_name: impl for<'x> Fn(&'x Database, &'x TypeOrClass) -> &'x str,
    original_formatter: Option<&dyn Fn() -> String>,
) {
    let original_inf = original_lookup_details.lookup.into_inferred();
    let original_t = original_inf.as_cow_type(i_s);
    let original_class = original_lookup_details.class;
    let override_inf = override_lookup_details.lookup.into_inferred();
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
                .map(|func| Function::new(node_ref, None))
                .filter(|func| func.node().name_def().index() == from.node_index)
        }
        _ => None,
    };

    let mut match_ = original_t.is_super_type_of(
        i_s,
        &mut Matcher::default().with_ignore_positional_param_names(),
        override_t,
    );

    let mut op_method_wider_note = false;
    if let Type::FunctionOverload(override_overload) = override_t {
        if match_.bool()
            && FORWARD_OP_METHODS.contains(name)
            && operator_domain_is_widened(i_s, override_overload, &original_t)
        {
            // Reverse operators lead to weird behavior when overloads widen. If you want to
            // understand why this is an issue, please look at testUnsafeDunderOverlapInSubclass.
            op_method_wider_note = true;
            match_ = Match::new_false();
        }
    }
    use AttributeKind::*;
    match (
        original_lookup_details.attr_kind,
        override_lookup_details.attr_kind,
    ) {
        (
            AttributeKind::Property {
                writable: writable1,
            },
            AttributeKind::Property {
                writable: writable2,
            },
        ) => {
            if writable1 && !writable2 {
                let func = from
                    .add_to_node_index(NAME_DEF_TO_NAME_DIFFERENCE as i64)
                    .maybe_name_of_function()
                    .unwrap();
                Function::new(NodeRef::new(from.file, func.index()), None)
                    .add_issue_onto_start_including_decorator(
                        i_s,
                        IssueKind::ReadOnlyPropertyCannotOverwriteReadWriteProperty,
                    );
            }
        }
        (Classmethod | Staticmethod, DefMethod) => {
            // Some method types may be overridden, because they still work the same way on class
            // and instance, others not.
            match_ = Match::new_false();
        }
        (ClassVar, AnnotatedAttribute) => from.add_issue(
            i_s,
            IssueKind::CannotOverrideClassVariableWithInstanceVariable {
                base_class: original_class_name(i_s.db, &original_class).into(),
            },
        ),
        (AnnotatedAttribute, ClassVar) => from.add_issue(
            i_s,
            IssueKind::CannotOverrideInstanceVariableWithClassVariable {
                base_class: original_class_name(i_s.db, &original_class).into(),
            },
        ),
        _ => (),
    }
    let mut added_liskov_note = false;
    if !match_.bool() {
        let db = i_s.db;
        let mut emitted = false;
        // Mypy helps the user a bit by formatting different error messages for similar
        // signatures. Try to make this as similar as possible to Mypy.
        match override_func_infos(override_t, &original_t) {
            Some(OverrideFuncInfos::CallablesSameParamLen(got_c, expected_c)) => {
                let supertype = original_class_name(db, &original_class);

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
                                from.file.add_issue(
                                    i_s,
                                    Issue {
                                        kind: issue,
                                        start_position: s.start,
                                        end_position: s.end,
                                    },
                                );
                            }
                            _ => from.add_issue(i_s, issue),
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
                        func.add_issue_for_declaration(i_s, issue)
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
                                from.add_issue(
                                    i_s,
                                    IssueKind::OverloadOrderMustMatchSupertype {
                                        name: name.into(),
                                        base_class: original_class_name(db, &original_class).into(),
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
                        base_class: original_class_name(i_s.db, &original_class).into(),
                    },
                )
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
                            ClassLookupOptions::new(&|_| todo!()).with_ignore_self(),
                        )
                        .lookup,
                );
            }
            notes.push("     Subclass:".into());
            try_pretty_format(
                &mut notes,
                &i_s.with_class_context(&override_class),
                override_t,
                override_class.simple_lookup(i_s, |_| (), name),
            );

            if op_method_wider_note {
                notes.push(
                    "Overloaded operator methods can't have wider argument types in overrides"
                        .into(),
                )
            }

            let issue = IssueKind::SignatureIncompatibleWithSupertype {
                name: name.into(),
                base_class: original_class_name(i_s.db, &original_class).into(),
                notes: notes.into(),
            };
            if let Some(func) = maybe_func() {
                func.add_issue_for_declaration(i_s, issue)
            } else {
                from.add_issue(i_s, issue)
            }
        }
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
    t1: &'t1 Type,
    t2: &'t2 Type,
) -> Option<OverrideFuncInfos<'t1, 't2>> {
    match (t1, t2) {
        (Type::Callable(c1), Type::Callable(c2)) => Some(match (&c1.params, &c2.params) {
            (CallableParams::Simple(p1), CallableParams::Simple(p2)) if p1.len() == p2.len() => {
                OverrideFuncInfos::CallablesSameParamLen(c1, c2)
            }
            _ => OverrideFuncInfos::Mixed,
        }),
        (Type::FunctionOverload(o1), Type::FunctionOverload(o2)) => {
            Some(OverrideFuncInfos::BothOverloads(o1, o2))
        }
        _ => (t1.is_func_or_overload() || t2.is_func_or_overload())
            .then_some(OverrideFuncInfos::Mixed),
    }
}

fn operator_domain_is_widened(
    i_s: &InferenceState,
    override_overload: &FunctionOverload,
    original: &Type,
) -> bool {
    override_overload.iter_functions().any(|overload_func| {
        let widens_callable = |original: &Rc<CallableContent>| {
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
            _ => unreachable!(),
        }
    })
}

fn check_protocol_type_var_variances(i_s: &InferenceState, class: Class) {
    for (i, tv_like) in class.type_vars(i_s).iter().enumerate() {
        let TypeVarLike::TypeVar(tv) = tv_like else {
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
        if tv.variance != expected_variance {
            NodeRef::new(class.node_ref.file, class.node().name().index()).add_issue(
                i_s,
                IssueKind::ProtocolWrongVariance {
                    type_var_name: tv.name(i_s.db).into(),
                    actual_variance: tv.variance,
                    expected_variance,
                },
            )
        }
    }
}

pub fn check_multiple_inheritance<'x, BASES: Iterator<Item = TypeOrClass<'x>>>(
    i_s: &InferenceState,
    bases: impl Fn() -> BASES,
    should_check: impl Fn(&str) -> bool,
    mut add_issue: impl FnMut(IssueKind),
) {
    let db = i_s.db;
    for (i, base1) in bases().enumerate() {
        let cls1 = match base1 {
            TypeOrClass::Class(c) => c,
            TypeOrClass::Type(t) => {
                debug!("TODO check complex base types");
                continue;
            }
        };
        for (type_var_like, arg) in cls1
            .use_cached_type_vars(db)
            .iter()
            .zip(cls1.type_var_remap.map(|g| g.iter()).unwrap_or([].iter()))
        {
            if let GenericItem::TypeArg(Type::TypeVar(tv)) = arg {
                if let TypeVarLike::TypeVar(tv_def) = type_var_like {
                    if tv.type_var.variance != Variance::Invariant
                        && tv.type_var.variance != tv_def.variance
                    {
                        add_issue(IssueKind::TypeVarVarianceIncompatibleWithParentType {
                            type_var_name: tv.type_var.name(db).into(),
                        });
                    }
                }
            }
        }
        let instance1 = Instance::new(cls1, None);
        for base2 in bases().skip(i + 1) {
            let instance2 = match base2 {
                TypeOrClass::Class(c) => Instance::new(c, None),
                TypeOrClass::Type(t) => continue,
            };
            instance1.run_on_symbols(|name| {
                if let Some(inner) = name.strip_prefix("__") {
                    if let Some(inner) = inner.strip_suffix("__") {
                        if IGNORED_INHERITANCE_NAMES.contains(&name) {
                            return;
                        }
                    } else {
                        // This is a private name
                        return;
                    }
                }
                let had_lookup_issue = Cell::new(false);
                let inst2_lookup = instance2.lookup(
                    i_s,
                    name,
                    // Everything can inherit from object and it should therefore be fine to ignore
                    // it.
                    InstanceLookupOptions::new(&|_| had_lookup_issue.set(true)).without_object(),
                );
                if had_lookup_issue.get() {
                    /*
                    add_issue(IssueKind::MultipleInheritanceIncompatibility {
                        name: name.into(),
                        class1: base1.name(db).into(),
                        class2: base2.name(db).into(),
                    });
                    return;
                    */
                    todo!()
                }
                if let Some(inf) = inst2_lookup.lookup.into_maybe_inferred() {
                    if !should_check(name) {
                        return;
                    }
                    let second = inf.as_cow_type(i_s);
                    let first = instance1
                        .lookup(
                            i_s,
                            name,
                            InstanceLookupOptions::new(&|_| had_lookup_issue.set(true)),
                        )
                        .lookup
                        .into_inferred();
                    if had_lookup_issue.get() {
                        todo!()
                    }
                    let first = first.as_cow_type(i_s);
                    if !first
                        .is_sub_type_of(
                            i_s,
                            &mut Matcher::default().with_ignore_positional_param_names(),
                            &second,
                        )
                        .bool()
                    {
                        add_issue(IssueKind::MultipleInheritanceIncompatibility {
                            name: name.into(),
                            class1: base1.name(db).into(),
                            class2: base2.name(db).into(),
                        });
                    }
                }
            });
        }
    }
}
