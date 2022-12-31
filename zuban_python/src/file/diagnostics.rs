use parsa_python_ast::*;

use crate::arguments::{Arguments, KnownArguments, NoArguments};
use crate::database::{
    CallableParams, ComplexPoint, DbType, GenericItem, GenericsList, Locality, ParamSpecArgument,
    ParamSpecUsage, Point, PointType, Specific, TypeArguments, TypeOrTypeVarTuple, TypeVarLike,
    TypeVarTupleUsage, TypeVarUsage, Variance,
};
use crate::debug;
use crate::diagnostics::IssueType;
use crate::file::Inference;
use crate::inferred::Inferred;
use crate::matching::{
    matches_simple_params, overload_has_overlapping_params, FormatData, Generics, Match, Matcher,
    Param, ResultContext, Type,
};
use crate::node_ref::NodeRef;
use crate::value::{Class, Function};

impl<'db> Inference<'db, '_, '_, '_> {
    pub fn calculate_diagnostics(&mut self) {
        self.calc_stmts_diagnostics(self.file.tree.root().iter_stmts(), None, None);
    }

    fn calc_simple_stmts_diagnostics(
        &mut self,
        simple_stmts: SimpleStmts,
        class: Option<Class>,
        func: Option<&Function>,
    ) {
        for simple_stmt in simple_stmts.iter() {
            match simple_stmt.unpack() {
                SimpleStmtContent::Assignment(assignment) => {
                    self.cache_assignment_nodes(assignment);
                }
                SimpleStmtContent::StarExpressions(star_exprs) => {
                    self.infer_star_expressions(star_exprs, &mut ResultContext::Unknown);
                }
                SimpleStmtContent::ReturnStmt(return_stmt) => {
                    self.calc_return_stmt_diagnostics(func, return_stmt)
                }
                SimpleStmtContent::YieldExpr(x) => {}
                SimpleStmtContent::RaiseStmt(x) => {}
                SimpleStmtContent::ImportFrom(import_from) => {
                    if class.is_some() && func.is_none() {
                        NodeRef::new(self.file, simple_stmt.index())
                            .add_typing_issue(self.i_s.db, IssueType::UnsupportedClassScopedImport);
                    }
                    self.cache_import_from(import_from);
                }
                SimpleStmtContent::ImportName(import_name) => {
                    self.cache_import_name(import_name);
                }
                SimpleStmtContent::PassStmt(x) => {}
                SimpleStmtContent::GlobalStmt(x) => {}
                SimpleStmtContent::NonlocalStmt(x) => {}
                SimpleStmtContent::AssertStmt(x) => {}
                SimpleStmtContent::BreakStmt(x) => {}
                SimpleStmtContent::ContinueStmt(x) => {}
                SimpleStmtContent::DelStmt(d) => {
                    self.calc_del_stmt_diagnostics(d.target());
                }
            }
        }
    }

    fn calc_stmts_diagnostics(
        &mut self,
        stmts: StmtIterator,
        class: Option<Class>,
        func: Option<&Function>,
    ) {
        // TODO In general all {} blocks are todos
        for stmt in stmts {
            let point = self.file.points.get(stmt.index());
            if point.calculated() {
                debug_assert_eq!(point.type_(), PointType::NodeAnalysis);
                continue;
            }

            match stmt.unpack() {
                StmtContent::SimpleStmts(simple_stmts) => {
                    self.calc_simple_stmts_diagnostics(simple_stmts, class, func)
                }
                StmtContent::FunctionDef(f) => self.calc_function_diagnostics(f, class),
                StmtContent::ClassDef(class) => self.calc_class_diagnostics(class),
                StmtContent::Decorated(decorated) => {
                    for decorator in decorated.decorators().iter() {
                        self.infer_named_expression(decorator.named_expression());
                    }
                    match decorated.decoratee() {
                        Decoratee::FunctionDef(f) => self.calc_function_diagnostics(f, class),
                        Decoratee::ClassDef(class) => self.calc_class_diagnostics(class),
                        Decoratee::AsyncFunctionDef(f) => todo!(),
                    }
                }
                StmtContent::IfStmt(if_stmt) => {
                    for block in if_stmt.iter_blocks() {
                        match block {
                            IfBlockType::If(if_expr, block) => {
                                self.infer_named_expression(if_expr);
                                self.calc_block_diagnostics(block, class, func)
                            }
                            IfBlockType::Else(block) => {
                                self.calc_block_diagnostics(block, class, func)
                            }
                        }
                    }
                }
                StmtContent::ForStmt(for_stmt) => {
                    self.calc_for_stmt_diagnostics(for_stmt, class, func)
                }
                StmtContent::TryStmt(try_stmt) => {
                    self.calc_try_stmt_diagnostics(try_stmt, class, func)
                }
                StmtContent::WhileStmt(while_stmt) => {
                    let (condition, block, else_block) = while_stmt.unpack();
                    self.infer_named_expression(condition);
                    self.calc_block_diagnostics(block, class, func);
                    if let Some(else_block) = else_block {
                        self.calc_block_diagnostics(else_block.block(), class, func)
                    }
                }
                StmtContent::WithStmt(with_stmt) => {
                    let (with_items, block) = with_stmt.unpack();
                    for with_item in with_items.iter() {
                        let (expr, target) = with_item.unpack();
                        let result = self.infer_expression(expr);
                        if let Some(target) = target {
                            self.assign_targets(
                                target,
                                result,
                                NodeRef::new(self.file, expr.index()),
                                true,
                            )
                        }
                    }
                    self.calc_block_diagnostics(block, class, func);
                }
                StmtContent::MatchStmt(match_stmt) => {
                    todo!()
                }
                StmtContent::AsyncStmt(async_stmt) => {
                    todo!()
                }
                StmtContent::Newline => {}
            };
            self.file
                .points
                .set(stmt.index(), Point::new_node_analysis(Locality::Todo));
        }
    }

    fn calc_block_diagnostics(
        &mut self,
        block: Block,
        class: Option<Class>,
        func: Option<&Function>,
    ) {
        match block.unpack() {
            BlockContent::Indented(stmts) => self.calc_stmts_diagnostics(stmts, class, func),
            BlockContent::OneLine(simple_stmts) => {
                self.calc_simple_stmts_diagnostics(simple_stmts, class, func)
            }
        }
    }

    fn calc_class_diagnostics(&mut self, class: ClassDef) {
        let (_, block) = class.unpack();
        let class =
            Class::from_position(NodeRef::new(self.file, class.index()), Generics::Any, None)
                .unwrap();
        // Make sure the type vars are properly pre-calculated
        class.class_infos(self.i_s);
        self.file
            .inference(&mut self.i_s.with_diagnostic_class_context(&class))
            .calc_block_diagnostics(block, Some(class), None)
    }

    fn calc_function_diagnostics(&mut self, f: FunctionDef, class: Option<Class>) {
        let name_def_node_ref = NodeRef::new(self.file, f.name_definition().index());
        if name_def_node_ref.point().maybe_specific() == Some(Specific::LazyInferredFunction) {
            self.check_point_cache(f.name_definition().index());
        }
        let mut is_overload_member = false;
        if let Some(ComplexPoint::FunctionOverload(o)) = name_def_node_ref.complex() {
            is_overload_member = o.implementing_function.is_none();
            if o.functions.len() < 2 {
                NodeRef::from_link(self.i_s.db, o.functions[0])
                    .add_typing_issue(self.i_s.db, IssueType::OverloadSingleNotAllowed);
            } else if o.implementing_function.is_none() && !self.file.is_stub(self.i_s.db) {
                name_def_node_ref
                    .add_typing_issue(self.i_s.db, IssueType::OverloadImplementationNeeded);
            }
            if o.implementing_function.is_some() && self.file.is_stub(self.i_s.db) {
                name_def_node_ref
                    .add_typing_issue(self.i_s.db, IssueType::OverloadStubImplementationNotAllowed);
            }
            let mut maybe_implementation = None;
            let mut implementation_callable_content = None;
            let decorated;
            if let Some(i) = o.implementing_function {
                let imp = Function::new(NodeRef::from_link(self.i_s.db, i), class);
                imp.type_vars(self.i_s);
                if !self.i_s.db.python_state.project.mypy_compatible
                    || imp.return_annotation().is_some()
                {
                    maybe_implementation = Some(imp);
                }
                if o.implementing_function_has_decorators {
                    decorated = imp.decorated(self.i_s);
                    implementation_callable_content = decorated.maybe_callable(self.i_s, true);
                    maybe_implementation = Some(imp);
                }
            }
            for (i, link1) in o.functions.iter().enumerate() {
                let f1 = Function::new(NodeRef::from_link(self.i_s.db, *link1), class);
                let f1_type_vars = f1.type_vars(self.i_s);
                if let Some(ref implementation) = maybe_implementation {
                    if o.implementing_function_has_decorators {
                        if let Some(callable_content) = &implementation_callable_content {
                            match &callable_content.params {
                                CallableParams::Simple(ps) => {
                                    let mut calculated_type_vars = vec![];
                                    let mut matcher = Matcher::new_reverse_callable_matcher(
                                        callable_content,
                                        &mut calculated_type_vars,
                                    );
                                    self.calc_overload_implementation_diagnostics(
                                        name_def_node_ref,
                                        f1,
                                        &mut matcher,
                                        ps.iter(),
                                        &Type::new(&callable_content.result_type),
                                        i + 1,
                                    )
                                }
                                CallableParams::Any => (),
                                CallableParams::WithParamSpec(_, _) => todo!(),
                            }
                        } else {
                            implementation.node_ref.add_typing_issue(
                                self.i_s.db,
                                IssueType::NotCallable {
                                    type_: implementation
                                        .decorated(self.i_s)
                                        .format(self.i_s, &FormatData::new_short(self.i_s.db)),
                                },
                            );
                            // Avoid multiple reports
                            maybe_implementation = None;
                        }
                    } else {
                        let impl_type_vars = implementation.type_vars(self.i_s);
                        let mut calculated_type_vars = vec![];
                        let mut matcher = Matcher::new_reverse_function_matcher(
                            *implementation,
                            impl_type_vars,
                            &mut calculated_type_vars,
                        );
                        let result_type = implementation.result_type(self.i_s);
                        self.calc_overload_implementation_diagnostics(
                            name_def_node_ref,
                            f1,
                            &mut matcher,
                            implementation.iter_params(),
                            &result_type,
                            i + 1,
                        )
                    };
                }
                for (k, link2) in o.functions[i + 1..].iter().enumerate() {
                    let f2 = Function::new(NodeRef::from_link(self.i_s.db, *link2), class);
                    let f2_type_vars = f2.type_vars(self.i_s);
                    let mut calculated_type_vars = vec![];
                    let mut matcher = Matcher::new_reverse_function_matcher(
                        f1,
                        f1_type_vars,
                        &mut calculated_type_vars,
                    );
                    if matches!(
                        matches_simple_params(
                            self.i_s,
                            &mut matcher,
                            f2.iter_params(),
                            f1.iter_params(),
                            Variance::Contravariant
                        ),
                        Match::True { with_any: false }
                    ) {
                        f2.node_ref.add_typing_issue(
                            self.i_s.db,
                            IssueType::OverloadUnmatchable {
                                matchable_signature_index: i + 1,
                                unmatchable_signature_index: i + k + 2,
                            },
                        );
                    } else {
                        let f2_result_type = f2.result_type(self.i_s);
                        if !f1
                            .result_type(self.i_s)
                            .is_simple_sub_type_of(self.i_s, &f2_result_type)
                            .bool()
                            && overload_has_overlapping_params(
                                self.i_s,
                                f1.iter_params(),
                                f2.iter_params(),
                            )
                        {
                            f1.node_ref.add_typing_issue(
                                self.i_s.db,
                                IssueType::OverloadIncompatibleReturnTypes {
                                    first_signature_index: i + 1,
                                    second_signature_index: i + k + 2,
                                },
                            );
                        }
                    }
                }
            }
        } else if name_def_node_ref.point().maybe_specific() == Some(Specific::OverloadUnreachable)
        {
            is_overload_member = true;
        }
        let function = Function::new(NodeRef::new(self.file, f.index()), class);
        // Make sure the type vars are properly pre-calculated
        function.type_vars(self.i_s);
        let (_, params, return_annotation, block) = f.unpack();
        if !is_overload_member {
            // Check defaults here.
            for param in params.iter() {
                if let Some(annotation) = param.annotation() {
                    if let Some(default) = param.default() {
                        let inf = self.infer_expression(default);
                        self.use_cached_annotation_type(annotation)
                            .error_if_not_matches(self.i_s, &inf, |i_s, got, expected| {
                                let node_ref =
                                    NodeRef::new(self.file, default.index()).to_db_lifetime(i_s.db);
                                if self.file.is_stub(self.i_s.db) && default.is_ellipsis_literal() {
                                    // In stubs it is allowed to do stuff like:
                                    // def foo(x: int = ...) -> int: ...
                                    return node_ref;
                                }
                                node_ref.add_typing_issue(
                                    i_s.db,
                                    IssueType::IncompatibleDefaultArgument {
                                        argument_name: Box::from(param.name_definition().as_code()),
                                        got,
                                        expected,
                                    },
                                );
                                node_ref
                            });
                    }
                }
            }
        }

        let (i_a, a, i);
        let node_ref = NodeRef::new(self.file, f.index());
        let args: &dyn Arguments = if let Some(class) = class {
            // TODO performancewise I don't like at all that this allocates
            i = Inferred::new_unsaved_complex(ComplexPoint::Instance(
                class.node_ref.as_link(),
                class.type_vars(self.i_s).map(|type_vars| {
                    GenericsList::new_generics(
                        type_vars
                            .iter()
                            .enumerate()
                            .map(|(i, t)| match t {
                                TypeVarLike::TypeVar(type_var) => {
                                    GenericItem::TypeArgument(DbType::TypeVar(TypeVarUsage {
                                        type_var: type_var.clone(),
                                        index: i.into(),
                                        in_definition: class.node_ref.as_link(),
                                    }))
                                }
                                TypeVarLike::TypeVarTuple(type_var_tuple) => {
                                    GenericItem::TypeArguments(TypeArguments::new_fixed_length(
                                        Box::new([TypeOrTypeVarTuple::TypeVarTuple(
                                            TypeVarTupleUsage {
                                                type_var_tuple: type_var_tuple.clone(),
                                                index: i.into(),
                                                in_definition: class.node_ref.as_link(),
                                            },
                                        )]),
                                    ))
                                }
                                TypeVarLike::ParamSpec(param_spec) => {
                                    GenericItem::ParamSpecArgument(ParamSpecArgument::new(
                                        CallableParams::WithParamSpec(
                                            Box::new([]),
                                            ParamSpecUsage {
                                                param_spec: param_spec.clone(),
                                                index: i.into(),
                                                in_definition: class.node_ref.as_link(),
                                            },
                                        ),
                                        None,
                                    ))
                                }
                            })
                            .collect(),
                    )
                }),
            ));
            i_a = KnownArguments::new(&i, None);
            &i_a
        } else {
            a = NoArguments::new(node_ref);
            &a
        };
        let function_i_s = &mut self.i_s.with_diagnostic_func_and_args(&function, args);
        let mut inference = self.file.inference(function_i_s);
        inference.calc_block_diagnostics(block, None, Some(&function))
    }

    fn calc_overload_implementation_diagnostics<'x, P1: Param<'x>>(
        &mut self,
        name_def_node_ref: NodeRef,
        overload_item: Function<'x>,
        matcher: &mut Matcher,
        implementation_params: impl Iterator<Item = P1>,
        implementation_type: &Type,
        signature_index: usize,
    ) where
        'db: 'x,
    {
        let item_result_type = overload_item.result_type(self.i_s);
        if !item_result_type
            .is_sub_type_of(self.i_s, matcher, implementation_type)
            .bool()
            && !item_result_type
                .is_super_type_of(self.i_s, matcher, implementation_type)
                .bool()
        {
            name_def_node_ref.add_typing_issue(
                self.i_s.db,
                IssueType::OverloadImplementationReturnTypeIncomplete { signature_index },
            );
        }

        let match_ = matches_simple_params(
            self.i_s,
            matcher,
            overload_item.iter_params(),
            implementation_params,
            Variance::Contravariant,
        );
        if !match_.bool() {
            name_def_node_ref.add_typing_issue(
                self.i_s.db,
                IssueType::OverloadImplementationArgumentsNotBroadEnough { signature_index },
            );
        }
    }

    fn calc_return_stmt_diagnostics(&mut self, func: Option<&Function>, return_stmt: ReturnStmt) {
        if let Some(func) = func {
            if let Some(annotation) = func.return_annotation() {
                if let Some(star_expressions) = return_stmt.star_expressions() {
                    let t = self.use_cached_return_annotation_type(annotation);
                    let inf = self
                        .infer_star_expressions(star_expressions, &mut ResultContext::Known(&t));
                    t.error_if_not_matches(self.i_s, &inf, |i_s, got, expected| {
                        let node_ref = NodeRef::new(self.file, return_stmt.index());
                        node_ref.add_typing_issue(
                            i_s.db,
                            IssueType::IncompatibleReturn { got, expected },
                        );
                        node_ref.to_db_lifetime(i_s.db)
                    });
                } else {
                    debug!("TODO what about an implicit None?");
                }
            }
        }
    }

    pub fn cache_for_stmt_names(&mut self, star_targets: StarTargets, star_exprs: StarExpressions) {
        let star_targets_point = self.file.points.get(star_targets.index());
        if star_targets_point.calculated() {
            debug_assert_eq!(star_targets_point.type_(), PointType::NodeAnalysis);
            return;
        }
        let element = self
            .infer_star_expressions(star_exprs, &mut ResultContext::Unknown)
            .save_and_iter(self.i_s, NodeRef::new(self.file, star_exprs.index()))
            .infer_all(self.i_s);
        debug!("For loop input: {}", element.description(self.i_s));
        self.assign_targets(
            star_targets.as_target(),
            element,
            NodeRef::new(self.file, star_exprs.index()),
            false,
        );
        self.file.points.set(
            star_targets.index(),
            Point::new_node_analysis(Locality::Todo),
        );
    }

    fn calc_for_stmt_diagnostics(
        &mut self,
        for_stmt: ForStmt,
        class: Option<Class>,
        func: Option<&Function>,
    ) {
        let (star_targets, star_exprs, block, else_block) = for_stmt.unpack();
        self.cache_for_stmt_names(star_targets, star_exprs);
        self.calc_block_diagnostics(block, class, func);
        if let Some(else_block) = else_block {
            self.calc_block_diagnostics(else_block.block(), class, func);
        }
    }

    fn calc_try_stmt_diagnostics(
        &mut self,
        try_stmt: TryStmt,
        class: Option<Class>,
        func: Option<&Function>,
    ) {
        for b in try_stmt.iter_blocks() {
            match b {
                TryBlockType::Try(block) => self.calc_block_diagnostics(block, class, func),
                TryBlockType::Except(b) => {
                    let (exception, _name_def, block) = b.unpack();
                    if let Some(exception) = exception {
                        if !self
                            .infer_expression(exception)
                            .maybe_class(self.i_s)
                            .map(|class| {
                                class.in_mro(self.i_s, &self.i_s.db.python_state.base_exception())
                            })
                            .unwrap_or(false)
                        {
                            NodeRef::new(self.file, exception.index())
                                .add_typing_issue(self.i_s.db, IssueType::BaseExceptionExpected);
                        }
                    }
                    self.calc_block_diagnostics(block, class, func)
                }
                TryBlockType::Else(b) => self.calc_block_diagnostics(b.block(), class, func),
                TryBlockType::Finally(b) => self.calc_block_diagnostics(b.block(), class, func),
            }
        }
    }

    pub fn calc_fstring_diagnostics(&mut self, fstring: FString) {
        self.calc_fstring_content_diagnostics(fstring.iter_content())
    }

    fn calc_fstring_content_diagnostics<'x>(
        &mut self,
        iter: impl Iterator<Item = FStringContent<'x>>,
    ) {
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

    fn calc_del_stmt_diagnostics(&mut self, target: Target) {
        match target {
            Target::Name(name_def) => todo!(),
            Target::NameExpression(_, _) => {
                // TODO this should still be implemented
                //self.infer_single_target(target);
            }
            Target::IndexExpression(t) => todo!(),
            Target::Tuple(_) => todo!(),
            Target::Starred(_) => unreachable!(),
        }
    }
}
