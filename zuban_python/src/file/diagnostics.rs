use parsa_python_ast::*;

use crate::arguments::NoArguments;
use crate::database::{
    CallableParams, ComplexPoint, Database, DbType, Locality, Point, PointType, Specific, Variance,
};
use crate::debug;
use crate::diagnostics::IssueType;
use crate::file::Inference;
use crate::matching::{
    matches_simple_params, overload_has_overlapping_params, Generics, Match, Matcher, Param,
    ResultContext, Type,
};
use crate::node_ref::NodeRef;
use crate::type_helpers::{Class, Function};

impl<'db> Inference<'db, '_, '_> {
    pub fn calculate_diagnostics(&mut self) {
        self.calc_stmts_diagnostics(self.file.tree.root().iter_stmts(), None, None);
        for complex_point in unsafe { self.file.complex_points.iter() } {
            if let ComplexPoint::NewTypeDefinition(n) = complex_point {
                // Make sure types are calculated and the errors are generated.
                n.type_(self.i_s);
            }
        }
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
                SimpleStmtContent::RaiseStmt(raise_stmt) => {
                    if let Some((expr, from_expr)) = raise_stmt.unpack() {
                        if !valid_raise_type(
                            self.i_s.db,
                            self.infer_expression(expr).as_type(self.i_s),
                        ) {
                            NodeRef::new(self.file, expr.index()).add_typing_issue(
                                self.i_s,
                                IssueType::BaseExceptionExpectedForRaise,
                            );
                        }
                    }
                }
                SimpleStmtContent::ImportFrom(import_from) => {
                    if class.is_some() && func.is_none() {
                        NodeRef::new(self.file, simple_stmt.index())
                            .add_typing_issue(self.i_s, IssueType::UnsupportedClassScopedImport);
                    }
                    self.cache_import_from(import_from);
                }
                SimpleStmtContent::ImportName(import_name) => {
                    self.cache_import_name(import_name);
                }
                SimpleStmtContent::PassStmt(x) => {}
                SimpleStmtContent::GlobalStmt(x) => {}
                SimpleStmtContent::NonlocalStmt(x) => {}
                SimpleStmtContent::AssertStmt(assert_stmt) => {
                    let (expr, message_expr) = assert_stmt.unpack();
                    self.infer_expression(expr);
                    if let Some(message_expr) = message_expr {
                        self.infer_expression(message_expr);
                    }
                }
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

    pub fn calc_block_diagnostics(
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
        let name_def = NodeRef::new(self.file, class.name_definition().index());
        self.cache_class(name_def, class);
        let class_node_ref = NodeRef::new(self.file, class.index());
        let type_var_likes =
            Class::from_position(class_node_ref, Generics::NotDefinedYet, None).type_vars(self.i_s);
        let c = Class::from_position(
            class_node_ref,
            Generics::Self_ {
                class_definition: class_node_ref.as_link(),
                type_var_likes,
            },
            None,
        );
        self.file
            .inference(&self.i_s.with_diagnostic_class_context(&c))
            .calc_block_diagnostics(block, Some(c), None)
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
                    .add_typing_issue(self.i_s, IssueType::OverloadSingleNotAllowed);
            } else if o.implementing_function.is_none() && !self.file.is_stub(self.i_s.db) {
                name_def_node_ref
                    .add_typing_issue(self.i_s, IssueType::OverloadImplementationNeeded);
            }
            if o.implementing_function.is_some() && self.file.is_stub(self.i_s.db) {
                name_def_node_ref
                    .add_typing_issue(self.i_s, IssueType::OverloadStubImplementationNotAllowed);
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
                                    let mut matcher = Matcher::new_reverse_callable_matcher(
                                        callable_content,
                                        0, // TODO are there really no type vars?
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
                            let type_ = implementation.decorated(self.i_s).format_short(self.i_s);
                            implementation
                                .node_ref
                                .add_typing_issue(self.i_s, IssueType::NotCallable { type_ });
                            // Avoid multiple reports
                            maybe_implementation = None;
                        }
                    } else {
                        let impl_type_vars = implementation.type_vars(self.i_s);
                        let mut matcher = Matcher::new_reverse_function_matcher(
                            class.as_ref(),
                            *implementation,
                            impl_type_vars,
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
                    let mut matcher =
                        Matcher::new_reverse_function_matcher(class.as_ref(), f1, f1_type_vars);
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
                            self.i_s,
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
                                self.i_s,
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
                                    i_s,
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

        let args = NoArguments::new(NodeRef::new(self.file, f.index()));
        let function_i_s = &mut self.i_s.with_diagnostic_func_and_args(&function, &args);
        let mut inference = self.file.inference(function_i_s);
        inference.calc_block_diagnostics(block, None, Some(&function))
    }

    fn calc_overload_implementation_diagnostics<'x, P1: Param<'x>>(
        &mut self,
        name_def_node_ref: NodeRef,
        overload_item: Function<'x, 'x>,
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
                self.i_s,
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
                self.i_s,
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
                        node_ref
                            .add_typing_issue(i_s, IssueType::IncompatibleReturn { got, expected });
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
        debug!("For loop input: {}", element.format_short(self.i_s));
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
                                class
                                    .in_mro(self.i_s.db, &self.i_s.db.python_state.base_exception())
                            })
                            .unwrap_or(false)
                        {
                            NodeRef::new(self.file, exception.index())
                                .add_typing_issue(self.i_s, IssueType::BaseExceptionExpected);
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

fn valid_raise_type(db: &Database, t: Type) -> bool {
    let check = |link, generics| {
        let cls = Class::from_db_type(db, link, generics);
        cls.incomplete_mro(db) || cls.in_mro(db, &db.python_state.base_exception())
    };
    match t.into_db_type(db) {
        DbType::Class(link, generics) => check(link, &generics),
        DbType::Type(t) => match t.as_ref() {
            DbType::Class(link, generics) => check(*link, generics),
            _ => return false,
        },
        DbType::Any => true,
        DbType::Never => todo!(),
        DbType::Union(union) => union.iter().all(|t| valid_raise_type(db, Type::new(t))),
        _ => false,
    }
}
