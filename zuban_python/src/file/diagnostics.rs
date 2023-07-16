use parsa_python_ast::*;

use crate::arguments::NoArguments;
use crate::database::{
    CallableContent, ComplexPoint, Database, DbType, FunctionKind, Locality,
    OverloadImplementation, Point, PointType, Specific, TupleTypeArguments, TypeOrTypeVarTuple,
    Variance,
};
use crate::debug;
use crate::diagnostics::IssueType;
use crate::file::Inference;
use crate::getitem::SliceType;
use crate::inference_state::InferenceState;
use crate::matching::params::has_overlapping_params;
use crate::matching::{matches_params, LookupResult, Match, Matcher, ResultContext, Type};
use crate::node_ref::NodeRef;
use crate::type_helpers::{
    format_pretty_callable, is_private, Class, Function, Instance, TypeOrClass,
};

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
                        self.check_valid_raise_type(expr, false);
                        if let Some(from_expr) = from_expr {
                            self.check_valid_raise_type(from_expr, true)
                        }
                    }
                }
                SimpleStmtContent::ImportFrom(import_from) => {
                    if class.is_some() && func.is_none() {
                        NodeRef::new(self.file, simple_stmt.index())
                            .add_issue(self.i_s, IssueType::UnsupportedClassScopedImport);
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

    fn check_valid_raise_type(&mut self, expr: Expression, allow_none: bool) {
        if !valid_raise_type(
            self.i_s.db,
            self.infer_expression(expr).as_type(self.i_s),
            allow_none,
        ) {
            NodeRef::new(self.file, expr.index())
                .add_issue(self.i_s, IssueType::BaseExceptionExpectedForRaise);
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
                StmtContent::Decorated(decorated) => match decorated.decoratee() {
                    Decoratee::FunctionDef(f) => self.calc_function_diagnostics(f, class),
                    Decoratee::ClassDef(class) => {
                        for decorator in decorated.decorators().iter() {
                            self.infer_named_expression(decorator.named_expression());
                        }
                        self.calc_class_diagnostics(class)
                    }
                    Decoratee::AsyncFunctionDef(f) => todo!(),
                },
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
                StmtContent::AsyncStmt(async_stmt) => match async_stmt.unpack() {
                    AsyncStmtContent::FunctionDef(func) => {
                        self.calc_function_diagnostics(func, class)
                    }
                    AsyncStmtContent::ForStmt(_) => todo!(),
                    AsyncStmtContent::WithStmt(_) => todo!(),
                },
                StmtContent::Newline => {}
            };
            self.file
                .points
                .set(stmt.index(), Point::new_node_analysis(Locality::Todo));
        }
    }

    fn calc_untyped_block_diagnostics(&mut self, block: Block) {
        for interesting in block.search_relevant_untyped_nodes() {
            match interesting {
                RelevantUntypedNode::Primary(p) => {
                    let PrimaryOrAtom::Atom(atom) = p.first() else {
                        continue
                    };
                    let AtomContent::Name(n) = atom.unpack() else {
                        continue
                    };
                    if n.as_code() == "reveal_type" && !self.file.points.get(n.index()).calculated()
                    {
                        let PrimaryContent::Execution(_) = p.second() else {
                            continue
                        };
                        let n = NodeRef::new(self.file, p.index());
                        n.add_issue(self.i_s, IssueType::Note("Revealed type is \"Any\"".into()));
                        n.add_issue(
                            self.i_s,
                            IssueType::Note(
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
                            .add_issue(self.i_s, IssueType::AnnotationInUntypedFunction);
                    }
                }
                RelevantUntypedNode::ImportFrom(i) => self.cache_import_from(i),
                RelevantUntypedNode::ImportName(i) => self.cache_import_name(i),
            }
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
        let c = Class::with_self_generics(self.i_s.db, class_node_ref);
        let i_s = self.i_s.with_diagnostic_class_context(&c);
        let mut inference = self.file.inference(&i_s);
        inference.calc_block_diagnostics(block, Some(c), None);

        for (i, base1) in c.bases(self.i_s.db).enumerate() {
            let instance1 = match base1 {
                TypeOrClass::Class(c) => Instance::new(c, None),
                TypeOrClass::Type(t) => {
                    debug!("TODO check complex base types");
                    continue;
                }
            };
            for base2 in c.bases(self.i_s.db).skip(i + 1) {
                let instance2 = match base2 {
                    TypeOrClass::Class(c) => Instance::new(c, None),
                    TypeOrClass::Type(t) => todo!(),
                };
                instance1.run_on_symbols(|name| {
                    if name.starts_with("__") {
                        return;
                    }
                    if let Some(inf) = instance2.lookup(self.i_s, None, name).into_maybe_inferred()
                    {
                        if c.lookup_symbol(self.i_s, name).into_maybe_inferred().is_some() {
                            // These checks happen elsewhere.
                            debug!("TODO this check might omit the check between current class and c2?");
                            return
                        }
                        let second = inf.as_type(self.i_s);
                        let first = instance1.lookup(self.i_s, None, name).into_inferred();
                        let first = first.as_type(self.i_s);
                        if !first
                            .is_sub_type_of(
                                self.i_s,
                                &mut Matcher::new_class_matcher(self.i_s, c),
                                &second,
                            )
                            .bool()
                        {
                            let index =
                                c.node().arguments().unwrap().iter().nth(i).unwrap().index();
                            NodeRef::new(self.file, index).add_issue(
                                self.i_s,
                                IssueType::MultipleInheritanceIncompatibility {
                                    name: name.into(),
                                    class1: base1.name().into(),
                                    class2: base2.name().into(),
                                },
                            );
                        }
                    }
                });
            }
        }
        let instance = Instance::new(c, None);
        for table in [
            &c.class_storage.class_symbol_table,
            &c.class_storage.self_symbol_table,
        ] {
            for (name, index) in unsafe { table.iter_on_finished_table() } {
                if ["__init__", "__new__", "__init_subclass__", "__slots__"].contains(&name)
                    || is_private(name)
                {
                    continue;
                }
                let (defined_in, result) =
                    instance.lookup_and_maybe_ignore_super_count(self.i_s, None, name, 1);
                if let Some(inf) = result.into_maybe_inferred() {
                    let expected = inf.as_type(self.i_s);
                    let got = instance.lookup(self.i_s, None, name).into_inferred();
                    let got = got.as_type(self.i_s);
                    if !expected
                        .is_same_type(self.i_s, &mut Matcher::new_class_matcher(self.i_s, c), &got)
                        .bool()
                    {
                        NodeRef::new(self.file, *index).add_issue(
                            self.i_s,
                            if got.is_func_or_overload() || expected.is_func_or_overload() {
                                let mut notes = vec![];
                                notes.push("     Superclass:".into());
                                try_pretty_format(
                                    &mut notes,
                                    &self.i_s.with_class_context(&match defined_in {
                                        TypeOrClass::Class(c) => c,
                                        TypeOrClass::Type(_) => c,
                                    }),
                                    expected,
                                    c.lookup_and_class_and_maybe_ignore_self(self.i_s, name, true)
                                        .0,
                                );
                                notes.push("     Subclass:".into());
                                try_pretty_format(
                                    &mut notes,
                                    &self.i_s.with_class_context(&c),
                                    got,
                                    c.lookup(self.i_s, None, name),
                                );

                                IssueType::SignatureIncompatibleWithSupertype {
                                    name: name.into(),
                                    base_class: defined_in.name().into(),
                                    notes: notes.into(),
                                }
                            } else {
                                IssueType::IncompatibleAssignmentInSubclass {
                                    got: got.format_short(self.i_s.db),
                                    expected: expected.format_short(self.i_s.db),
                                    base_class: defined_in.name().into(),
                                }
                            },
                        )
                    }
                }
            }
        }
    }

    fn calc_function_diagnostics(&mut self, f: FunctionDef, class: Option<Class>) {
        let function = Function::new(NodeRef::new(self.file, f.index()), class);
        let decorator_ref = function.decorator_ref();
        let mut is_overload_member = false;
        let inf = function.as_inferred_from_name(self.i_s);
        if let Some(ComplexPoint::FunctionOverload(o)) = decorator_ref.complex() {
            is_overload_member = true;
            for (i, c1) in o.iter_functions().enumerate() {
                if let Some(implementation) = &o.implementation {
                    self.calc_overload_implementation_diagnostics(&c1, implementation, i + 1)
                }
                for (k, c2) in o.iter_functions().skip(i + 1).enumerate() {
                    if is_overload_unmatchable(self.i_s, &c1, &c2) {
                        NodeRef::from_link(self.i_s.db, c2.defined_at).add_issue(
                            self.i_s,
                            IssueType::OverloadUnmatchable {
                                matchable_signature_index: i + 1,
                                unmatchable_signature_index: i + k + 2,
                            },
                        );
                    } else {
                        if !Type::new(&c1.result_type)
                            .is_simple_sub_type_of(self.i_s, &Type::new(&c2.result_type))
                            .bool()
                            && has_overlapping_params(self.i_s, &c1.params, &c2.params)
                        {
                            NodeRef::from_link(self.i_s.db, c1.defined_at).add_issue(
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
        } else if function.node_ref.point().maybe_specific() == Some(Specific::DecoratedFunction)
            && decorator_ref.point().maybe_specific() == Some(Specific::OverloadUnreachable)
        {
            is_overload_member = true;
        }
        if class.is_some()
            && function.node().params().iter().next().is_none()
            && function.kind(self.i_s) != FunctionKind::Staticmethod
        {
            function
                .node_ref
                .add_issue(self.i_s, IssueType::MethodWithoutArguments)
        }

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
                                if self.file.is_stub_or_in_protocol(self.i_s)
                                    && default.is_ellipsis_literal()
                                {
                                    // In stubs it is allowed to do stuff like:
                                    // def foo(x: int = ...) -> int: ...
                                    return node_ref;
                                }
                                node_ref.add_issue(
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

        let is_dynamic = function.is_dynamic();
        if !is_dynamic || self.i_s.db.python_state.project.check_untyped_defs {
            let args = NoArguments::new(NodeRef::new(self.file, f.index()));
            let function_i_s = &mut self.i_s.with_diagnostic_func_and_args(&function, &args);
            let mut inference = self.file.inference(function_i_s);
            inference.calc_block_diagnostics(block, None, Some(&function))
        } else {
            self.calc_untyped_block_diagnostics(block)
        }
        if self.i_s.db.python_state.project.disallow_untyped_defs {
            dbg!(function);
            match (
                function.is_missing_param_annotations(self.i_s),
                function.return_annotation().is_none(),
            ) {
                (true, true) => function
                    .node_ref
                    .add_issue(self.i_s, IssueType::FunctionIsDynamic),
                (true, false) => function
                    .node_ref
                    .add_issue(self.i_s, IssueType::FunctionMissingParamAnnotations),
                (false, true) => function
                    .node_ref
                    .add_issue(self.i_s, IssueType::FunctionMissingReturnAnnotation),
                (false, false) => (),
            }
        }
    }

    fn calc_overload_implementation_diagnostics(
        &mut self,
        overload_item: &CallableContent,
        implementation: &OverloadImplementation,
        signature_index: usize,
    ) {
        let issue_node_ref = NodeRef::from_link(self.i_s.db, implementation.function_link);
        let matcher = &mut Matcher::new_reverse_callable_matcher(&implementation.callable);
        let implementation_result = &Type::new(&implementation.callable.result_type);
        let item_result = Type::new(&overload_item.result_type);
        if !item_result
            .is_sub_type_of(self.i_s, matcher, implementation_result)
            .bool()
            && !item_result
                .is_super_type_of(self.i_s, matcher, implementation_result)
                .bool()
        {
            issue_node_ref.add_issue(
                self.i_s,
                IssueType::OverloadImplementationReturnTypeIncomplete { signature_index },
            );
        }

        let match_ = matches_params(
            self.i_s,
            matcher,
            &overload_item.params,
            &implementation.callable.params,
            None,
            Variance::Contravariant,
            false,
        );
        if !match_.bool() {
            issue_node_ref.add_issue(
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
                        let node_ref = NodeRef::new(self.file, star_expressions.index());
                        node_ref.add_issue(i_s, IssueType::IncompatibleReturn { got, expected });
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
                        let inf = self.infer_expression(exception);
                        if !is_valid_except_type(self.i_s, inf.as_type(self.i_s).as_ref(), true) {
                            NodeRef::new(self.file, exception.index())
                                .add_issue(self.i_s, IssueType::BaseExceptionExpected);
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
            Target::Name(name_def) => debug!("TODO del name"),
            Target::NameExpression(primary_target, name_def) => {
                // TODO this should still be implemented
                //self.infer_single_target(target);
                let node_ref = NodeRef::new(self.file, name_def.index());
                // We do a normal lookup to check that the attribute is there.
                self.infer_primary_target_or_atom(primary_target.first())
                    .lookup_with_error(self.i_s, node_ref, name_def.as_code());
            }
            Target::IndexExpression(primary_target) => {
                let base = self.infer_primary_target_or_atom(primary_target.first());
                let PrimaryContent::GetItem(s) = primary_target.second() else {
                    unreachable!()
                };
                let slice_type = SliceType::new(self.file, primary_target.index(), s);
                let node_ref = slice_type.as_node_ref();
                base.lookup_with_error(self.i_s, node_ref, "__delitem__")
                    .into_inferred()
                    .execute(self.i_s, &slice_type.as_args(*self.i_s));
            }
            Target::Tuple(targets) => {
                for target in targets {
                    self.calc_del_stmt_diagnostics(target)
                }
            }
            Target::Starred(_) => unreachable!(),
        }
    }
}

fn valid_raise_type(db: &Database, t: Type, allow_none: bool) -> bool {
    let check = |generic_class| {
        let cls = Class::from_generic_class(db, generic_class);
        cls.incomplete_mro(db) || cls.in_mro(db, &db.python_state.base_exception())
    };
    match t.into_db_type() {
        DbType::Class(c) => check(&c),
        DbType::Type(t) => match t.as_ref() {
            DbType::Class(c) => check(c),
            _ => false,
        },
        DbType::Any => true,
        DbType::Never => todo!(),
        DbType::Union(union) => union
            .iter()
            .all(|t| valid_raise_type(db, Type::new(t), allow_none)),
        DbType::None if allow_none => true,
        _ => false,
    }
}

fn is_valid_except_type(i_s: &InferenceState, t: &DbType, allow_tuple: bool) -> bool {
    match t {
        DbType::Type(t) => {
            let db = i_s.db;
            Type::new(t.as_ref())
                .maybe_class(i_s.db)
                .is_some_and(|cls| cls.in_mro(db, &db.python_state.base_exception()))
        }
        DbType::Tuple(content) if allow_tuple => match &content.args {
            Some(TupleTypeArguments::FixedLength(ts)) => ts.iter().all(|t| match t {
                TypeOrTypeVarTuple::Type(t) => is_valid_except_type(i_s, t, false),
                TypeOrTypeVarTuple::TypeVarTuple(_) => todo!(),
            }),
            Some(TupleTypeArguments::ArbitraryLength(t)) => is_valid_except_type(i_s, t, false),
            _ => todo!(),
        },
        DbType::Union(union) => union
            .iter()
            .all(|t| is_valid_except_type(i_s, t, allow_tuple)),
        _ => false,
    }
}

fn try_pretty_format(
    notes: &mut Vec<Box<str>>,
    i_s: &InferenceState,
    t: Type,
    class_lookup_result: LookupResult,
) {
    let prefix = "         ";
    if let Some(inf) = class_lookup_result.into_maybe_inferred() {
        match inf.as_type(i_s).as_ref() {
            DbType::Callable(c) => {
                notes.push(format!("{prefix}{}", format_pretty_callable(i_s, c)).into());
                return;
            }
            DbType::FunctionOverload(overloads) => {
                for c in overloads.iter_functions() {
                    notes.push(format!("{prefix}@overload").into());
                    notes.push(format!("{prefix}{}", format_pretty_callable(i_s, c)).into());
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
    let mut matcher = Matcher::new_reverse_callable_matcher(&c1);
    let result = matches_params(
        i_s,
        &mut matcher,
        &c2.params,
        &c1.params,
        c1.type_vars.as_ref().map(|t| (t, c1.defined_at)),
        Variance::Contravariant,
        false,
    );
    matches!(result, Match::True { with_any: false })
}
