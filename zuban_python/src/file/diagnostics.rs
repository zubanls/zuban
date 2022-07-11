use parsa_python_ast::*;

use crate::arguments::{Arguments, KnownArguments, NoArguments};
use crate::database::{
    ComplexPoint, DbType, GenericsList, Locality, Point, PointType, TypeVarIndex, TypeVarType,
    TypeVarUsage,
};
use crate::debug;
use crate::diagnostics::IssueType;
use crate::file::PythonInference;
use crate::generics::Generics;
use crate::inferred::Inferred;
use crate::node_ref::NodeRef;
use crate::value::{Class, Function};

impl<'db, 'a, 'b> PythonInference<'db, 'a, 'b> {
    pub fn calculate_diagnostics(&mut self) {
        self.calc_stmts_diagnostics(self.file.tree.root().iter_stmts(), None, None);
    }

    fn calc_simple_stmts_diagnostics(
        &mut self,
        simple_stmts: SimpleStmts,
        class: Option<Class<'db, '_>>,
        func: Option<&Function<'db, '_>>,
    ) {
        for simple_stmt in simple_stmts.iter() {
            match simple_stmt.unpack() {
                SimpleStmtContent::Assignment(assignment) => {
                    self.cache_assignment_nodes(assignment);
                }
                SimpleStmtContent::StarExpressions(star_exprs) => {
                    self.infer_star_expressions(star_exprs);
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
        class: Option<Class<'db, '_>>,
        func: Option<&Function<'db, '_>>,
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
                StmtContent::ForStmt(for_stmt) => {}
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
                StmtContent::WithStmt(with_stmt) => {}
                StmtContent::MatchStmt(match_stmt) => {}
                StmtContent::AsyncStmt(async_stmt) => {}
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
        class: Option<Class<'db, '_>>,
        func: Option<&Function<'db, '_>>,
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
            Class::from_position(NodeRef::new(self.file, class.index()), Generics::None, None)
                .unwrap();
        // Make sure the type vars are properly pre-calculated
        class.class_infos(self.i_s);
        self.file
            .inference(&mut self.i_s.with_diagnostic_class_context(&class))
            .calc_block_diagnostics(block, Some(class), None)
    }

    fn calc_function_diagnostics(&mut self, f: FunctionDef, class: Option<Class<'db, '_>>) {
        let function = Function::new(NodeRef::new(self.file, f.index()), class);
        // Make sure the type vars are properly pre-calculated
        function.type_vars(self.i_s);
        let (_, params, return_annotation, block) = f.unpack();
        /*
         * TODO I think this is not needed anymore
        for param in params.iter() {
            if let Some(annotation) = param.annotation() {
                self.compute_annotation(annotation);
            }
        }
        if let Some(annotation) = return_annotation {
            self.compute_return_annotation(annotation);
        }
        */

        let (i_a, a, i);
        let node_ref = NodeRef::new(self.file, f.index());
        let args: &dyn Arguments = if let Some(class) = class {
            i = Inferred::new_unsaved_complex(ComplexPoint::Instance(
                class.node_ref.as_link(),
                Some(GenericsList::new_generics(
                    class
                        .type_vars(self.i_s)
                        .iter()
                        .enumerate()
                        .map(|(i, t)| {
                            DbType::TypeVar(TypeVarUsage {
                                type_var: t.clone(),
                                index: TypeVarIndex::new(i),
                                type_: TypeVarType::Class,
                            })
                        })
                        .collect(),
                )),
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

    fn calc_return_stmt_diagnostics(
        &mut self,
        func: Option<&Function<'db, '_>>,
        return_stmt: ReturnStmt,
    ) {
        if let Some(func) = func {
            if let Some(annotation) = func.return_annotation() {
                if let Some(star_expressions) = return_stmt.star_expressions() {
                    let inf = self.infer_star_expressions(star_expressions);
                    self.use_cached_return_annotation_type(annotation)
                        .error_if_not_matches(self.i_s, None, &inf, |i_s, got, expected| {
                            NodeRef::new(self.file, return_stmt.index()).add_typing_issue(
                                i_s.db,
                                IssueType::IncompatibleReturn { got, expected },
                            );
                        });
                } else {
                    debug!("TODO what about an implicit None?");
                }
            }
        }
    }

    fn calc_try_stmt_diagnostics(
        &mut self,
        try_stmt: TryStmt,
        class: Option<Class<'db, '_>>,
        func: Option<&Function<'db, '_>>,
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
                    self.infer_star_expressions(expressions);
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
