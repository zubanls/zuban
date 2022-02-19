use parsa_python_ast::*;

use crate::arguments::{Arguments, InstanceArguments, NoArguments};
use crate::database::{ComplexPoint, Locality, Point, PointType};
use crate::diagnostics::IssueType;
use crate::file::PythonInference;
use crate::generics::Generics;
use crate::inferred::Inferred;
use crate::node_ref::NodeRef;
use crate::value::{Class, Function, Instance};

impl<'db, 'a, 'b> PythonInference<'db, 'a, 'b> {
    pub fn calculate_diagnostics(&mut self) {
        self.calc_stmts_diagnostics(self.file.tree.root().iter_stmts(), None, None);
    }

    fn calc_stmts_diagnostics(
        &mut self,
        stmts: StmtIterator<'db>,
        class: Option<&Class<'db, '_>>,
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
                    for simple_stmt in simple_stmts.iter() {
                        match simple_stmt.unpack() {
                            SimpleStmtContent::Assignment(assignment) => {
                                self.cache_assignment_nodes(assignment);
                            }
                            SimpleStmtContent::StarExpressions(star_exprs) => {
                                let inf = self.infer_star_expressions(star_exprs);
                                inf.as_generic_option(self.i_s);
                            }
                            SimpleStmtContent::ReturnStmt(return_stmt) => {
                                self.calc_return_stmt_diagnostics(func, return_stmt)
                            }
                            SimpleStmtContent::YieldExpr(x) => {}
                            SimpleStmtContent::RaiseStmt(x) => {}
                            SimpleStmtContent::ImportFrom(import_from) => {
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
                            SimpleStmtContent::DelStmt(x) => {}
                        }
                    }
                }
                StmtContent::FunctionDef(f) => self.calc_function_diagnostics(f, class),
                StmtContent::ClassDef(class) => self.calc_class_diagnostics(class),
                StmtContent::Decorated(decorated) => {}
                StmtContent::IfStmt(if_stmt) => {
                    for block in if_stmt.iter_blocks() {
                        match block {
                            IfBlockType::If(_, block) => {
                                self.calc_block_diagnostics(block, class, func)
                            }
                            IfBlockType::Else(block) => {
                                self.calc_block_diagnostics(block, class, func)
                            }
                        }
                    }
                }
                StmtContent::ForStmt(for_stmt) => {}
                StmtContent::TryStmt(try_stmt) => {}
                StmtContent::WhileStmt(while_stmt) => {}
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
        block: Block<'db>,
        class: Option<&Class<'db, '_>>,
        func: Option<&Function<'db, '_>>,
    ) {
        match block.unpack() {
            BlockContent::Indented(stmts) => self.calc_stmts_diagnostics(stmts, class, func),
            BlockContent::OneLine(simple_stmts) => {}
        }
    }

    fn calc_class_diagnostics(&mut self, class: ClassDef<'db>) {
        let (_, block) = class.unpack();
        let class =
            Class::from_position(NodeRef::new(self.file, class.index()), Generics::None, None)
                .unwrap();
        self.calc_block_diagnostics(block, Some(&class), None)
    }

    fn calc_function_diagnostics(&mut self, f: FunctionDef<'db>, class: Option<&Class<'db, '_>>) {
        let (_, params, return_annotation, block) = f.unpack();
        for param in params.iter() {
            if let Some(annotation) = param.annotation() {
                self.infer_annotation_expression(annotation.expression());
            }
        }
        let function = Function::new(NodeRef::new(self.file, f.index()), class);

        let i_a;
        let i;
        let inst;
        let node_ref = NodeRef::new(self.file, f.index());
        let a = NoArguments::new(node_ref);
        let args: &dyn Arguments = if let Some(class) = class {
            i = Inferred::new_unsaved_complex(ComplexPoint::Instance(
                class.reference.as_link(),
                None,
            ));
            inst = Instance::new(*class, &i);
            i_a = InstanceArguments::new(&inst, &a);
            &i_a
        } else {
            &a
        };
        let function_i_s = &mut self.i_s.with_func_and_args(&function, args);
        let mut inference = self.file.inference(function_i_s);
        inference.calc_block_diagnostics(block, None, Some(&function))
    }

    fn calc_return_stmt_diagnostics(
        &mut self,
        func: Option<&Function<'db, '_>>,
        return_stmt: ReturnStmt<'db>,
    ) {
        if let Some(func) = func {
            if let Some(expr) = func.return_annotation() {
                let inf = self.infer_star_expressions(return_stmt.star_expressions());
                let inf_annot = self.infer_annotation_expression_class(expr);
                inf_annot.as_generic_option(self.i_s).error_if_not_matches(
                    self.i_s,
                    &inf,
                    |t1, t2| {
                        NodeRef::new(self.file, return_stmt.index()).add_typing_issue(
                            self.i_s.database,
                            IssueType::IncompatibleReturn(t1, t2),
                        );
                    },
                );
            }
        } else {
            todo!()
        }
    }
}
