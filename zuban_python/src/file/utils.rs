use parsa_python_ast::{List, ListOrSetElementIterator, StarLikeExpression};

use crate::database::{ComplexPoint, DbType};
use crate::diagnostics::IssueType;
use crate::file::PythonInference;
use crate::matching::{ClassLike, ResultContext, Type};
use crate::node_ref::NodeRef;
use crate::Inferred;

impl<'db, 'a, 'b> PythonInference<'db, 'a, 'b> {
    pub fn create_list_or_set_generics(&mut self, elements: ListOrSetElementIterator) -> DbType {
        let mut result = DbType::Unknown;
        for child in elements {
            result.union_in_place(match child {
                StarLikeExpression::NamedExpression(named_expr) => self
                    .infer_named_expression(named_expr)
                    .class_as_db_type(self.i_s),
                StarLikeExpression::StarNamedExpression(e) => self
                    .infer_expression_part(e.expression_part(), ResultContext::Unknown)
                    .iter(self.i_s, NodeRef::new(self.file, e.index()))
                    .infer_all(self.i_s)
                    .class_as_db_type(self.i_s),
                StarLikeExpression::Expression(_) | StarLikeExpression::StarExpression(_) => {
                    unreachable!()
                }
            });
        }
        result
    }

    pub fn infer_list_literal_from_context(
        &mut self,
        list: List,
        result_context: ResultContext<'db, '_>,
    ) -> Option<Inferred<'db>> {
        let file = self.file;
        result_context
            .with_type_if_exists(self.i_s, |i_s, type_| {
                let mut found = None;
                let maybe = type_.any(i_s.db, &mut |t| match t {
                    ClassLike::Class(list_cls)
                        if list_cls.node_ref == i_s.db.python_state.list() =>
                    {
                        let generic_t = list_cls.generics().nth(i_s, 0.into());
                        let generic_t = Type::from_db_type(i_s.db, &generic_t);
                        let new_result_context = ResultContext::Known(&generic_t);

                        // Since it's a list, now check all the entries if they match the given result
                        // generic;
                        if let Some(elements) = list.unpack() {
                            for (item, element) in elements.enumerate() {
                                let check_item = |i_s, inferred, index| {
                                    generic_t.error_if_not_matches(
                                        i_s,
                                        &inferred,
                                        |i_s, got, expected| {
                                            NodeRef::new(file, index).add_typing_issue(
                                                i_s.db,
                                                IssueType::ListItemMismatch {
                                                    item,
                                                    got,
                                                    expected,
                                                },
                                            );
                                        },
                                    );
                                };
                                let mut inference = file.inference(i_s);
                                match element {
                                    StarLikeExpression::NamedExpression(e) => {
                                        let inferred = inference
                                            .infer_named_expression_with_context(
                                                e,
                                                new_result_context,
                                            );
                                        check_item(i_s, inferred, e.index())
                                    }
                                    StarLikeExpression::Expression(e) => {
                                        let inferred = inference
                                            .infer_expression_with_context(e, new_result_context);
                                        check_item(i_s, inferred, e.index())
                                    }
                                    StarLikeExpression::StarNamedExpression(e) => {
                                        todo!()
                                    }
                                    StarLikeExpression::StarExpression(e) => {
                                        todo!()
                                    }
                                };
                            }
                        }

                        found = Some(t.as_db_type(i_s));
                        true
                    }
                    _ => false,
                });
                // `found` might still be empty, because we matched Any.
                found.filter(|_| maybe).map(|found| {
                    Inferred::new_unsaved_complex(ComplexPoint::TypeInstance(Box::new(found)))
                })
            })
            .flatten()
    }
}
