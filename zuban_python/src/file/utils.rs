use parsa_python_ast::{List, ListOrSetElementIterator, StarLikeExpression};

use crate::database::{ComplexPoint, DbType, GenericsList};
use crate::diagnostics::IssueType;
use crate::file::PythonInference;
use crate::matching::ResultContext;
use crate::node_ref::NodeRef;
use crate::Inferred;

impl PythonInference<'_, '_, '_, '_> {
    pub fn create_list_or_set_generics(&mut self, elements: ListOrSetElementIterator) -> DbType {
        let mut result = DbType::Never;
        for child in elements {
            result.union_in_place(match child {
                StarLikeExpression::NamedExpression(named_expr) => self
                    .infer_named_expression(named_expr)
                    .class_as_db_type(self.i_s),
                StarLikeExpression::StarNamedExpression(e) => self
                    .infer_expression_part(e.expression_part(), &mut ResultContext::Unknown)
                    .save_and_iter(self.i_s, NodeRef::new(self.file, e.index()))
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
        result_context: &mut ResultContext,
    ) -> Option<Inferred> {
        let file = self.file;
        result_context
            .with_type_if_exists(self.i_s, |i_s, type_| {
                let mut found = None;
                type_.on_any_class(i_s.db, &mut |list_cls| {
                    if list_cls.node_ref == i_s.db.python_state.list() {
                        let generic_t = list_cls.generics().nth(i_s, 0.into());
                        let mut new_result_context = ResultContext::Known(&generic_t);

                        // Since it's a list, now check all the entries if they match the given result
                        // generic;
                        if let Some(elements) = list.unpack() {
                            for (item, element) in elements.enumerate() {
                                let mut check_item = |i_s: &mut _, inferred, index| {
                                    let m = generic_t.error_if_not_matches(
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
                                    if m.bool() && found.is_none() {
                                        found = Some(DbType::Class(
                                            i_s.db.python_state.list().as_link(),
                                            Some(GenericsList::new_generics(Box::new([
                                                inferred.class_as_db_type(i_s)
                                            ]))),
                                        ));
                                    }
                                };
                                let mut inference = file.inference(i_s);
                                match element {
                                    StarLikeExpression::NamedExpression(e) => {
                                        let inferred = inference
                                            .infer_named_expression_with_context(
                                                e,
                                                &mut new_result_context,
                                            );
                                        check_item(i_s, inferred, e.index())
                                    }
                                    StarLikeExpression::Expression(e) => {
                                        let inferred = inference.infer_expression_with_context(
                                            e,
                                            &mut new_result_context,
                                        );
                                        check_item(i_s, inferred, e.index())
                                    }
                                    StarLikeExpression::StarNamedExpression(e) => {
                                        todo!("{e:?}")
                                    }
                                    StarLikeExpression::StarExpression(e) => {
                                        todo!("{e:?}")
                                    }
                                };
                            }
                        }
                        if found.is_none() {
                            // As a fallback if there were only errors or no items at all, just use
                            // the given and expected result context as a type.
                            found = Some(list_cls.as_db_type(i_s));
                        }
                        true
                    } else {
                        false
                    }
                });
                // `found` might still be empty, because we matched Any.
                found.map(|found| {
                    Inferred::new_unsaved_complex(ComplexPoint::TypeInstance(Box::new(found)))
                })
            })
            .flatten()
    }
}
