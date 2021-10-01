use parsa_python_ast::{List, ListContent, ListElement, NamedExpression};

use super::{Value, ValueKind};
use crate::getitem::SliceType;
use crate::inference_state::InferenceState;
use crate::inferred::{Inferred, NodeReference};

#[derive(Debug)]
pub struct ListLiteral<'db, 'a> {
    node_reference: &'a NodeReference<'db>,
}

impl<'db, 'a> ListLiteral<'db, 'a> {
    pub fn new(node_reference: &'a NodeReference<'db>) -> Self {
        Self { node_reference }
    }

    fn infer_named_expr(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        named_expr: NamedExpression<'db>,
    ) -> Inferred<'db> {
        self.node_reference
            .file
            .get_inference(i_s)
            .infer_named_expression(named_expr.0)
    }

    fn get_list(&self) -> List<'db> {
        List::by_index(
            &self.node_reference.file.tree,
            self.node_reference.node_index,
        )
    }
}

impl<'db> Value<'db> for ListLiteral<'db, '_> {
    fn get_kind(&self) -> ValueKind {
        ValueKind::Object
    }

    fn get_name(&self) -> &'db str {
        "list"
    }

    fn lookup(&self, i_s: &mut InferenceState<'db, '_>, name: &str) -> Inferred<'db> {
        todo!()
    }

    fn get_item(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        slice_type: &SliceType<'db>,
    ) -> Inferred<'db> {
        match slice_type {
            SliceType::Simple(simple) => {
                if let Some(wanted) = simple.infer(i_s).expect_int() {
                    match self.get_list().unpack() {
                        ListContent::Elements(elements) => {
                            for (i, child) in elements.enumerate() {
                                match child {
                                    ListElement::NamedExpression(named_expr) => {
                                        if i as i64 == wanted {
                                            return self.infer_named_expr(i_s, named_expr);
                                        }
                                    }
                                    ListElement::StarNamedExpression(_) => {
                                        // It gets quite complicated to figure out the index here,
                                        // so just stop for now.
                                        break;
                                    }
                                }
                            }
                        }
                        ListContent::Comprehension(_) => unreachable!(),
                        ListContent::None => todo!(),
                    };
                }
                match self.get_list().unpack() {
                    ListContent::Elements(mut elements) => {
                        let mut inferred = match elements.next().unwrap() {
                            ListElement::NamedExpression(named_expr) => {
                                self.infer_named_expr(i_s, named_expr)
                            }
                            ListElement::StarNamedExpression(_) => {
                                todo!()
                            }
                        };
                        for child in elements {
                            match child {
                                ListElement::NamedExpression(named_expr) => {
                                    inferred =
                                        inferred.union(self.infer_named_expr(i_s, named_expr));
                                }
                                ListElement::StarNamedExpression(_) => {
                                    todo!()
                                }
                            }
                        }
                        inferred
                    }
                    ListContent::Comprehension(_) => unreachable!(),
                    ListContent::None => todo!(),
                }
            }
            SliceType::Slice(simple) => {
                todo!()
            }
            SliceType::Slices(simple) => {
                todo!()
            }
        }
    }
}
