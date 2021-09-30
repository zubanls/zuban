use parsa_python::{NonterminalType, PyNode, PyNodeType::Nonterminal};

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
        node: PyNode<'db>,
    ) -> Inferred<'db> {
        self.node_reference
            .file
            .get_inference(i_s)
            .infer_named_expression(node)
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
                let n = self.node_reference.node.get_nth_child(1);
                if let Some(wanted) = simple.infer(i_s).expect_int() {
                    for (i, child) in n.iter_children().step_by(2).enumerate() {
                        if child.is_type(Nonterminal(NonterminalType::named_expression)) {
                            if i as i64 == wanted {
                                return self.infer_named_expr(i_s, child);
                            }
                        } else {
                            debug_assert_eq!(
                                child.get_type(),
                                Nonterminal(NonterminalType::star_named_expression)
                            );
                            // It gets quite complicated to figure out the index here, so just stop
                            // for now.
                            break;
                        }
                    }
                }
                let mut iterator = n.iter_children().step_by(2);
                if let Some(first_node) = iterator.next() {
                    let mut inferred =
                        if first_node.is_type(Nonterminal(NonterminalType::named_expression)) {
                            self.infer_named_expr(i_s, first_node)
                        } else {
                            todo!()
                        };
                    for child in iterator {
                        if child.is_type(Nonterminal(NonterminalType::named_expression)) {
                            inferred = inferred.union(self.infer_named_expr(i_s, child));
                        } else {
                            todo!()
                        }
                    }
                    inferred
                } else {
                    todo!()
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
