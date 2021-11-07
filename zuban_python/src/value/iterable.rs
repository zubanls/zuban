use parsa_python_ast::{List, ListContent, ListElement, NamedExpression};

use super::{Class, Value, ValueKind};
use crate::database::{ComplexPoint, GenericPart, GenericsList};
use crate::generics::Generics;
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
            .infer_named_expression(named_expr)
    }

    fn get_list(&self) -> List<'db> {
        List::by_index(
            &self.node_reference.file.tree,
            self.node_reference.node_index,
        )
    }

    fn get_generic_part(&self, i_s: &mut InferenceState<'db, '_>) -> &'db GenericsList {
        let reference = self.node_reference.add_to_node_index(1);
        if reference.get_point().calculated() {
            match reference.get_complex().unwrap() {
                ComplexPoint::GenericClass(_, list) => list,
                _ => unreachable!(),
            }
        } else {
            let mut result = GenericPart::Unknown;
            let ptr = &mut result;
            match self.get_list().unpack() {
                ListContent::Elements(elements) => {
                    for child in elements {
                        match child {
                            ListElement::NamedExpression(named_expr) => {
                                self.infer_named_expr(i_s, named_expr)
                                    .run(i_s, &mut |i_s, v| {
                                        let cls = v.class(i_s);
                                        *ptr = std::mem::replace(ptr, GenericPart::Unknown)
                                            .union(i_s, &cls);
                                    });
                            }
                            ListElement::StarNamedExpression(_) => {
                                todo!()
                            }
                        }
                    }
                }
                ListContent::Comprehension(_) => unreachable!(),
                ListContent::None => todo!(),
            };
            reference.insert_complex(ComplexPoint::GenericClass(
                i_s.database.python_state.builtins_point_link("list"),
                GenericsList::new(Box::new([result])),
            ));
            self.get_generic_part(i_s)
        }
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

    fn class(&self, i_s: &mut InferenceState<'db, '_>) -> Class<'db, '_> {
        let node_reference = NodeReference::from_link(
            i_s.database,
            i_s.database.python_state.builtins_point_link("list"),
        );
        Class::from_position(
            node_reference,
            Generics::List(self.get_generic_part(i_s)),
            None,
        )
        .unwrap()
    }
}
