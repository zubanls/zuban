use parsa_python_ast::{
    Dict, DictElement, Expression, List, ListContent, NamedExpression, StarLikeExpression,
};

use super::{Class, ClassLike, IteratorContent, Value, ValueKind};
use crate::database::{ComplexPoint, GenericPart, GenericsList, TypeVarIndex};
use crate::debug;
use crate::generics::Generics;
use crate::getitem::SliceType;
use crate::inference_state::InferenceState;
use crate::inferred::{Inferred, NodeRef};

#[derive(Debug, Copy, Clone)]
pub struct ListLiteral<'db> {
    node_reference: NodeRef<'db>,
}

impl<'db> ListLiteral<'db> {
    pub fn new(node_reference: NodeRef<'db>) -> Self {
        Self { node_reference }
    }

    pub fn infer_named_expr(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        named_expr: NamedExpression<'db>,
    ) -> Inferred<'db> {
        self.node_reference
            .file
            .inference(i_s)
            .infer_named_expression(named_expr)
    }

    fn list_node(&self) -> List<'db> {
        List::by_index(
            &self.node_reference.file.tree,
            self.node_reference.node_index,
        )
    }

    pub fn generic_part(&self, i_s: &mut InferenceState<'db, '_>) -> &'db GenericPart {
        self.generic_list(i_s).nth(TypeVarIndex::new(0)).unwrap()
    }

    fn generic_list(&self, i_s: &mut InferenceState<'db, '_>) -> &'db GenericsList {
        let reference = self.node_reference.add_to_node_index(1);
        if reference.point().calculated() {
            match reference.complex().unwrap() {
                ComplexPoint::GenericClass(_, list) => list,
                _ => unreachable!(),
            }
        } else {
            let mut result = GenericPart::Unknown;
            match self.list_node().unpack() {
                ListContent::Elements(elements) => {
                    for child in elements {
                        result.union_in_place(match child {
                            StarLikeExpression::NamedExpression(named_expr) => self
                                .infer_named_expr(i_s, named_expr)
                                .as_class_generic_part(i_s),
                            StarLikeExpression::StarNamedExpression(_) => {
                                todo!()
                            }
                        });
                    }
                }
                ListContent::Comprehension(_) => unreachable!(),
                ListContent::None => todo!(),
            };
            reference.insert_complex(ComplexPoint::GenericClass(
                i_s.database.python_state.builtins_point_link("list"),
                GenericsList::new(Box::new([result])),
            ));
            debug!(
                "Calculated generics for {}: {}",
                self.list_node().short_debug(),
                &self.class(i_s).as_string(i_s),
            );
            self.generic_list(i_s)
        }
    }
}

impl<'db: 'a, 'a> Value<'db, 'a> for ListLiteral<'db> {
    fn kind(&self) -> ValueKind {
        ValueKind::Object
    }

    fn name(&self) -> &'db str {
        "list"
    }

    fn lookup_internal(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        name: &str,
    ) -> Option<Inferred<'db>> {
        todo!()
    }

    fn iter(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        from: NodeRef<'db>,
    ) -> IteratorContent<'db, 'a> {
        match self.list_node().unpack() {
            ListContent::Elements(elements) => IteratorContent::ListLiteral(*self, elements),
            ListContent::Comprehension(_) => unreachable!(),
            ListContent::None => IteratorContent::Empty,
        }
    }

    fn get_item(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        slice_type: &SliceType<'db>,
    ) -> Inferred<'db> {
        match slice_type {
            SliceType::Simple(simple) => {
                if let Some(wanted) = simple.infer(i_s).expect_int() {
                    match self.list_node().unpack() {
                        ListContent::Elements(elements) => {
                            for (i, child) in elements.enumerate() {
                                match child {
                                    StarLikeExpression::NamedExpression(named_expr) => {
                                        if i as i64 == wanted {
                                            return self.infer_named_expr(i_s, named_expr);
                                        }
                                    }
                                    StarLikeExpression::StarNamedExpression(_) => {
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
                match self.list_node().unpack() {
                    ListContent::Elements(mut elements) => {
                        let mut inferred = match elements.next().unwrap() {
                            StarLikeExpression::NamedExpression(named_expr) => {
                                self.infer_named_expr(i_s, named_expr)
                            }
                            StarLikeExpression::StarNamedExpression(_) => {
                                todo!()
                            }
                        };
                        for child in elements {
                            match child {
                                StarLikeExpression::NamedExpression(named_expr) => {
                                    inferred =
                                        inferred.union(self.infer_named_expr(i_s, named_expr));
                                }
                                StarLikeExpression::StarNamedExpression(_) => {
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

    fn class(&self, i_s: &mut InferenceState<'db, '_>) -> ClassLike<'db, 'a> {
        let node_reference = NodeRef::from_link(
            i_s.database,
            i_s.database.python_state.builtins_point_link("list"),
        );
        ClassLike::Class(
            Class::from_position(
                node_reference,
                Generics::new_list(self.generic_list(i_s)),
                None,
            )
            .unwrap(),
        )
    }
}

#[derive(Debug)]
pub struct DictLiteral<'db> {
    node_reference: NodeRef<'db>,
}

impl<'db> DictLiteral<'db> {
    pub fn new(node_reference: NodeRef<'db>) -> Self {
        Self { node_reference }
    }

    fn infer_expr(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        expr: Expression<'db>,
    ) -> Inferred<'db> {
        self.node_reference
            .file
            .inference(i_s)
            .infer_expression(expr)
    }

    fn dict_node(&self) -> Dict<'db> {
        Dict::by_index(
            &self.node_reference.file.tree,
            self.node_reference.node_index,
        )
    }

    fn generic_part(&self, i_s: &mut InferenceState<'db, '_>) -> &'db GenericsList {
        let reference = self.node_reference.add_to_node_index(1);
        if reference.point().calculated() {
            match reference.complex().unwrap() {
                ComplexPoint::GenericClass(_, list) => list,
                _ => unreachable!(),
            }
        } else {
            let mut keys = GenericPart::Unknown;
            let mut values = GenericPart::Unknown;
            for child in self.dict_node().iter_elements() {
                match child {
                    DictElement::KeyValue(key_value) => {
                        keys.union_in_place(
                            self.infer_expr(i_s, key_value.key())
                                .as_class_generic_part(i_s),
                        );
                        values.union_in_place(
                            self.infer_expr(i_s, key_value.value())
                                .as_class_generic_part(i_s),
                        );
                    }
                    DictElement::DictStarred(_) => {
                        todo!()
                    }
                }
            }
            reference.insert_complex(ComplexPoint::GenericClass(
                i_s.database.python_state.builtins_point_link("list"),
                GenericsList::new(Box::new([keys, values])),
            ));
            debug!(
                "Calculated generics for {}: {}",
                self.dict_node().short_debug(),
                &self.class(i_s).as_string(i_s),
            );
            self.generic_part(i_s)
        }
    }
}

impl<'db: 'a, 'a> Value<'db, 'a> for DictLiteral<'db> {
    fn kind(&self) -> ValueKind {
        ValueKind::Object
    }

    fn name(&self) -> &'db str {
        "dict"
    }

    fn lookup_internal(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        name: &str,
    ) -> Option<Inferred<'db>> {
        todo!()
    }

    fn get_item(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        slice_type: &SliceType<'db>,
    ) -> Inferred<'db> {
        /*
        match slice_type {
            SliceType::Simple(simple) => {
                if let Some(wanted) = simple.infer(i_s).expect_int() {
                    for child in self.dict_node().iter_elements() {
                        match child {
                            DictElement::KeyValue(named_expr) => {
                                if i as i64 == wanted {
                                    return self.infer_expr(i_s, named_expr);
                                }
                            }
                            DictElement::DictStarred(_) => {
                                // It gets quite complicated to figure out the index here,
                                // so just stop for now.
                                break;
                            }
                        }
                    }
                }
                let elements = self.dict_node().iter_elements();
                let mut inferred = None;
                for child in elements {
                    match child {
                        DictElement::KeyValue(key_value) => {
                            let new_inferred = self.infer_expr(i_s, key_value);
                            if let Some(current) = inferred {
                                inferred = Some(current.union(new_inferred));
                            } else {
                                inferred = Some(new_inferred);
                            }
                        }
                        DictElement::DictStarred(_) => {
                            todo!()
                        }
                    }
                }
                inferred.unwrap_or_else(|| todo!())
            }
            SliceType::Slice(simple) => {
                todo!()
            }
            SliceType::Slices(simple) => {
                todo!()
            }
        }
        */
        todo!()
    }

    fn class(&self, i_s: &mut InferenceState<'db, '_>) -> ClassLike<'db, 'a> {
        let node_reference = NodeRef::from_link(
            i_s.database,
            i_s.database.python_state.builtins_point_link("dict"),
        );
        ClassLike::Class(
            Class::from_position(
                node_reference,
                Generics::new_list(self.generic_part(i_s)),
                None,
            )
            .unwrap(),
        )
    }
}
