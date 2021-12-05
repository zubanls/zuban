use parsa_python_ast::{
    Dict, DictElement, Expression, List, ListContent, ListElement, NamedExpression,
};

use super::{Class, ClassLike, Value, ValueKind};
use crate::database::{ComplexPoint, GenericPart, GenericsList};
use crate::debug;
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
            .inference(i_s)
            .infer_named_expression(named_expr)
    }

    fn list_node(&self) -> List<'db> {
        List::by_index(
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
            let mut result = GenericPart::Unknown;
            match self.list_node().unpack() {
                ListContent::Elements(elements) => {
                    for child in elements {
                        match child {
                            ListElement::NamedExpression(named_expr) => {
                                self.infer_named_expr(i_s, named_expr).run(
                                    i_s,
                                    &mut |i_s, v| {
                                        result =
                                            std::mem::replace(&mut result, GenericPart::Unknown)
                                                .union(v.as_generic_part(i_s));
                                    },
                                    || todo!(),
                                );
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
            debug!(
                "Calculated generics for {}: {}",
                self.list_node().short_debug(),
                &self.class(i_s).as_string(i_s),
            );
            self.generic_part(i_s)
        }
    }
}

impl<'db> Value<'db> for ListLiteral<'db, '_> {
    fn kind(&self) -> ValueKind {
        ValueKind::Object
    }

    fn name(&self) -> &'db str {
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
                    match self.list_node().unpack() {
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
                match self.list_node().unpack() {
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

    fn class(&self, i_s: &mut InferenceState<'db, '_>) -> ClassLike<'db, '_> {
        let node_reference = NodeReference::from_link(
            i_s.database,
            i_s.database.python_state.builtins_point_link("list"),
        );
        ClassLike::Class(
            Class::from_position(node_reference, Generics::List(self.generic_part(i_s)), None)
                .unwrap(),
        )
    }
}

#[derive(Debug)]
pub struct DictLiteral<'db, 'a> {
    node_reference: &'a NodeReference<'db>,
}

impl<'db, 'a> DictLiteral<'db, 'a> {
    pub fn new(node_reference: &'a NodeReference<'db>) -> Self {
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
                        self.infer_expr(i_s, key_value.key()).run(
                            i_s,
                            &mut |i_s, v| {
                                keys = std::mem::replace(&mut keys, GenericPart::Unknown)
                                    .union(v.as_generic_part(i_s));
                            },
                            || todo!(),
                        );
                        self.infer_expr(i_s, key_value.value()).run(
                            i_s,
                            &mut |i_s, v| {
                                values = std::mem::replace(&mut values, GenericPart::Unknown)
                                    .union(v.as_generic_part(i_s));
                            },
                            || todo!(),
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

impl<'db> Value<'db> for DictLiteral<'db, '_> {
    fn kind(&self) -> ValueKind {
        ValueKind::Object
    }

    fn name(&self) -> &'db str {
        "dict"
    }

    fn lookup(&self, i_s: &mut InferenceState<'db, '_>, name: &str) -> Inferred<'db> {
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

    fn class(&self, i_s: &mut InferenceState<'db, '_>) -> ClassLike<'db, '_> {
        let node_reference = NodeReference::from_link(
            i_s.database,
            i_s.database.python_state.builtins_point_link("dict"),
        );
        ClassLike::Class(
            Class::from_position(node_reference, Generics::List(self.generic_part(i_s)), None)
                .unwrap(),
        )
    }
}
