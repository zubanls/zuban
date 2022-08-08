use parsa_python_ast::{Dict, DictElement, Expression, List, NamedExpression, StarLikeExpression};

use super::{Class, Instance, IteratorContent, LookupResult, Value, ValueKind};
use crate::database::{ComplexPoint, DbType, FormatStyle, GenericsList, Locality};
use crate::debug;
use crate::getitem::{SliceType, SliceTypeContent};
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::matching::{ClassLike, Generics};
use crate::node_ref::NodeRef;

#[derive(Debug, Copy, Clone)]
pub struct ListLiteral<'db> {
    node_ref: NodeRef<'db>,
}

impl<'db> ListLiteral<'db> {
    pub fn new(node_ref: NodeRef<'db>) -> Self {
        Self { node_ref }
    }

    pub fn infer_named_expr(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        named_expr: NamedExpression<'db>,
    ) -> Inferred<'db> {
        self.node_ref
            .file
            .inference(i_s)
            .infer_named_expression(named_expr)
    }

    fn list_node(&self) -> List<'db> {
        List::by_index(&self.node_ref.file.tree, self.node_ref.node_index)
    }

    pub fn db_type(&self, i_s: &mut InferenceState<'db, '_>) -> &'db DbType {
        self.generic_list(i_s).nth(0.into()).unwrap()
    }

    fn generic_list(&self, i_s: &mut InferenceState<'db, '_>) -> &'db GenericsList {
        match self.type_instance_ref(i_s).complex().unwrap() {
            ComplexPoint::TypeInstance(t) => match t.as_ref() {
                DbType::GenericClass(_, generics) => generics,
                _ => unreachable!(),
            },
            _ => unreachable!(),
        }
    }

    fn type_instance_ref(&self, i_s: &mut InferenceState<'db, '_>) -> NodeRef<'db> {
        let reference = self.node_ref.add_to_node_index(1);
        if !reference.point().calculated() {
            let result = match self.list_node().unpack() {
                Some(elements) => self
                    .node_ref
                    .file
                    .inference(i_s)
                    .create_list_or_set_generics(elements),
                None => DbType::Any,
            };
            reference.insert_complex(
                ComplexPoint::TypeInstance(Box::new(DbType::GenericClass(
                    i_s.db.python_state.builtins_point_link("list"),
                    GenericsList::new_generics(Box::new([result])),
                ))),
                Locality::Todo,
            );
            debug!(
                "Calculated generics for {}: {}",
                self.list_node().short_debug(),
                &self.class(i_s).format(i_s, None, FormatStyle::Short),
            );
        }
        reference
    }
}

impl<'db: 'a, 'a> Value<'db, 'a> for ListLiteral<'db> {
    fn kind(&self) -> ValueKind {
        ValueKind::Object
    }

    fn name(&self) -> &'db str {
        "list"
    }

    fn lookup_internal(&self, i_s: &mut InferenceState<'db, '_>, name: &str) -> LookupResult<'db> {
        Instance::new(
            Class::from_position(
                NodeRef::from_link(i_s.db, i_s.db.python_state.builtins_point_link("list")),
                Generics::List(self.generic_list(i_s), None),
                None,
            )
            .unwrap(),
            Some(self.type_instance_ref(i_s)),
        )
        .lookup_internal(i_s, name)
    }

    fn iter(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        from: NodeRef<'db>,
    ) -> IteratorContent<'db, 'a> {
        match self.list_node().unpack() {
            Some(elements) => IteratorContent::ListLiteral(*self, elements),
            None => IteratorContent::Empty,
        }
    }

    fn get_item(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        slice_type: &SliceType<'db, '_>,
    ) -> Inferred<'db> {
        match slice_type.unpack() {
            SliceTypeContent::Simple(simple) => {
                if let Some(wanted) = simple.infer(i_s).expect_int() {
                    match self.list_node().unpack() {
                        Some(elements) => {
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
                                    StarLikeExpression::Expression(_)
                                    | StarLikeExpression::StarExpression(_) => unreachable!(),
                                }
                            }
                        }
                        None => todo!(),
                    };
                }
                match self.list_node().unpack() {
                    Some(mut elements) => {
                        let mut inferred = match elements.next().unwrap() {
                            StarLikeExpression::NamedExpression(named_expr) => {
                                self.infer_named_expr(i_s, named_expr)
                            }
                            StarLikeExpression::StarNamedExpression(_) => {
                                todo!()
                            }
                            StarLikeExpression::Expression(_)
                            | StarLikeExpression::StarExpression(_) => unreachable!(),
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
                                StarLikeExpression::Expression(_)
                                | StarLikeExpression::StarExpression(_) => unreachable!(),
                            }
                        }
                        inferred
                    }
                    None => todo!(),
                }
            }
            SliceTypeContent::Slice(simple) => {
                todo!()
            }
            SliceTypeContent::Slices(simple) => {
                todo!()
            }
        }
    }

    fn class(&self, i_s: &mut InferenceState<'db, '_>) -> ClassLike<'db, 'a> {
        let node_ref = NodeRef::from_link(i_s.db, i_s.db.python_state.builtins_point_link("list"));
        ClassLike::Class(
            Class::from_position(node_ref, Generics::new_list(self.generic_list(i_s)), None)
                .unwrap(),
        )
    }
}

#[derive(Debug)]
pub struct DictLiteral<'db> {
    node_ref: NodeRef<'db>,
}

impl<'db> DictLiteral<'db> {
    pub fn new(node_ref: NodeRef<'db>) -> Self {
        Self { node_ref }
    }

    fn infer_expr(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        expr: Expression<'db>,
    ) -> Inferred<'db> {
        self.node_ref.file.inference(i_s).infer_expression(expr)
    }

    fn dict_node(&self) -> Dict<'db> {
        Dict::by_index(&self.node_ref.file.tree, self.node_ref.node_index)
    }

    fn db_type(&self, i_s: &mut InferenceState<'db, '_>) -> &'db GenericsList {
        let reference = self.node_ref.add_to_node_index(1);
        if reference.point().calculated() {
            match reference.complex().unwrap() {
                ComplexPoint::GenericClass(_, list) => list,
                _ => unreachable!(),
            }
        } else {
            let mut keys = DbType::Unknown;
            let mut values = DbType::Unknown;
            for child in self.dict_node().iter_elements() {
                match child {
                    DictElement::KeyValue(key_value) => {
                        keys.union_in_place(
                            self.infer_expr(i_s, key_value.key()).class_as_db_type(i_s),
                        );
                        values.union_in_place(
                            self.infer_expr(i_s, key_value.value())
                                .class_as_db_type(i_s),
                        );
                    }
                    DictElement::DictStarred(_) => {
                        todo!()
                    }
                }
            }
            reference.insert_complex(
                ComplexPoint::GenericClass(
                    i_s.db.python_state.builtins_point_link("list"),
                    GenericsList::new_generics(Box::new([keys, values])),
                ),
                Locality::Todo,
            );
            debug!(
                "Calculated generics for {}: {}",
                self.dict_node().short_debug(),
                &self.class(i_s).format(i_s, None, FormatStyle::Short),
            );
            self.db_type(i_s)
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

    fn lookup_internal(&self, i_s: &mut InferenceState<'db, '_>, name: &str) -> LookupResult<'db> {
        todo!()
    }

    fn get_item(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        slice_type: &SliceType<'db, '_>,
    ) -> Inferred<'db> {
        /*
        match slice_type {
            SliceTypeContent::Simple(simple) => {
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
            SliceTypeContent::Slice(simple) => {
                todo!()
            }
            SliceTypeContent::Slices(simple) => {
                todo!()
            }
        }
        */
        todo!()
    }

    fn class(&self, i_s: &mut InferenceState<'db, '_>) -> ClassLike<'db, 'a> {
        let node_ref = NodeRef::from_link(i_s.db, i_s.db.python_state.builtins_point_link("dict"));
        ClassLike::Class(
            Class::from_position(node_ref, Generics::new_list(self.db_type(i_s)), None).unwrap(),
        )
    }
}
