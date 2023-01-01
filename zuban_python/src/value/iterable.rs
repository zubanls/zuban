use parsa_python_ast::{
    Dict, DictElement, Expression, List, ListOrSetElementIterator, NamedExpression,
    StarLikeExpression,
};

use super::{Class, Instance, IteratorContent, LookupResult, Value, ValueKind};
use crate::database::{ComplexPoint, DbType, GenericItem, GenericsList, Locality};
use crate::debug;
use crate::getitem::{SliceType, SliceTypeContent};
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::matching::{FormatData, Generics, ResultContext, Type};
use crate::node_ref::NodeRef;

#[derive(Debug, Copy, Clone)]
pub struct ListLiteral<'a> {
    node_ref: NodeRef<'a>,
}

impl<'a> ListLiteral<'a> {
    pub fn new(node_ref: NodeRef<'a>) -> Self {
        Self { node_ref }
    }

    pub fn infer_named_expr(
        &self,
        i_s: &mut InferenceState,
        named_expr: NamedExpression,
    ) -> Inferred {
        self.node_ref
            .file
            .inference(i_s)
            .infer_named_expression(named_expr)
    }

    fn list_node(&self) -> List<'a> {
        List::by_index(&self.node_ref.file.tree, self.node_ref.node_index)
    }

    pub fn db_type(&self, i_s: &mut InferenceState) -> &'a DbType {
        match &self.generic_list(i_s)[0.into()] {
            GenericItem::TypeArgument(t) => t,
            _ => unreachable!(),
        }
    }

    fn generic_list(&self, i_s: &mut InferenceState) -> &'a GenericsList {
        match self.type_instance_ref(i_s).complex().unwrap() {
            ComplexPoint::TypeInstance(t) => match t.as_ref() {
                DbType::Class(_, Some(generics)) => generics,
                _ => unreachable!(),
            },
            _ => unreachable!(),
        }
    }

    fn type_instance_ref(&self, i_s: &mut InferenceState) -> NodeRef<'a> {
        let reference = self.node_ref.add_to_node_index(1);
        if !reference.point().calculated() {
            let result = match self.list_node().unpack() {
                Some(elements) => self
                    .node_ref
                    .file
                    .inference(i_s)
                    .create_list_or_set_generics(elements),
                None => GenericItem::TypeArgument(DbType::Any), // TODO shouldn't this be Never?
            };
            reference.insert_complex(
                ComplexPoint::TypeInstance(Box::new(DbType::Class(
                    i_s.db.python_state.builtins_point_link("list"),
                    Some(GenericsList::new_generics(Box::new([result]))),
                ))),
                Locality::Todo,
            );
            debug!(
                "Calculated generics for {}: {}",
                self.list_node().short_debug(),
                &self.as_type(i_s).format(&FormatData::new_short(i_s.db)),
            );
        }
        reference
    }
}

impl<'db: 'a, 'a> Value<'db, 'a> for ListLiteral<'a> {
    fn kind(&self) -> ValueKind {
        ValueKind::Object
    }

    fn name(&self) -> &str {
        "list"
    }

    fn lookup_internal(&self, i_s: &mut InferenceState, name: &str) -> LookupResult {
        Instance::new(
            Class::from_position(
                NodeRef::from_link(i_s.db, i_s.db.python_state.builtins_point_link("list")),
                Generics::List(self.generic_list(i_s), None),
                None,
            ),
            Some(self.type_instance_ref(i_s)),
        )
        .lookup_internal(i_s, name)
    }

    fn iter(&self, i_s: &mut InferenceState<'db, '_>, from: NodeRef) -> IteratorContent<'a> {
        match self.list_node().unpack() {
            Some(elements) => IteratorContent::ListLiteral(*self, elements),
            // TODO shouldn't this be IteratorContent::Empty, ???
            None => IteratorContent::ListLiteral(
                *self,
                ListOrSetElementIterator::new_empty(&self.node_ref.file.tree),
            ),
        }
    }

    fn get_item(
        &self,
        i_s: &mut InferenceState,
        slice_type: &SliceType,
        result_context: &mut ResultContext,
    ) -> Inferred {
        match slice_type.unpack() {
            SliceTypeContent::Simple(simple) => {
                if let Some(wanted) = simple.infer(i_s).expect_int(i_s.db) {
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

    fn as_type(&self, i_s: &mut InferenceState<'db, '_>) -> Type<'a> {
        let node_ref = NodeRef::from_link(i_s.db, i_s.db.python_state.builtins_point_link("list"));
        Type::Class(Class::from_position(
            node_ref,
            Generics::new_list(self.generic_list(i_s)),
            None,
        ))
    }
}

#[derive(Debug)]
pub struct DictLiteral<'a> {
    node_ref: NodeRef<'a>,
}

impl<'a> DictLiteral<'a> {
    pub fn new(node_ref: NodeRef<'a>) -> Self {
        Self { node_ref }
    }

    fn infer_expr(&self, i_s: &mut InferenceState, expr: Expression) -> Inferred {
        self.node_ref.file.inference(i_s).infer_expression(expr)
    }

    fn dict_node(&self) -> Dict<'a> {
        Dict::by_index(&self.node_ref.file.tree, self.node_ref.node_index)
    }

    fn db_type(&self, i_s: &mut InferenceState) -> &'a GenericsList {
        let reference = self.node_ref.add_to_node_index(1);
        if reference.point().calculated() {
            match reference.complex().unwrap() {
                ComplexPoint::GenericClass(_, list) => list,
                _ => unreachable!(),
            }
        } else {
            let mut keys: Option<DbType> = None;
            let mut values: Option<DbType> = None;
            for child in self.dict_node().iter_elements() {
                match child {
                    DictElement::KeyValue(key_value) => {
                        let key_t = self.infer_expr(i_s, key_value.key()).class_as_db_type(i_s);
                        match keys.as_mut() {
                            Some(keys) => keys.union_in_place(key_t),
                            None => keys = Some(key_t),
                        };
                        let key_t = self
                            .infer_expr(i_s, key_value.value())
                            .class_as_db_type(i_s);
                        match values.as_mut() {
                            Some(values) => values.union_in_place(key_t),
                            None => values = Some(key_t),
                        };
                    }
                    DictElement::DictStarred(_) => {
                        todo!()
                    }
                }
            }
            reference.insert_complex(
                ComplexPoint::GenericClass(
                    i_s.db.python_state.builtins_point_link("list"),
                    GenericsList::new_generics(Box::new([
                        GenericItem::TypeArgument(keys.unwrap_or(DbType::Any)),
                        GenericItem::TypeArgument(values.unwrap_or(DbType::Any)),
                    ])),
                ),
                Locality::Todo,
            );
            debug!(
                "Calculated generics for {}: {}",
                self.dict_node().short_debug(),
                &self.as_type(i_s).format(&FormatData::new_short(i_s.db)),
            );
            self.db_type(i_s)
        }
    }
}

impl<'db: 'a, 'a> Value<'db, 'a> for DictLiteral<'a> {
    fn kind(&self) -> ValueKind {
        ValueKind::Object
    }

    fn name(&self) -> &'a str {
        "dict"
    }

    fn lookup_internal(&self, i_s: &mut InferenceState, name: &str) -> LookupResult {
        todo!()
    }

    fn get_item(
        &self,
        i_s: &mut InferenceState,
        slice_type: &SliceType,
        _: &mut ResultContext,
    ) -> Inferred {
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

    fn as_type(&self, i_s: &mut InferenceState<'db, '_>) -> Type<'a> {
        let node_ref = NodeRef::from_link(i_s.db, i_s.db.python_state.builtins_point_link("dict"));
        Type::Class(Class::from_position(
            node_ref,
            Generics::new_list(self.db_type(i_s)),
            None,
        ))
    }
}
