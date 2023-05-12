use std::rc::Rc;

use super::{IteratorContent, LookupResult, Value};
use crate::database::{DbType, TupleContent, TupleTypeArguments, TypeOrTypeVarTuple};
use crate::debug;
use crate::file::infer_index;
use crate::getitem::{SliceType, SliceTypeContent};
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::matching::{ResultContext, Type};
use crate::node_ref::NodeRef;
use crate::value::Instance;

#[derive(Debug, Clone, Copy)]
pub struct Tuple<'a> {
    db_type: &'a DbType,
    content: &'a Rc<TupleContent>,
}

impl<'a> Tuple<'a> {
    pub fn new(db_type: &'a DbType, content: &'a Rc<TupleContent>) -> Self {
        Self { db_type, content }
    }

    pub fn iter(&self, i_s: &InferenceState, from: NodeRef) -> IteratorContent<'a> {
        match &self.content.args {
            Some(args @ TupleTypeArguments::FixedLength(ts)) => {
                if args.has_type_var_tuple().is_some() {
                    todo!()
                } else {
                    IteratorContent::FixedLengthTupleGenerics(ts.iter())
                }
            }
            Some(TupleTypeArguments::ArbitraryLength(t)) => {
                IteratorContent::Inferred(Inferred::execute_db_type(i_s, t.as_ref().clone()))
            }
            None => todo!(),
        }
    }

    pub fn lookup(
        &self,
        i_s: &InferenceState,
        node_ref: Option<NodeRef>,
        name: &str,
    ) -> LookupResult {
        let tuple_cls = i_s.db.python_state.tuple_class(i_s.db, self.content);
        let tuple_instance = Instance::new(tuple_cls, None);
        for (mro_index, class) in tuple_cls.mro(i_s.db) {
            let result = class.lookup_symbol(i_s, name).and_then(|inf| {
                inf.bind_instance_descriptors(
                    i_s,
                    &tuple_instance,
                    class.maybe_class(i_s.db).unwrap(),
                    |i_s| tuple_instance.as_inferred(i_s),
                    node_ref,
                    mro_index,
                )
            });
            match result {
                Some(LookupResult::None) => (),
                None => return LookupResult::None,
                Some(x) => return x,
            }
        }
        debug!("TODO tuple object lookups");
        LookupResult::None
    }
}

impl<'db, 'a> Value<'db, 'a> for Tuple<'a> {
    fn name(&self) -> &str {
        "tuple"
    }

    fn as_type(&self, i_s: &InferenceState<'db, '_>) -> Type<'a> {
        Type::new(self.db_type)
    }

    fn get_item(
        &self,
        i_s: &InferenceState,
        slice_type: &SliceType,
        result_context: &mut ResultContext,
    ) -> Inferred {
        match slice_type.unpack() {
            SliceTypeContent::Simple(simple) => match &self.content.args {
                Some(args @ TupleTypeArguments::FixedLength(ts)) => {
                    if args.has_type_var_tuple().is_some() {
                        todo!()
                    }
                    infer_index(i_s, simple, |index| {
                        ts.as_ref().get(index).map(|t| match t {
                            TypeOrTypeVarTuple::Type(t) => {
                                Inferred::execute_db_type(i_s, t.clone())
                            }
                            TypeOrTypeVarTuple::TypeVarTuple(t) => unreachable!(),
                        })
                    })
                }
                Some(TupleTypeArguments::ArbitraryLength(t)) => {
                    Inferred::execute_db_type(i_s, t.as_ref().clone())
                }
                _ => Inferred::new_unknown(),
            },
            SliceTypeContent::Slice(simple) => {
                todo!()
            }
            SliceTypeContent::Slices(simple) => {
                todo!()
            }
        }
    }
}
