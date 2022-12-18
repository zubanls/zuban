use super::{IteratorContent, LookupResult, Value, ValueKind};
use crate::database::{
    ComplexPoint, DbType, GenericItem, GenericsList, TupleContent, TupleTypeArguments,
    TypeOrTypeVarTuple,
};
use crate::debug;
use crate::getitem::{SliceType, SliceTypeContent};
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::matching::{FormatData, ResultContext, Type};
use crate::node_ref::NodeRef;

#[derive(Debug, Clone, Copy)]
pub struct Tuple<'a> {
    db_type: &'a DbType,
    content: &'a TupleContent,
}

impl<'a> Tuple<'a> {
    pub fn new(db_type: &'a DbType, content: &'a TupleContent) -> Self {
        Self { db_type, content }
    }

    pub fn as_db_type(&self) -> DbType {
        DbType::Tuple(self.content.clone())
    }
}

impl<'db, 'a> Value<'db, 'a> for Tuple<'a> {
    fn kind(&self) -> ValueKind {
        ValueKind::Object
    }

    fn name(&self) -> &str {
        "tuple"
    }

    fn lookup_internal(&self, i_s: &mut InferenceState, name: &str) -> LookupResult {
        let tuple_cls = i_s.db.python_state.tuple();
        for (mro_index, class) in tuple_cls.mro(i_s) {
            let result = class.lookup_symbol(i_s, name).map(|inf| {
                inf.bind(
                    i_s,
                    |i_s| {
                        Inferred::new_unsaved_complex(ComplexPoint::Instance(
                            tuple_cls.node_ref.as_link(),
                            Some(GenericsList::new_generics(Box::new([
                                GenericItem::TypeArgument(match &self.content.args {
                                    Some(TupleTypeArguments::FixedLength(ts)) => {
                                        match ts.as_ref() {
                                            [] => DbType::Never,
                                            [TypeOrTypeVarTuple::Type(t)] => t.clone(),
                                            _ => i_s.db.python_state.object_db_type(),
                                        }
                                    }
                                    Some(TupleTypeArguments::ArbitraryLength(t)) => {
                                        t.as_ref().clone()
                                    }
                                    None => DbType::Any,
                                }),
                            ]))),
                        ))
                    },
                    mro_index,
                )
            });
            if !matches!(result, LookupResult::None) {
                return result;
            }
        }
        debug!("TODO tuple object lookups");
        LookupResult::None
    }

    fn iter(&self, i_s: &mut InferenceState, from: NodeRef) -> IteratorContent<'a> {
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

    fn as_type(&self, i_s: &mut InferenceState<'db, '_>) -> Type<'a> {
        Type::new(self.db_type)
    }

    fn get_item(
        &self,
        i_s: &mut InferenceState,
        slice_type: &SliceType,
        result_context: &mut ResultContext,
    ) -> Inferred {
        match slice_type.unpack() {
            SliceTypeContent::Simple(simple) => match &self.content.args {
                Some(args @ TupleTypeArguments::FixedLength(ts)) => {
                    if let Some(wanted) = simple.infer(i_s).expect_int(i_s.db) {
                        if args.has_type_var_tuple().is_some() {
                            todo!()
                        } else {
                            let index = usize::try_from(wanted).ok().unwrap_or_else(|| todo!());
                            ts.as_ref()
                                .get(index)
                                .map(|t| match t {
                                    TypeOrTypeVarTuple::Type(t) => {
                                        Inferred::execute_db_type(i_s, t.clone())
                                    }
                                    TypeOrTypeVarTuple::TypeVarTuple(t) => unreachable!(),
                                })
                                .unwrap_or_else(Inferred::new_unknown)
                        }
                    } else {
                        todo!()
                    }
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

    fn description(&self, i_s: &mut InferenceState) -> String {
        self.content.format(&FormatData::new_short(i_s.db)).into()
    }
}
