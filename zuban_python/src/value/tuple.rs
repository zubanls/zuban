use super::{IteratorContent, LookupResult, Value, ValueKind};
use crate::database::{
    DbType, Literal, LiteralKind, LiteralValue, TupleContent, TupleTypeArguments,
    TypeOrTypeVarTuple,
};
use crate::debug;
use crate::getitem::{SliceType, SliceTypeContent};
use crate::inference_state::InferenceState;
use crate::inferred::{Inferred, UnionValue};
use crate::matching::{FormatData, ResultContext, Type};
use crate::node_ref::NodeRef;
use crate::value::Instance;

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

    fn lookup_internal(
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

    fn iter(&self, i_s: &InferenceState, from: NodeRef) -> IteratorContent<'a> {
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
                    let infer = |i_s: &InferenceState, literal: Literal| {
                        if !matches!(literal.kind, LiteralKind::Int(_)) {
                            return None;
                        }
                        let LiteralValue::Int(i) = literal.value(i_s.db) else {
                            unreachable!();
                        };
                        let index = usize::try_from(i).ok().unwrap_or_else(|| todo!());
                        ts.as_ref().get(index).map(|t| match t {
                            TypeOrTypeVarTuple::Type(t) => {
                                Inferred::execute_db_type(i_s, t.clone())
                            }
                            TypeOrTypeVarTuple::TypeVarTuple(t) => unreachable!(),
                        })
                    };
                    match simple
                        .infer(i_s, &mut ResultContext::ExpectLiteral)
                        .maybe_literal(i_s.db)
                    {
                        UnionValue::Single(literal) => infer(i_s, literal),
                        UnionValue::Multiple(mut literals) => literals
                            .next()
                            .and_then(|l| infer(i_s, l))
                            .and_then(|mut inferred| {
                                for literal in literals {
                                    if let Some(new_inf) = infer(i_s, literal) {
                                        inferred = inferred.union(new_inf);
                                    } else {
                                        return None;
                                    }
                                }
                                Some(inferred)
                            }),
                        UnionValue::Any => todo!(),
                    }
                    .unwrap_or_else(Inferred::new_unknown)
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

    fn description(&self, i_s: &InferenceState) -> String {
        self.content.format(&FormatData::new_short(i_s.db)).into()
    }
}
