use super::{IteratorContent, LookupResult, Value, ValueKind};
use crate::database::{ComplexPoint, DbType, GenericsList, TupleContent};
use crate::debug;
use crate::getitem::{SliceType, SliceTypeContent};
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::matching::{FormatData, Type};
use crate::node_ref::NodeRef;

#[derive(Debug, Clone, Copy)]
pub struct Tuple<'a> {
    db_type: &'a DbType,
    content: &'a TupleContent,
}

impl<'db, 'a> Tuple<'a> {
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

    fn name(&self) -> &'db str {
        "tuple"
    }

    fn lookup_internal(&self, i_s: &mut InferenceState<'db, '_>, name: &str) -> LookupResult {
        let tuple_cls = i_s.db.python_state.tuple();
        for (mro_index, class) in tuple_cls.mro(i_s) {
            let result = class.lookup_symbol(i_s, name).map(|inf| {
                inf.bind(
                    i_s,
                    |i_s| {
                        Inferred::new_unsaved_complex(ComplexPoint::Instance(
                            tuple_cls.node_ref.as_link(),
                            Some(GenericsList::new_generics(Box::new([
                                match &self.content.generics {
                                    Some(generics) => match generics.as_slice_ref() {
                                        [] => DbType::Never,
                                        [t] => t.clone(),
                                        _ => i_s.db.python_state.object_db_type(),
                                    },
                                    None => DbType::Any,
                                },
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

    fn iter(&self, i_s: &mut InferenceState<'db, '_>, from: NodeRef) -> IteratorContent<'a> {
        if let Some(generics) = self.content.generics.as_ref() {
            if self.content.arbitrary_length {
                IteratorContent::Inferred(Inferred::execute_db_type(
                    i_s,
                    generics[0.into()].clone(),
                ))
            } else {
                match &self.content.generics {
                    Some(generics) => IteratorContent::TupleGenerics(generics.iter()),
                    None => todo!(),
                }
            }
        } else {
            todo!()
        }
    }

    fn as_type(&self, i_s: &mut InferenceState<'db, '_>) -> Type<'a, 'a> {
        Type::new(self.db_type)
    }

    fn get_item(&self, i_s: &mut InferenceState<'db, '_>, slice_type: &SliceType) -> Inferred {
        match slice_type.unpack() {
            SliceTypeContent::Simple(simple) => {
                let by_index = |i_s: &mut InferenceState<'db, '_>, index: usize| {
                    self.content
                        .generics
                        .as_ref()
                        .and_then(|generics| {
                            generics
                                .nth(index.into())
                                .map(|db_type| Inferred::execute_db_type(i_s, db_type.clone()))
                        })
                        .unwrap_or_else(Inferred::new_unknown)
                };
                if self.content.arbitrary_length {
                    by_index(i_s, 0)
                } else if let Some(wanted) = simple.infer(i_s).expect_int(i_s.db) {
                    by_index(i_s, usize::try_from(wanted).ok().unwrap_or_else(|| todo!()))
                } else {
                    todo!()
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

    fn description(&self, i_s: &mut InferenceState) -> String {
        self.content.format(&FormatData::new_short(i_s.db)).into()
    }
}
