use super::class::MroIterator;
use super::{IteratorContent, LookupResult, Value, ValueKind};
use crate::base_description;
use crate::database::{ComplexPoint, DbType, FormatStyle, GenericsList, TupleContent, Variance};
use crate::debug;
use crate::getitem::{SliceType, SliceTypeContent};
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::matching::{ClassLike, Generics, Type, TypeVarMatcher};
use crate::node_ref::NodeRef;

#[derive(Debug, Clone, Copy)]
pub struct Tuple<'a> {
    content: &'a TupleContent,
}

impl<'db, 'a> Tuple<'a> {
    pub fn new(content: &'a TupleContent) -> Self {
        Self { content }
    }

    pub fn mro(&self, i_s: &mut InferenceState<'db, '_>) -> MroIterator<'db, 'a> {
        let class_infos = i_s.db.python_state.tuple().class_infos(i_s);
        if !self.content.arbitrary_length {
            debug!("TODO Only used TypeVarIndex #0 for tuple, and not all of them");
        }
        MroIterator::new(
            i_s.db,
            ClassLike::Tuple(*self),
            Some(Generics::DbType(
                self.content
                    .generics
                    .as_ref()
                    .map(|g| g.nth(0.into()).unwrap_or(&DbType::Never))
                    .unwrap_or(&DbType::Any),
            )),
            class_infos.mro.iter(),
        )
    }

    pub fn matches(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        other: &Tuple,
        mut matcher: Option<&mut TypeVarMatcher<'db, '_>>,
        variance: Variance,
    ) -> bool {
        if let Some(generics1) = &self.content.generics {
            if let Some(generics2) = &other.content.generics {
                return match (
                    self.content.arbitrary_length,
                    other.content.arbitrary_length,
                    variance,
                ) {
                    (false, false, _) | (true, true, _) => {
                        generics1.len() == generics2.len()
                            && Generics::new_list(generics1)
                                .matches(
                                    i_s,
                                    matcher,
                                    Generics::new_list(generics2),
                                    variance,
                                    None,
                                )
                                .bool()
                    }
                    (false, true, Variance::Covariant)
                    | (true, false, Variance::Contravariant)
                    | (_, _, Variance::Invariant) => false,
                    (true, false, Variance::Covariant) => {
                        let t1 = Type::from_db_type(i_s.db, &generics1[0.into()]);
                        generics2.iter().all(|g2| {
                            let t2 = Type::from_db_type(i_s.db, g2);
                            t1.matches(i_s, matcher.as_deref_mut(), &t2, variance)
                                .bool()
                        })
                    }
                    (false, true, Variance::Contravariant) => {
                        let t2 = Type::from_db_type(i_s.db, &generics2[0.into()]);
                        generics1.iter().all(|g1| {
                            let t1 = Type::from_db_type(i_s.db, g1);
                            t1.matches(i_s, matcher.as_deref_mut(), &t2, variance)
                                .bool()
                        })
                    }
                };
            }
        }
        true
    }

    pub fn overlaps(&self, i_s: &mut InferenceState<'db, '_>, other: &Self) -> bool {
        if let Some(generics1) = &self.content.generics {
            if let Some(generics2) = &other.content.generics {
                return match (
                    self.content.arbitrary_length,
                    other.content.arbitrary_length,
                ) {
                    (false, false) | (true, true) => {
                        generics1.len() == generics2.len()
                            && Generics::new_list(generics1).overlaps(
                                i_s,
                                Generics::new_list(generics2),
                                None,
                            )
                    }
                    (false, true) => {
                        let t2 = Type::from_db_type(i_s.db, &generics2[0.into()]);
                        for g in generics1.iter() {
                            let t1 = Type::from_db_type(i_s.db, g);
                            if !t1.overlaps(i_s, &t2) {
                                dbg!();
                                return false;
                            }
                        }
                        true
                    }
                    (true, false) => {
                        let t1 = Type::from_db_type(i_s.db, &generics1[0.into()]);
                        for g in generics2.iter() {
                            let t2 = Type::from_db_type(i_s.db, g);
                            if !t1.overlaps(i_s, &t2) {
                                return false;
                            }
                        }
                        true
                    }
                };
            }
        }
        true
    }

    pub fn as_db_type(&self) -> DbType {
        DbType::Tuple(self.content.clone())
    }

    pub fn format(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        matcher: Option<&TypeVarMatcher<'db, '_>>,
        style: FormatStyle,
    ) -> Box<str> {
        self.content.format(i_s, matcher, style)
    }
}

impl<'db, 'a> Value<'db, 'a> for Tuple<'a> {
    fn kind(&self) -> ValueKind {
        ValueKind::Object
    }

    fn name(&self) -> &'db str {
        "tuple"
    }

    fn lookup_internal(&self, i_s: &mut InferenceState<'db, '_>, name: &str) -> LookupResult<'db> {
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

    fn iter(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        from: NodeRef<'db>,
    ) -> IteratorContent<'db, 'a> {
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

    fn class(&self, i_s: &mut InferenceState<'db, '_>) -> ClassLike<'db, 'a> {
        ClassLike::Tuple(*self)
    }

    fn get_item(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        slice_type: &SliceType<'db, '_>,
    ) -> Inferred<'db> {
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
                } else if let Some(wanted) = simple.infer(i_s).expect_int() {
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
        base_description!(self) + &self.content.format(i_s, None, FormatStyle::Short)
    }
}
