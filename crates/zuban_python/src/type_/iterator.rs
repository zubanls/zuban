use std::sync::Arc;

use crate::{
    prelude::*,
    type_::{InferredTypeGatherer, TupleUnpack, WithUnpack},
};

#[derive(Debug, Clone)]
pub(crate) enum IteratorContent {
    Inferred(Inferred),
    // The code before makes sure that no type var tuples are passed.
    FixedLenTupleGenerics {
        entries: Arc<[Type]>,
        current_index: usize,
    },
    WithUnpack {
        unpack: WithUnpack,
        before_index: usize,
        after_index: usize,
    },
    Union(Vec<Self>),
    Any(AnyCause),
}

impl IteratorContent {
    pub fn new_tuple(entries: Arc<[Type]>) -> Self {
        Self::FixedLenTupleGenerics {
            entries,
            current_index: 0,
        }
    }

    pub fn infer_all(self, i_s: &InferenceState) -> Inferred {
        match self {
            Self::Inferred(inferred) => inferred,
            Self::FixedLenTupleGenerics {
                entries,
                current_index,
            } => Inferred::gather_simplified_union(i_s, |add| {
                for entry in entries.iter().skip(current_index) {
                    add(Inferred::from_type(entry.clone()))
                }
            }),
            Self::Union(iterators) => Inferred::gather_simplified_union(i_s, |add| {
                for iterator in iterators {
                    add(iterator.infer_all(i_s))
                }
            }),
            Self::WithUnpack {
                unpack,
                before_index,
                after_index,
            } => Inferred::gather_simplified_union(i_s, |add| match unpack.unpack {
                TupleUnpack::TypeVarTuple(_) => add(Inferred::new_object(i_s.db)),
                TupleUnpack::ArbitraryLen(t) => {
                    for entry in unpack.before.iter().skip(before_index) {
                        add(Inferred::from_type(entry.clone()))
                    }
                    add(Inferred::from_type(t));
                    for entry in unpack.before.iter().skip(after_index) {
                        add(Inferred::from_type(entry.clone()))
                    }
                }
            }),
            Self::Any(cause) => Inferred::new_any(cause),
        }
    }

    pub fn next_as_argument(&mut self, i_s: &InferenceState) -> Option<UnpackedArgument> {
        match self {
            Self::Inferred(inferred) => Some(UnpackedArgument::Normal {
                inferred: inferred.clone(),
                arbitrary_len: true,
            }),
            Self::FixedLenTupleGenerics {
                entries,
                current_index,
            } => next_fixed_length(entries, current_index).map(|inf| UnpackedArgument::Normal {
                inferred: inf,
                arbitrary_len: false,
            }),
            Self::Union(iterators) => {
                let mut gatherer = InferredTypeGatherer::default();
                let mut arbitrary_len = true;
                for iterator in iterators {
                    let i = iterator.next_as_argument(i_s)?;
                    match i {
                        UnpackedArgument::Normal {
                            inferred,
                            arbitrary_len: a,
                        } => {
                            arbitrary_len &= a;
                            gatherer.add(inferred);
                        }
                        UnpackedArgument::WithUnpack(_) => {
                            debug!("Unpacking a union with incompatible results");
                            return None;
                        }
                    }
                }
                gatherer
                    .into_inferred_if_not_never(i_s)
                    .map(|inferred| UnpackedArgument::Normal {
                        inferred,
                        arbitrary_len,
                    })
            }
            Self::WithUnpack {
                unpack,
                before_index,
                after_index,
            } => {
                debug_assert_eq!(*after_index, 0);
                let new_unpack = if *before_index == 0 {
                    unpack.clone()
                } else {
                    WithUnpack {
                        before: unpack.before.iter().skip(*before_index).cloned().collect(),
                        unpack: unpack.unpack.clone(),
                        after: unpack.after.clone(),
                    }
                };
                Some(UnpackedArgument::WithUnpack(new_unpack))
            }
            Self::Any(cause) => Some(UnpackedArgument::Normal {
                inferred: Inferred::new_any(*cause),
                arbitrary_len: true,
            }),
        }
    }

    pub fn unpack_starred_and_return_is_empty(
        &mut self,
        i_s: &InferenceState,
        after: usize,
        tuple_target: bool,
        use_joins: bool,
    ) -> (bool, Inferred) {
        (
            false,
            match self {
                Self::Inferred(inf) => Inferred::new_list_of(i_s.db, inf.as_type(i_s)),
                Self::Any(cause) => Inferred::new_list_of(i_s.db, Type::Any(*cause)),
                Self::FixedLenTupleGenerics {
                    entries,
                    current_index,
                } => {
                    let end = entries.len() - after;
                    let fetch = end - *current_index;
                    let relevant_entries = &entries[*current_index..end];
                    let inf = if tuple_target {
                        let mut tuple_entries = vec![];
                        for t in relevant_entries {
                            tuple_entries.push(t.clone());
                        }
                        Inferred::from_type(Type::Tuple(Tuple::new_fixed_length(
                            tuple_entries.into(),
                        )))
                    } else {
                        let union = if use_joins {
                            Inferred::gather_base_types(i_s, |callable| {
                                for t in relevant_entries {
                                    callable(Inferred::from_type(
                                        t.avoid_implicit_literal_cow(i_s.db).into_owned(),
                                    ));
                                }
                            })
                        } else {
                            Inferred::gather_simplified_union(i_s, |callable| {
                                for t in relevant_entries {
                                    callable(Inferred::from_type(
                                        t.avoid_implicit_literal_cow(i_s.db).into_owned(),
                                    ));
                                }
                            })
                        };
                        let generic = union.as_type(i_s);
                        Inferred::new_list_of(i_s.db, generic)
                    };
                    *current_index += fetch;
                    if fetch == 0 {
                        return (true, inf);
                    }
                    inf
                }
                Self::WithUnpack {
                    unpack,
                    before_index,
                    after_index,
                } => {
                    let result = Inferred::new_list_of(
                        i_s.db,
                        match &unpack.unpack {
                            TupleUnpack::TypeVarTuple(_) => i_s.db.python_state.object_type(),
                            TupleUnpack::ArbitraryLen(t) => {
                                let mut result = Type::NEVER;
                                for entry in unpack.before.iter().skip(*before_index) {
                                    result =
                                        result.gather_types_maybe_with_joins(i_s, entry, use_joins);
                                }
                                result = result.gather_types_maybe_with_joins(i_s, t, use_joins);
                                for entry in unpack.after.iter().rev().skip(after).rev() {
                                    result =
                                        result.gather_types_maybe_with_joins(i_s, entry, use_joins);
                                }
                                result
                            }
                        },
                    );
                    // Change the indexes, to account for what has been fetched.
                    *before_index = unpack.before.len();
                    let after_len = unpack.after.len();
                    *after_index = after_len.saturating_sub(after);
                    result
                }
                Self::Union(_) => unreachable!(),
            },
        )
    }

    pub fn unpack_next(&mut self) -> Inferred {
        self.unpack_next_with_customized_after(|_| None)
    }

    pub fn unpack_next_with_customized_after(
        &mut self,
        on_after: impl FnOnce(&WithUnpack) -> Option<Type>,
    ) -> Inferred {
        // It is important to note that the lengths have been checked before and it is at this
        // point clear that we can unpack the iterator. This should only ever be used for
        // assignment calculation and assigning patterns, e.g. foo, *bar = ...
        match self {
            Self::Inferred(inf) => inf.clone(),
            Self::Any(cause) => Inferred::new_any(*cause),
            Self::FixedLenTupleGenerics {
                entries,
                current_index,
            } => next_fixed_length(entries, current_index).unwrap(),
            Self::WithUnpack {
                unpack,
                before_index,
                after_index,
            } => Inferred::from_type({
                if let Some(result) = unpack.before.get(*before_index) {
                    *before_index += 1;
                    result.clone()
                } else if let Some(custom) = on_after(unpack) {
                    custom
                } else if let Some(result) = unpack.after.get(*after_index) {
                    *after_index += 1;
                    result.clone()
                } else {
                    recoverable_error!("Next on exhausted after should never happen");
                    Type::ERROR
                }
            }),
            Self::Union(_) => unreachable!(),
        }
    }

    pub fn len_infos(&self) -> Option<TupleLenInfos> {
        match self {
            Self::Inferred(_) | Self::Any(_) => None,
            Self::FixedLenTupleGenerics {
                entries,
                current_index,
            } => Some(TupleLenInfos::FixedLen(
                entries.as_ref().len() - current_index,
            )),
            Self::Union(_) => unreachable!(),
            Self::WithUnpack { unpack, .. } => Some(TupleLenInfos::WithStar {
                before: unpack.before.len(),
                after: unpack.after.len(),
            }),
        }
    }
}

pub(crate) enum UnpackedArgument {
    Normal {
        inferred: Inferred,
        arbitrary_len: bool,
    },
    WithUnpack(WithUnpack),
}

#[derive(Copy, Clone)]
pub(crate) enum TupleLenInfos {
    FixedLen(usize),
    WithStar { before: usize, after: usize },
}

fn next_fixed_length(entries: &[Type], current_index: &mut usize) -> Option<Inferred> {
    let result = entries.get(*current_index)?;
    *current_index += 1;
    Some(Inferred::from_type(result.clone()))
}
