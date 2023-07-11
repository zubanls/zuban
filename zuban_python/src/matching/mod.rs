mod format_data;
mod generic;
mod generics;
mod lookup_result;
mod match_;
mod matcher;
pub mod params;
mod result_context;
mod type_;
mod utils;

pub use format_data::{FormatData, ParamsStyle};
pub use generic::Generic;
pub use generics::{Generics, GenericsIterator};
pub use lookup_result::LookupResult;
pub use match_::{ArgumentIndexWithParam, Match, MismatchReason, SignatureMatch};
pub use matcher::{
    calculate_callable_init_type_vars_and_return, calculate_callable_type_vars_and_return,
    calculate_class_init_type_vars_and_return, calculate_function_type_vars_and_return,
    CalculatedTypeArguments, Matcher,
};
pub use params::{matches_params, matches_simple_params, Param};
pub use result_context::ResultContext;
pub use type_::{common_base_type, execute_type_of_type, match_tuple_type_arguments, Type};
pub use utils::{
    create_signature_without_self, create_signature_without_self_for_callable, maybe_class_usage,
    replace_class_type_vars, replace_class_type_vars_in_callable,
};

use crate::{
    arguments::Argument,
    database::{DbType, TypeOrTypeVarTuple},
    inference_state::InferenceState,
    inferred::Inferred,
    type_helpers::Class,
};

type OnOverloadMismatch<'db, 'a> = Option<&'a dyn Fn(&InferenceState<'db, '_>, Option<&Class>)>;

#[derive(Clone, Copy)]
pub struct OnTypeError<'db, 'a> {
    pub callback: OnTypeErrorCallback<'db, 'a>,
    pub on_overload_mismatch: OnOverloadMismatch<'db, 'a>,
}

impl<'db, 'a> OnTypeError<'db, 'a> {
    pub fn new(callback: OnTypeErrorCallback<'db, 'a>) -> Self {
        Self {
            callback,
            on_overload_mismatch: None,
        }
    }
}

pub type OnTypeErrorCallback<'db, 'a> = &'a dyn Fn(
    &InferenceState<'db, '_>,
    Option<&Class>,
    &dyn Fn(&str) -> Option<Box<str>>, // error_text; argument is a prefix
    &Argument,
    Box<str>,
    Box<str>,
);
pub type OnLookupError<'a> = &'a dyn Fn(&Type);

#[derive(Debug, Clone)]
pub enum IteratorContent<'a> {
    Inferred(Inferred),
    // The code before makes sure that no type var tuples are passed.
    FixedLengthTupleGenerics(std::slice::Iter<'a, TypeOrTypeVarTuple>),
    Union(Vec<IteratorContent<'a>>),
    Empty,
    Any,
}

impl IteratorContent<'_> {
    pub fn infer_all(self, i_s: &InferenceState) -> Inferred {
        match self {
            Self::Inferred(inferred) => inferred,
            Self::FixedLengthTupleGenerics(generics) => {
                Inferred::from_type(generics.fold(DbType::Never, |a, b| {
                    a.union(
                        i_s.db,
                        match b {
                            TypeOrTypeVarTuple::Type(b) => b.clone(),
                            TypeOrTypeVarTuple::TypeVarTuple(_) => unreachable!(),
                        },
                    )
                }))
            }
            Self::Union(iterators) => Inferred::gather_union(i_s, |add| {
                for iterator in iterators {
                    add(iterator.infer_all(i_s))
                }
            }),
            Self::Empty => todo!(),
            Self::Any => Inferred::new_any(),
        }
    }

    pub fn next(&mut self, i_s: &InferenceState) -> Option<Inferred> {
        match self {
            Self::Inferred(inferred) => Some(inferred.clone()),
            Self::FixedLengthTupleGenerics(t) => t.next().map(|t| {
                Inferred::from_type(match t {
                    TypeOrTypeVarTuple::Type(t) => t.clone(),
                    TypeOrTypeVarTuple::TypeVarTuple(_) => unreachable!(),
                })
            }),
            Self::Union(iterators) => {
                let mut had_next = false;
                let result = Inferred::gather_union(i_s, |add| {
                    for iterator in iterators {
                        if let Some(inf) = iterator.next(i_s) {
                            had_next = true;
                            add(inf)
                        }
                    }
                });
                had_next.then_some(result)
            }
            Self::Empty => todo!(),
            Self::Any => Some(Inferred::new_any()),
        }
    }

    pub fn len(&self) -> Option<usize> {
        match self {
            Self::Inferred(_) | Self::Any => None,
            Self::FixedLengthTupleGenerics(t) => Some(t.len()),
            Self::Union(iterators) => todo!(),
            Self::Empty => todo!(),
        }
    }
}
