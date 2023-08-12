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

use std::rc::Rc;

pub use format_data::{FormatData, ParamsStyle};
pub use generic::Generic;
pub use generics::{Generics, GenericsIterator};
pub use lookup_result::LookupResult;
pub use match_::{ArgumentIndexWithParam, Match, MismatchReason, SignatureMatch};
pub use matcher::{
    calculate_callable_init_type_vars_and_return, calculate_callable_type_vars_and_return,
    calculate_class_init_type_vars_and_return, calculate_function_type_vars_and_return,
    CalculatedTypeArguments, FunctionOrCallable, Matcher,
};
pub use params::{matches_params, matches_simple_params, Param};
pub use result_context::ResultContext;
pub use type_::{
    common_base_type, execute_type_of_type, match_tuple_type_arguments, ReplaceSelf, Type,
};
pub use utils::{
    create_signature_without_self, create_signature_without_self_for_callable, maybe_class_usage,
    replace_class_type_vars, replace_class_type_vars_in_callable,
};

use crate::{
    arguments::Argument,
    database::{Database, TypeOrTypeVarTuple},
    inference_state::InferenceState,
    inferred::Inferred,
    type_helpers::Class,
};

type OnOverloadMismatch<'db, 'a> = Option<&'a dyn Fn(&InferenceState<'db, '_>, Option<&Class>)>;
type GenerateDiagnosticString<'a> =
    &'a dyn Fn(&FunctionOrCallable, &Database, Option<&Class>) -> Option<String>;

#[derive(Clone, Copy)]
pub struct OnTypeError<'db, 'a> {
    pub callback: OnTypeErrorCallback<'db, 'a>,
    pub on_overload_mismatch: OnOverloadMismatch<'db, 'a>,
    pub generate_diagnostic_string: GenerateDiagnosticString<'a>,
}

impl<'db, 'a> OnTypeError<'db, 'a> {
    pub fn new(callback: OnTypeErrorCallback<'db, 'a>) -> Self {
        Self {
            callback,
            on_overload_mismatch: None,
            generate_diagnostic_string: &func_or_callable_diagnostic_string,
        }
    }

    pub fn with_overload_mismatch(
        callback: OnTypeErrorCallback<'db, 'a>,
        on_overload_mismatch: OnOverloadMismatch<'db, 'a>,
    ) -> Self {
        Self {
            callback,
            on_overload_mismatch,
            generate_diagnostic_string: &func_or_callable_diagnostic_string,
        }
    }

    pub fn with_custom_generate_diagnostic_string<'c>(
        &self,
        generate_diagnostic_string: GenerateDiagnosticString<'c>,
    ) -> OnTypeError<'db, 'c>
    where
        'a: 'c,
    {
        OnTypeError {
            generate_diagnostic_string,
            callback: self.callback,
            on_overload_mismatch: self.on_overload_mismatch,
        }
    }
}

// For whatever reason we cannot just pass FunctionOrCallable::diagnostic_string, even though it
// results in the exactly same behavior. Probably a Rust bug.
fn func_or_callable_diagnostic_string(
    f: &FunctionOrCallable,
    db: &Database,
    c: Option<&Class>,
) -> Option<String> {
    f.diagnostic_string(db)
}

pub type OnTypeErrorCallback<'db, 'a> = &'a dyn Fn(
    &InferenceState<'db, '_>,
    &dyn Fn(&str) -> Option<Box<str>>, // error_text; argument is a prefix
    &Argument,
    Box<str>,
    Box<str>,
);
pub type OnLookupError<'a> = &'a dyn Fn(&Type);

#[derive(Debug, Clone)]
pub enum IteratorContent {
    Inferred(Inferred),
    // The code before makes sure that no type var tuples are passed.
    FixedLengthTupleGenerics {
        entries: Rc<[TypeOrTypeVarTuple]>,
        current_index: usize,
    },
    Union(Vec<IteratorContent>),
    Empty,
    Any,
}

impl IteratorContent {
    pub fn new_tuple(entries: Rc<[TypeOrTypeVarTuple]>) -> IteratorContent {
        Self::FixedLengthTupleGenerics {
            entries,
            current_index: 0,
        }
    }

    pub fn infer_all(self, i_s: &InferenceState) -> Inferred {
        match self {
            Self::Inferred(inferred) => inferred,
            Self::FixedLengthTupleGenerics {
                entries,
                current_index,
            } => Inferred::gather_union(i_s, |add| {
                for entry in entries.iter().skip(current_index) {
                    match entry {
                        TypeOrTypeVarTuple::Type(b) => add(Inferred::from_type(b.clone())),
                        TypeOrTypeVarTuple::TypeVarTuple(_) => unreachable!(),
                    }
                }
            }),
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
            Self::FixedLengthTupleGenerics {
                entries,
                current_index,
            } => {
                let result = entries.get(*current_index);
                *current_index += 1;
                result.map(|result| {
                    Inferred::from_type(match result {
                        TypeOrTypeVarTuple::Type(t) => t.clone(),
                        TypeOrTypeVarTuple::TypeVarTuple(_) => unreachable!(),
                    })
                })
            }
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
            Self::FixedLengthTupleGenerics {
                entries,
                current_index,
            } => Some(entries.as_ref().len() - current_index),
            Self::Union(iterators) => todo!(),
            Self::Empty => todo!(),
        }
    }
}
