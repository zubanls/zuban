mod bound_method;
mod callable;
mod class;
mod function;
mod instance;
mod module;
mod named_tuple;
mod tuple;
mod typing;

use crate::arguments::Argument;
use crate::database::{DbType, TypeOrTypeVarTuple};
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::matching::Type;
pub use bound_method::{BoundMethod, BoundMethodFunction};
pub use callable::Callable;
pub use class::{Class, MroIterator};
pub use function::{FirstParamProperties, Function, InferrableParam, OverloadedFunction};
pub use instance::Instance;
pub use module::Module;
pub use named_tuple::NamedTupleValue;
pub use tuple::Tuple;
pub use typing::{
    NewTypeClass, ParamSpecClass, RevealTypeFunction, TypeVarClass, TypeVarInstance,
    TypeVarTupleClass, TypingCast, TypingClass, TypingType,
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
pub type OnLookupError<'db, 'a> = &'a dyn Fn(&InferenceState<'db, '_>, &Type);

#[macro_export]
macro_rules! base_qualified_name {
    ($value:ident, $db:ident, $name:expr) => {
        format!("{}.{}", $value.module().qualified_name($db), $name)
    };
}

#[derive(Debug, Clone)]
pub enum IteratorContent<'a> {
    Inferred(Inferred),
    // The code before makes sure that no type var tuples are passed.
    FixedLengthTupleGenerics(std::slice::Iter<'a, TypeOrTypeVarTuple>),
    Empty,
    Any,
}

impl IteratorContent<'_> {
    pub fn infer_all(self, i_s: &InferenceState) -> Inferred {
        match self {
            Self::Inferred(inferred) => inferred,
            Self::FixedLengthTupleGenerics(generics) => Inferred::execute_db_type(
                i_s,
                generics.fold(DbType::Never, |a, b| {
                    a.union(match b {
                        TypeOrTypeVarTuple::Type(b) => b.clone(),
                        TypeOrTypeVarTuple::TypeVarTuple(_) => unreachable!(),
                    })
                }),
            ),
            Self::Empty => todo!(),
            Self::Any => Inferred::new_any(),
        }
    }

    pub fn next(&mut self, i_s: &InferenceState) -> Option<Inferred> {
        match self {
            Self::Inferred(inferred) => Some(inferred.clone()),
            Self::FixedLengthTupleGenerics(t) => t.next().map(|t| {
                Inferred::execute_db_type(
                    i_s,
                    match t {
                        TypeOrTypeVarTuple::Type(t) => t.clone(),
                        TypeOrTypeVarTuple::TypeVarTuple(_) => unreachable!(),
                    },
                )
            }),
            Self::Empty => todo!(),
            Self::Any => Some(Inferred::new_any()),
        }
    }

    pub fn len(&self) -> Option<usize> {
        match self {
            Self::Inferred(_) | Self::Any => None,
            Self::FixedLengthTupleGenerics(t) => Some(t.len()),
            Self::Empty => todo!(),
        }
    }
}
