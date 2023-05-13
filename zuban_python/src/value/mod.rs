mod bound_method;
mod callable;
mod class;
mod function;
mod instance;
mod module;
mod named_tuple;
mod none;
mod tuple;
mod typing;

use crate::arguments::Argument;
use crate::database::{DbType, FileIndex, PointLink, TypeOrTypeVarTuple};
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
pub use none::NoneInstance;
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
        format!("{}.{}", $value.module($db).qualified_name($db), $name)
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

#[derive(Debug)]
pub enum LookupResult {
    // Locality is part of Inferred
    GotoName(PointLink, Inferred),
    FileReference(FileIndex),
    UnknownName(Inferred),
    None,
}

impl LookupResult {
    pub fn any() -> Self {
        Self::UnknownName(Inferred::new_any())
    }

    pub fn into_maybe_inferred(self) -> Option<Inferred> {
        // TODO is it ok that map does not include FileReference(_)? (probably not)
        match self {
            Self::GotoName(_, inf) | Self::UnknownName(inf) => Some(inf),
            Self::FileReference(f) => Some(Inferred::new_file_reference(f)),
            Self::None => None,
        }
    }

    pub fn into_inferred(self) -> Inferred {
        self.into_maybe_inferred()
            .unwrap_or_else(Inferred::new_unknown)
    }

    pub fn union(self, i_s: &InferenceState, other: Self) -> Self {
        match self.into_maybe_inferred() {
            Some(self_) => match other.into_maybe_inferred() {
                Some(other) => LookupResult::UnknownName(self_.union(i_s, other)),
                None => LookupResult::UnknownName(self_),
            },
            None => other,
        }
    }

    /*
     * TODO remove?
    fn map(self, c: impl FnOnce(Inferred) -> Inferred) -> Self {
        match self {
            Self::GotoName(link, inf) => Self::GotoName(link, c(inf)),
            Self::UnknownName(inf) => Self::UnknownName(c(inf)),
            // TODO is it ok that map does not include FileReference(_)?
            _ => self,
        }
    }
    */

    fn and_then(self, c: impl FnOnce(Inferred) -> Option<Inferred>) -> Option<Self> {
        match self {
            Self::GotoName(link, inf) => c(inf).map(|inf| Self::GotoName(link, inf)),
            Self::UnknownName(inf) => c(inf).map(Self::UnknownName),
            // TODO is it ok that map does not include FileReference(_)?
            _ => Some(self),
        }
    }
}
