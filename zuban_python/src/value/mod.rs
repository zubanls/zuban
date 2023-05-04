mod bound_method;
mod callable;
mod class;
mod function;
mod instance;
mod literal;
mod module;
mod named_tuple;
mod none;
mod tuple;
mod type_alias;
mod typing;

use crate::arguments::Argument;
use crate::database::{Database, DbType, FileIndex, PointLink, TypeOrTypeVarTuple};
use crate::getitem::SliceType;
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::matching::{ResultContext, Type};
use crate::node_ref::NodeRef;
pub use bound_method::{BoundMethod, BoundMethodFunction};
pub use callable::Callable;
pub use class::{Class, MroIterator};
pub use function::{FirstParamProperties, Function, InferrableParam, OverloadedFunction};
pub use instance::Instance;
pub use literal::Literal;
pub use module::Module;
pub use named_tuple::NamedTupleValue;
pub use none::NoneInstance;
pub use tuple::Tuple;
pub use type_alias::TypeAlias;
pub use typing::{
    NewTypeClass, NewTypeInstance, ParamSpecClass, RevealTypeFunction, TypeVarClass,
    TypeVarInstance, TypeVarTupleClass, TypingAny, TypingCast, TypingClass, TypingClassVar,
    TypingType,
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
pub type OnLookupError<'db, 'a> = &'a dyn Fn(&InferenceState<'db, '_>);

enum ArrayType {
    None,
    Tuple,
    List,
    Dict,
    Set,
}

#[derive(Debug, Eq, PartialEq)]
pub enum ValueKind {
    Unknown = 0,
    // Taken from LSP, unused kinds are commented
    //File = 1,
    Module = 2,
    Namespace = 3,
    //Package = 4,
    Class = 5,
    Method = 6,
    Property = 7,
    Field = 8,
    //Constructor = 9,
    //Enum = 10,
    //Interface = 11,
    Function = 12,
    //Variable = 13,
    Constant = 14,
    String = 15,
    Number = 16,
    Bool = 17,
    Array = 18,
    Object = 19, // From JavaScript objects -> Basically an instance
    //Key = 20,
    Null = 21,
    //EnumMember = 22,
    //Struct = 23,
    //Event = 24,
    //Operator = 25,
    TypeParameter = 26,
}

#[macro_export]
macro_rules! base_description {
    ($value:ident) => {
        format!(
            "{} {}",
            format!("{:?}", $value.kind()).to_lowercase(),
            $value.name()
        )
    };
}

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
    pub fn into_maybe_inferred(self) -> Option<Inferred> {
        // TODO is it ok that map does not include FileReference(_)? (probably not)
        match self {
            Self::GotoName(_, inf) | Self::UnknownName(inf) => Some(inf),
            Self::None | Self::FileReference(_) => None,
        }
    }

    pub fn into_inferred(self) -> Inferred {
        self.into_maybe_inferred()
            .unwrap_or_else(Inferred::new_unknown)
    }

    pub fn union(self, other: Self) -> Self {
        match self.into_maybe_inferred() {
            Some(self_) => match other.into_maybe_inferred() {
                Some(other) => LookupResult::UnknownName(self_.union(other)),
                None => LookupResult::UnknownName(self_),
            },
            None => other,
        }
    }

    fn map(self, c: impl FnOnce(Inferred) -> Inferred) -> Self {
        match self {
            Self::GotoName(link, inf) => Self::GotoName(link, c(inf)),
            Self::UnknownName(inf) => Self::UnknownName(c(inf)),
            // TODO is it ok that map does not include FileReference(_)?
            _ => self,
        }
    }

    fn and_then(self, c: impl FnOnce(Inferred) -> Option<Inferred>) -> Option<Self> {
        match self {
            Self::GotoName(link, inf) => c(inf).map(|inf| Self::GotoName(link, inf)),
            Self::UnknownName(inf) => c(inf).map(Self::UnknownName),
            // TODO is it ok that map does not include FileReference(_)?
            _ => Some(self),
        }
    }
}

// Why HackyProof, see: https://github.com/rust-lang/rust/issues/92520
pub trait Value<'db: 'a, 'a, HackyProof = &'a &'db ()>: std::fmt::Debug {
    fn kind(&self) -> ValueKind;

    //fn file(&self) -> &'db dyn File;

    fn name(&self) -> &str;

    fn qualified_name(&self, db: &'a Database) -> String {
        base_qualified_name!(self, db, self.name())
    }

    fn module(&self, db: &'a Database) -> Module<'a> {
        todo!("{:?}", self)
    }

    fn description(&self, i_s: &InferenceState) -> String {
        base_description!(self)
    }

    fn lookup_internal(
        &self,
        i_s: &InferenceState,
        node_ref: Option<NodeRef>,
        name: &str,
    ) -> LookupResult;

    fn should_add_lookup_error(&self, db: &Database) -> bool {
        true
    }

    fn lookup(
        &self,
        i_s: &InferenceState<'db, '_>,
        node_ref: Option<NodeRef>,
        name: &str,
        on_error: OnLookupError<'db, '_>,
    ) -> LookupResult {
        let result = self.lookup_internal(i_s, node_ref, name);
        if matches!(result, LookupResult::None) && self.should_add_lookup_error(i_s.db) {
            on_error(i_s);
        }
        result
    }

    fn lookup_implicit(
        &self,
        i_s: &InferenceState<'db, '_>,
        node_ref: Option<NodeRef>,
        name: &str,
        on_error: OnLookupError<'db, '_>,
    ) -> Inferred {
        match self.lookup(i_s, node_ref, name, on_error) {
            LookupResult::GotoName(_, inf) | LookupResult::UnknownName(inf) => inf,
            LookupResult::FileReference(f) => todo!(),
            LookupResult::None => Inferred::new_unknown(),
        }
    }

    fn get_item(
        &self,
        i_s: &InferenceState,
        slice_type: &SliceType,
        result_context: &mut ResultContext,
    ) -> Inferred {
        todo!("get_item not implemented for {self:?}")
    }

    fn as_instance(&self) -> Option<&Instance<'a>> {
        None
    }
    fn as_function(&self) -> Option<&Function<'a, '_>> {
        None
    }
    fn as_callable(&self) -> Option<Callable<'a>> {
        None
    }
    fn as_overloaded_function(&self) -> Option<&OverloadedFunction<'a>> {
        None
    }
    fn as_typing_class(&self) -> Option<&TypingClass> {
        None
    }
    fn as_class(&self) -> Option<&Class> {
        None
    }
    fn is_any(&self) -> bool {
        false
    }
    fn is_none(&self) -> bool {
        false
    }
    fn as_module(&self) -> Option<&Module<'a>> {
        None
    }

    fn as_type(&self, i_s: &InferenceState<'db, '_>) -> Type<'a> {
        todo!("{self:?}")
    }
}
