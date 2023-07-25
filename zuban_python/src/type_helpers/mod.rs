mod bound_method;
mod callable;
mod class;
mod enum_;
mod function;
mod instance;
mod module;
mod named_tuple;
mod tuple;
mod typing;

pub use bound_method::{BoundMethod, BoundMethodFunction};
pub use callable::{format_pretty_callable, Callable};
pub use class::{Class, MroIterator, TypeOrClass};
pub use enum_::{lookup_on_enum_class, lookup_on_enum_instance, lookup_on_enum_member_instance};
pub use function::{
    is_private, FirstParamKind, FirstParamProperties, Function, InferrableParam, OverloadedFunction,
};
pub use instance::{execute_super, Instance};
pub use module::{lookup_in_namespace, Module};
pub use named_tuple::NamedTupleValue;
pub use tuple::Tuple;
pub use typing::{
    NewTypeClass, ParamSpecClass, RevealTypeFunction, TypeVarClass, TypeVarTupleClass, TypingCast,
    TypingClass, TypingType,
};

#[macro_export]
macro_rules! base_qualified_name {
    ($value:ident, $db:ident, $name:expr) => {
        format!("{}.{}", $value.module().qualified_name($db), $name)
    };
}
