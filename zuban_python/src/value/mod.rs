mod bound_method;
mod callable;
mod class;
mod function;
mod instance;
mod module;
mod named_tuple;
mod tuple;
mod typing;

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

#[macro_export]
macro_rules! base_qualified_name {
    ($value:ident, $db:ident, $name:expr) => {
        format!("{}.{}", $value.module().qualified_name($db), $name)
    };
}
