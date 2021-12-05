mod bound_method;
mod class;
mod function;
mod instance;
mod iterable;
mod module;
mod typing;

use crate::arguments::Arguments;
use crate::database::GenericPart;
use crate::getitem::SliceType;
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
pub use bound_method::BoundMethod;
pub use class::{Class, ClassLike};
pub use function::{Function, OverloadedFunction};
pub use instance::Instance;
pub use iterable::{DictLiteral, ListLiteral};
pub use module::Module;
pub use typing::{Tuple, TupleClass, TypingClass, TypingWithGenerics};

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
    Boolean = 17,
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

pub trait Value<'db>: std::fmt::Debug {
    fn kind(&self) -> ValueKind;

    //fn file(&self) -> &'db dyn File;

    fn name(&self) -> &'db str;

    fn description(&self, i_s: &mut InferenceState<'db, '_>) -> String {
        format!(
            "{} {}",
            format!("{:?}", self.kind()).to_lowercase(),
            self.name()
        )
    }

    fn lookup(&self, i_s: &mut InferenceState<'db, '_>, name: &str) -> Inferred<'db>;
    fn execute(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
    ) -> Inferred<'db> {
        todo!()
    }
    fn get_item(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        slice_type: &SliceType<'db>,
    ) -> Inferred<'db> {
        todo!()
    }

    fn as_instance(&self) -> Option<&Instance<'db, '_>> {
        None
    }
    fn as_class(&self) -> Option<&Class<'db, '_>> {
        None
    }
    fn as_typing_with_generics(
        &self,
        i_s: &mut InferenceState<'db, '_>,
    ) -> Option<&TypingWithGenerics<'db>> {
        None
    }
    fn as_tuple_class(&self) -> Option<&TupleClass> {
        None
    }

    fn class(&self, i_s: &mut InferenceState<'db, '_>) -> ClassLike<'db, '_> {
        todo!("{:?}", self)
    }

    fn as_generic_part(&self, i_s: &mut InferenceState<'db, '_>) -> GenericPart {
        todo!()
    }
}
