mod bound_method;
mod class;
mod function;
mod instance;
mod iterable;
mod module;
mod none;
mod typing;

use parsa_python_ast::{ListElement, ListElementIterator};

use crate::arguments::{Arguments, NoArguments};
use crate::getitem::SliceType;
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
pub use bound_method::BoundMethod;
pub use class::{Class, ClassLike};
pub use function::{Function, OverloadedFunction};
pub use instance::Instance;
pub use iterable::{DictLiteral, ListLiteral};
pub use module::Module;
pub use none::NoneInstance;
pub use typing::{
    Callable, CallableClass, Tuple, TupleClass, TypingCast, TypingClass, TypingClassVar,
    TypingType, TypingWithGenerics,
};

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

pub enum IteratorContent<'db> {
    Inferred(Inferred<'db>),
    ListLiteral(ListLiteral<'db>, ListElementIterator<'db>),
    Empty,
}

impl<'db> IteratorContent<'db> {
    pub fn infer_all(self) -> Inferred<'db> {
        match self {
            Self::Inferred(inferred) => inferred,
            Self::ListLiteral(list, _) => todo!(), //list.generic_part(),
            Self::Empty => todo!(),
        }
    }

    pub fn next(&mut self, i_s: &mut InferenceState<'db, '_>) -> Option<Inferred<'db>> {
        match self {
            Self::Inferred(inferred) => None,
            Self::ListLiteral(list, list_elements) => {
                list_elements.next().map(|list_element| match list_element {
                    ListElement::NamedExpression(named_expr) => {
                        list.infer_named_expr(i_s, named_expr)
                    }
                    ListElement::StarNamedExpression(_) => todo!(),
                })
            }
            Self::Empty => todo!(),
        }
    }
}

// Why HackyProof, see: https://github.com/rust-lang/rust/issues/92520
pub trait Value<'db: 'a, 'a, HackyProof = &'a &'db ()>: std::fmt::Debug {
    fn kind(&self) -> ValueKind;

    //fn file(&self) -> &'db dyn File;

    fn name(&self) -> &'db str;

    fn description(&self, i_s: &mut InferenceState<'db, '_>) -> String {
        base_description!(self)
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

    fn iter(&self, i_s: &mut InferenceState<'db, '_>) -> IteratorContent<'db> {
        IteratorContent::Inferred(
            self.lookup(i_s, "__iter__")
                .run_on_value(i_s, &mut |i_s, value| value.execute(i_s, &NoArguments()))
                .execute_function(i_s, "__next__"),
        )
    }

    fn as_instance(&self) -> Option<&Instance<'db, 'a>> {
        None
    }
    fn as_class(&self) -> Option<&Class<'db, 'a>> {
        // TODO is this really needed anymore next to as_class_like?
        None
    }
    fn as_class_like(&self) -> Option<ClassLike<'db, 'a>> {
        None
    }
    fn as_typing_with_generics(
        &self,
        i_s: &mut InferenceState<'db, '_>,
    ) -> Option<&TypingWithGenerics<'db>> {
        None
    }
    fn is_none(&self) -> bool {
        false
    }

    fn class(&self, i_s: &mut InferenceState<'db, '_>) -> ClassLike<'db, 'a> {
        todo!("{:?}", self)
    }
}
