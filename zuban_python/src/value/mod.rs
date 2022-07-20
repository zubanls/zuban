mod bound_method;
mod callable;
mod class;
mod function;
mod instance;
mod iterable;
mod module;
mod none;
mod type_alias;
mod typing;

use parsa_python_ast::{ListOrSetElementIterator, StarLikeExpression};

use crate::arguments::{Arguments, NoArguments};
use crate::database::{Database, DbType, FileIndex, FormatStyle, PointLink};
use crate::diagnostics::IssueType;
use crate::getitem::SliceType;
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::node_ref::NodeRef;
pub use bound_method::BoundMethod;
pub use callable::{matches_params, Callable, CallableClass, CallableLike};
pub use class::{Class, ClassLike};
pub use function::{Function, InferrableParam, OverloadedFunction, ParamWithArgument};
pub use instance::Instance;
pub use iterable::{DictLiteral, ListLiteral};
pub use module::Module;
pub use none::NoneInstance;
pub use type_alias::TypeAlias;
pub use typing::{
    RevealTypeFunction, Tuple, TupleClass, TypeVarClass, TypeVarInstance, TypingCast, TypingClass,
    TypingClassVar, TypingType, TypingWithGenerics,
};

pub type OnTypeError<'db, 'a> = &'a dyn Fn(
    &mut InferenceState<'db, '_>,
    NodeRef<'db>,
    Option<&Class<'db, '_>>,
    Option<&Function<'db, '_>>,
    &dyn ParamWithArgument<'db, '_>,
    Box<str>,
    Box<str>,
);
pub type OnLookupError<'db, 'a> = &'a dyn Fn(&mut InferenceState<'db, '_>);

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

#[derive(Debug)]
pub enum IteratorContent<'db, 'a> {
    Inferred(Inferred<'db>),
    ListLiteral(ListLiteral<'db>, ListOrSetElementIterator<'db>),
    // TODO this should include the arbitrary_length
    TupleGenerics(std::slice::Iter<'a, DbType>),
    Empty,
    Any,
}

impl<'db> IteratorContent<'db, '_> {
    pub fn infer_all(self, i_s: &mut InferenceState<'db, '_>) -> Inferred<'db> {
        match self {
            Self::Inferred(inferred) => inferred,
            Self::ListLiteral(list, _) => {
                let g = list.db_type(i_s).clone();
                Inferred::execute_db_type(i_s, g)
            }
            Self::TupleGenerics(generics) => Inferred::execute_db_type(
                i_s,
                generics.fold(DbType::Unknown, |a, b| a.union(b.clone())),
            ),
            Self::Empty => todo!(),
            Self::Any => Inferred::new_any(),
        }
    }

    pub fn next(&mut self, i_s: &mut InferenceState<'db, '_>) -> Option<Inferred<'db>> {
        match self {
            Self::Inferred(inferred) => Some(inferred.clone()),
            Self::TupleGenerics(t) => t.next().map(|g| Inferred::execute_db_type(i_s, g.clone())),
            Self::ListLiteral(list, list_elements) => {
                list_elements.next().map(|list_element| match list_element {
                    StarLikeExpression::NamedExpression(named_expr) => {
                        list.infer_named_expr(i_s, named_expr)
                    }
                    StarLikeExpression::StarNamedExpression(_) => todo!(),
                    StarLikeExpression::Expression(_) | StarLikeExpression::StarExpression(_) => {
                        unreachable!()
                    }
                })
            }
            Self::Empty => todo!(),
            Self::Any => Some(Inferred::new_any()),
        }
    }

    pub fn len(&self) -> Option<usize> {
        match self {
            Self::Inferred(_) | Self::Any => None,
            Self::TupleGenerics(t) => Some(t.len()),
            Self::ListLiteral(_, iterator) => todo!(),
            Self::Empty => Some(0),
        }
    }
}

#[derive(Debug)]
pub enum LookupResult<'db> {
    // Locality is part of Inferred
    GotoName(PointLink, Inferred<'db>),
    FileReference(FileIndex),
    UnknownName(Inferred<'db>),
    None,
}

impl<'db> LookupResult<'db> {
    fn into_maybe_inferred(self) -> Option<Inferred<'db>> {
        // TODO is it ok that map does not include FileReference(_)? (probably not)
        match self {
            Self::GotoName(_, inf) | Self::UnknownName(inf) => Some(inf),
            Self::None | Self::FileReference(_) => None,
        }
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

    fn map(self, c: impl FnOnce(Inferred<'db>) -> Inferred<'db>) -> Self {
        match self {
            Self::GotoName(link, inf) => Self::GotoName(link, c(inf)),
            Self::UnknownName(inf) => Self::UnknownName(c(inf)),
            // TODO is it ok that map does not include FileReference(_)?
            _ => self,
        }
    }
}

// Why HackyProof, see: https://github.com/rust-lang/rust/issues/92520
pub trait Value<'db: 'a, 'a, HackyProof = &'a &'db ()>: std::fmt::Debug {
    fn kind(&self) -> ValueKind;

    //fn file(&self) -> &'db dyn File;

    fn name(&self) -> &'db str;

    fn qualified_name(&self, db: &'db Database) -> String {
        format!(
            "{}.{}",
            self.module(db).qualified_name(db),
            self.name().to_owned()
        )
    }

    fn module(&self, db: &'db Database) -> Module<'db> {
        todo!("{:?}", self)
    }

    fn description(&self, i_s: &mut InferenceState<'db, '_>) -> String {
        base_description!(self)
    }

    fn lookup_internal(&self, i_s: &mut InferenceState<'db, '_>, name: &str) -> LookupResult<'db>;

    fn should_add_lookup_error(&self, i_s: &mut InferenceState<'db, '_>) -> bool {
        true
    }

    fn lookup(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        name: &str,
        on_error: OnLookupError<'db, '_>,
    ) -> LookupResult<'db> {
        let result = self.lookup_internal(i_s, name);
        if matches!(result, LookupResult::None) && self.should_add_lookup_error(i_s) {
            on_error(i_s);
        }
        result
    }

    fn lookup_implicit(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        name: &str,
        on_error: OnLookupError<'db, '_>,
    ) -> Inferred<'db> {
        match self.lookup(i_s, name, on_error) {
            LookupResult::GotoName(_, inf) | LookupResult::UnknownName(inf) => inf,
            LookupResult::FileReference(f) => todo!(),
            LookupResult::None => Inferred::new_unknown(),
        }
    }

    fn execute(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
        on_type_error: OnTypeError<'db, '_>,
    ) -> Inferred<'db> {
        args.as_node_ref().add_typing_issue(
            i_s.db,
            IssueType::NotCallable {
                type_: format!(
                    "{:?}",
                    self.class(i_s).format(i_s, None, FormatStyle::Short)
                )
                .into(),
            },
        );
        Inferred::new_unknown()
    }

    fn get_item(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        slice_type: &SliceType<'db, '_>,
    ) -> Inferred<'db> {
        todo!("get_item not implemented for {self:?}")
    }

    fn iter(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        from: NodeRef<'db>,
    ) -> IteratorContent<'db, 'a> {
        IteratorContent::Inferred(
            self.lookup_implicit(i_s, "__iter__", &|i_s| {
                from.add_typing_issue(
                    i_s.db,
                    IssueType::NotIterable {
                        type_: format!(
                            "{:?}",
                            self.class(i_s).format(i_s, None, FormatStyle::Short)
                        )
                        .into(),
                    },
                );
            })
            .run_on_value(i_s, &mut |i_s, value| {
                value.execute(i_s, &NoArguments::new(from), &|_, _, _, _, _, _, _| todo!())
            })
            .execute_function(i_s, "__next__", from),
        )
    }

    fn as_instance(&self) -> Option<&Instance<'db, 'a>> {
        None
    }
    fn as_function(&self) -> Option<&Function<'db, 'a>> {
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
    fn as_typing_class(&self) -> Option<&TypingClass> {
        None
    }
    fn is_any(&self) -> bool {
        false
    }
    fn is_none(&self) -> bool {
        false
    }
    fn as_module(&self) -> Option<&Module<'db>> {
        None
    }

    fn class(&self, i_s: &mut InferenceState<'db, '_>) -> ClassLike<'db, 'a> {
        todo!("{self:?}")
    }
}
