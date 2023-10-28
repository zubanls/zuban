use std::{cell::OnceCell, rc::Rc};

use crate::{
    arguments::Arguments,
    database::{ComplexPoint, Database},
    debug,
    file::{new_collections_named_tuple, new_typing_named_tuple},
    getitem::SliceType,
    inference_state::InferenceState,
    inferred::Inferred,
    matching::{FormatData, Generics, IteratorContent, LookupResult, OnTypeError, ResultContext},
    node_ref::NodeRef,
    type_helpers::{Module, Tuple},
    utils::join_with_commas,
};

use super::{
    CallableContent, CallableParam, FormatStyle, RecursiveAlias, StringSlice, TupleContent, Type,
    TypeOrTypeVarTuple,
};

#[derive(Debug, PartialEq, Clone)]
pub struct NamedTuple {
    pub name: StringSlice,
    pub __new__: Rc<CallableContent>,
    tuple: OnceCell<Rc<TupleContent>>,
}

impl NamedTuple {
    pub fn new(name: StringSlice, __new__: CallableContent) -> Self {
        Self {
            name,
            __new__: Rc::new(__new__),
            tuple: OnceCell::new(),
        }
    }

    pub fn clone_with_new_init_class(&self, name: StringSlice) -> Rc<NamedTuple> {
        let mut nt = self.clone();
        let mut callable = nt.__new__.as_ref().clone();
        callable.name = Some(name);
        nt.__new__ = Rc::new(callable);
        Rc::new(nt)
    }

    pub fn params(&self) -> &[CallableParam] {
        // Namedtuple callables contain a first param `Type[Self]` that we should skip.
        &self.__new__.expect_simple_params()[1..]
    }

    pub fn search_param(&self, db: &Database, search_name: &str) -> Option<&CallableParam> {
        self.params()
            .iter()
            .find(|p| p.name.unwrap().as_str(db) == search_name)
    }

    pub fn name<'a>(&self, db: &'a Database) -> &'a str {
        self.name.as_str(db)
    }

    pub fn qualified_name(&self, db: &Database) -> String {
        let module = Module::from_file_index(db, self.name.file_index).qualified_name(db);
        format!("{module}.{}", self.name(db))
    }

    pub fn as_tuple(&self) -> Rc<TupleContent> {
        self.tuple
            .get_or_init(|| {
                Rc::new(TupleContent::new_fixed_length(
                    self.params()
                        .iter()
                        .map(|t| {
                            TypeOrTypeVarTuple::Type(
                                t.param_specific.expect_positional_type_as_ref().clone(),
                            )
                        })
                        .collect(),
                ))
            })
            .clone()
    }

    pub fn as_tuple_ref(&self) -> &TupleContent {
        self.as_tuple();
        self.tuple.get().unwrap()
    }

    pub fn format_with_name(
        &self,
        format_data: &FormatData,
        name: &str,
        generics: Generics,
    ) -> Box<str> {
        if format_data.style != FormatStyle::MypyRevealType {
            return Box::from(name);
        }
        let params = self.params();
        // We need to check recursions here, because for class definitions of named tuples can
        // recurse with their attributes.
        let rec = RecursiveAlias::new(self.__new__.defined_at, None);
        if format_data.has_already_seen_recursive_alias(&rec) {
            return Box::from(name);
        }
        let format_data = &format_data.with_seen_recursive_alias(&rec);
        let types = match params.is_empty() {
            true => "()".into(),
            false => join_with_commas(params.iter().map(|p| {
                let t = p.param_specific.expect_positional_type_as_ref();
                match generics {
                    Generics::NotDefinedYet | Generics::None => t.format(format_data),
                    _ => t
                        .replace_type_var_likes_and_self(
                            format_data.db,
                            &mut |usage| {
                                generics
                                    .nth_usage(format_data.db, &usage)
                                    .into_generic_item(format_data.db)
                            },
                            &|| todo!(),
                        )
                        .format(format_data),
                }
                .into()
            })),
        };
        format!("tuple[{types}, fallback={name}]",).into()
    }

    pub fn iter(&self, i_s: &InferenceState, from: NodeRef) -> IteratorContent {
        Tuple::new(&self.as_tuple()).iter(i_s, from)
    }

    pub fn get_item(
        &self,
        i_s: &InferenceState,
        slice_type: &SliceType,
        result_context: &mut ResultContext,
    ) -> Inferred {
        Tuple::new(&self.as_tuple()).get_item(i_s, slice_type, result_context)
    }

    pub fn lookup(&self, i_s: &InferenceState, name: &str) -> LookupResult {
        for p in self.params() {
            if name == p.name.unwrap().as_str(i_s.db) {
                return LookupResult::UnknownName(Inferred::from_type(
                    p.param_specific.expect_positional_type_as_ref().clone(),
                ));
            }
        }
        if name == "__new__" {
            return LookupResult::UnknownName(Inferred::from_type(Type::Callable(
                self.__new__.clone(),
            )));
        }
        debug!("TODO lookup of NamedTuple base classes");
        LookupResult::None
    }
}

pub fn execute_typing_named_tuple(i_s: &InferenceState, args: &dyn Arguments) -> Inferred {
    match new_typing_named_tuple(i_s, args, false) {
        Some(rc) => Inferred::new_unsaved_complex(ComplexPoint::NamedTupleDefinition(Rc::new(
            Type::NamedTuple(rc),
        ))),
        None => Inferred::new_any(),
    }
}

pub fn execute_collections_named_tuple<'db>(
    i_s: &InferenceState<'db, '_>,
    args: &dyn Arguments<'db>,
    result_context: &mut ResultContext,
    on_type_error: OnTypeError<'db, '_>,
) -> Inferred {
    i_s.db
        .python_state
        .collections_namedtuple_function()
        .execute(i_s, args, result_context, on_type_error);
    match new_collections_named_tuple(i_s, args) {
        Some(rc) => Inferred::new_unsaved_complex(ComplexPoint::NamedTupleDefinition(Rc::new(
            Type::NamedTuple(rc),
        ))),
        None => Inferred::new_any(),
    }
}
