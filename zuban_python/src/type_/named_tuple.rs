use std::{cell::OnceCell, rc::Rc};

use crate::{database::Database, type_helpers::Module};

use super::{CallableContent, CallableParam, StringSlice, TupleContent, TypeOrTypeVarTuple};

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
}
