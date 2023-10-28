use std::rc::Rc;

use crate::arguments::Arguments;
use crate::database::ComplexPoint;
use crate::database::Database;
use crate::debug;
use crate::file::{new_collections_named_tuple, new_typing_named_tuple};
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::matching::{LookupResult, OnTypeError, ResultContext};
use crate::type_::{NamedTuple, Type};

#[derive(Debug)]
pub struct NamedTupleValue<'a> {
    pub db: &'a Database,
    pub nt: &'a Rc<NamedTuple>,
}

impl<'a> NamedTupleValue<'a> {
    pub fn new(db: &'a Database, nt: &'a Rc<NamedTuple>) -> Self {
        Self { db, nt }
    }

    pub fn lookup(&self, i_s: &InferenceState, name: &str) -> LookupResult {
        for p in self.nt.params() {
            if name == p.name.unwrap().as_str(i_s.db) {
                return LookupResult::UnknownName(Inferred::from_type(
                    p.param_specific.expect_positional_type_as_ref().clone(),
                ));
            }
        }
        if name == "__new__" {
            return LookupResult::UnknownName(Inferred::from_type(Type::Callable(
                self.nt.__new__.clone(),
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
