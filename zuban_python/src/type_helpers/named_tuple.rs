use std::rc::Rc;

use crate::arguments::Arguments;
use crate::database::{ComplexPoint, DbType, FormatStyle, NamedTuple, RecursiveAlias};
use crate::debug;
use crate::file::{new_collections_named_tuple, new_typing_named_tuple};
use crate::getitem::SliceType;
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::matching::{
    FormatData, Generics, IteratorContent, LookupResult, OnTypeError, ResultContext, Type,
};
use crate::{database::Database, node_ref::NodeRef};

use super::Tuple;

#[derive(Debug)]
pub struct NamedTupleValue<'a> {
    pub db: &'a Database,
    pub nt: &'a Rc<NamedTuple>,
}

impl<'a> NamedTupleValue<'a> {
    pub fn new(db: &'a Database, nt: &'a Rc<NamedTuple>) -> Self {
        Self { db, nt }
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
        let params = self.nt.params();
        // We need to check recursions here, because for class definitions of named tuples can
        // recurse with their attributes.
        let rec = RecursiveAlias::new(self.nt.__new__.defined_at, None);
        if format_data.has_already_seen_recursive_alias(&rec) {
            return Box::from(name);
        }
        let format_data = &format_data.with_seen_recursive_alias(&rec);
        let types = match params.is_empty() {
            true => "()".into(),
            false => params
                .iter()
                .map(|p| {
                    let t = p.param_specific.expect_positional_db_type_as_ref();
                    match generics {
                        Generics::NotDefinedYet | Generics::None => t.format(format_data),
                        _ => Type::new(t)
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
                })
                .collect::<Vec<_>>()
                .join(", "),
        };
        format!("tuple[{types}, fallback={name}]",).into()
    }

    pub fn iter(&self, i_s: &InferenceState, from: NodeRef) -> IteratorContent {
        Tuple::new(&self.nt.as_tuple()).iter(i_s, from)
    }

    pub fn lookup(&self, i_s: &InferenceState, name: &str) -> LookupResult {
        for p in self.nt.params() {
            if name == p.name.unwrap().as_str(i_s.db) {
                return LookupResult::UnknownName(Inferred::from_type(
                    p.param_specific.expect_positional_db_type_as_ref().clone(),
                ));
            }
        }
        if name == "__new__" {
            return LookupResult::UnknownName(Inferred::from_type(DbType::Callable(
                self.nt.__new__.clone(),
            )));
        }
        debug!("TODO lookup of NamedTuple base classes");
        LookupResult::None
    }

    pub fn get_item(
        &self,
        i_s: &InferenceState,
        slice_type: &SliceType,
        result_context: &mut ResultContext,
    ) -> Inferred {
        Tuple::new(&self.nt.as_tuple()).get_item(i_s, slice_type, result_context)
    }
}

pub fn execute_typing_named_tuple(i_s: &InferenceState, args: &dyn Arguments) -> Inferred {
    match new_typing_named_tuple(i_s, args) {
        Some(rc) => Inferred::new_unsaved_complex(ComplexPoint::NamedTupleDefinition(Rc::new(
            DbType::NamedTuple(rc),
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
            DbType::NamedTuple(rc),
        ))),
        None => Inferred::new_any(),
    }
}
