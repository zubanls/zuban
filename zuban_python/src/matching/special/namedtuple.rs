use std::rc::Rc;

use once_cell::unsync::OnceCell;

use crate::{
    arguments::Arguments,
    database::{
        CallableContent, CallableParam, CallableParams, Database, DbType, FormatStyle,
        GenericsList, ParamSpecific, RecursiveAlias, ReplaceSelf, ReplaceTypeVarLike, SpecialType,
        StringSlice, TupleContent, TupleTypeArguments, Variance,
    },
    debug,
    diagnostics::IssueType,
    file::infer_index,
    getitem::{SliceType, SliceTypeContent},
    inference_state::InferenceState,
    inferred::Inferred,
    matching::{
        calculate_callable_type_vars_and_return, FormatData, Generics, Match, Matcher,
        ResultContext, Type,
    },
    node_ref::NodeRef,
    value::{IteratorContent, LookupResult, OnTypeError, Value},
    ValueKind,
};

#[derive(Debug, PartialEq, Clone)]
pub struct NamedTuple {
    name: StringSlice,
    // Basically __new__
    constructor: Rc<CallableContent>,
    tuple: OnceCell<Rc<TupleContent>>,
}

impl NamedTuple {}

/*
impl SpecialType for NamedTuple {
    fn matches_internal(
        &self,
        i_s: &InferenceState,
        matcher: &mut Matcher,
        value_type: &Type,
        variance: Variance,
    ) -> Match {
    }
    fn instantiate<'db>(
        &self,
        i_s: &InferenceState<'db, '_>,
        full_type: &DbType,
        args: &dyn Arguments<'db>,
        on_type_error: OnTypeError<'db, '_>,
    ) -> DbType {
    }
}
*/
