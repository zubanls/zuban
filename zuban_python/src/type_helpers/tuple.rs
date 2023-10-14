use std::rc::Rc;

use crate::arguments::Arguments;
use crate::database::{
    CustomBehavior, DbType, TupleContent, TupleTypeArguments, TypeOrTypeVarTuple,
};
use crate::debug;
use crate::diagnostics::IssueType;
use crate::getitem::{SliceType, SliceTypeContent};
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::matching::{
    simplified_union_from_iterators, IteratorContent, LookupKind, LookupResult, OnTypeError,
    ResultContext, Type,
};
use crate::node_ref::NodeRef;
use crate::type_helpers::Instance;

use super::utils::method_with_fallback;

#[derive(Debug, Clone, Copy)]
pub struct Tuple<'a> {
    content: &'a Rc<TupleContent>,
}

impl<'a> Tuple<'a> {
    pub fn new(content: &'a Rc<TupleContent>) -> Self {
        Self { content }
    }

    pub fn iter(&self, i_s: &InferenceState, from: NodeRef) -> IteratorContent {
        match &self.content.args {
            args @ TupleTypeArguments::FixedLength(ts) => {
                if args.has_type_var_tuple().is_some() {
                    todo!()
                } else {
                    IteratorContent::new_tuple(ts.clone())
                }
            }
            TupleTypeArguments::ArbitraryLength(t) => {
                IteratorContent::Inferred(Inferred::from_type(t.as_ref().clone()))
            }
        }
    }

    pub fn lookup(&self, i_s: &InferenceState, node_ref: NodeRef, name: &str) -> LookupResult {
        match name {
            "__mul__" | "__rmul__" => {
                return LookupResult::UnknownName(Inferred::from_type(DbType::CustomBehavior(
                    CustomBehavior::new_method(
                        tuple_mul,
                        Some(Rc::new(DbType::Tuple(self.content.clone()))),
                    ),
                )));
            }
            "__add__" => {
                return LookupResult::UnknownName(Inferred::from_type(DbType::CustomBehavior(
                    CustomBehavior::new_method(
                        tuple_add,
                        Some(Rc::new(DbType::Tuple(self.content.clone()))),
                    ),
                )));
            }
            _ => (),
        }
        let tuple_cls = i_s.db.python_state.tuple_class(i_s.db, self.content);
        let tuple_instance = Instance::new(tuple_cls, None);
        for (mro_index, class_or_type) in tuple_cls.mro(i_s.db) {
            let (cls, lookup) = class_or_type.lookup_symbol(i_s, name);
            let result = lookup.and_then(|inf| {
                let Some(cls) = cls else {
                    unreachable!();
                };
                inf.bind_instance_descriptors(
                    i_s,
                    tuple_cls.as_db_type(i_s.db),
                    cls,
                    node_ref,
                    mro_index,
                )
            });
            match result {
                Some(LookupResult::None) => (),
                None => return LookupResult::None,
                Some(x) => return x,
            }
        }
        debug!("TODO tuple object lookups");
        LookupResult::None
    }

    pub fn get_item(
        &self,
        i_s: &InferenceState,
        slice_type: &SliceType,
        result_context: &mut ResultContext,
    ) -> Inferred {
        match slice_type.unpack() {
            SliceTypeContent::Simple(simple) => {
                let index_inf = simple
                    .file
                    .inference(i_s)
                    .infer_expression(simple.named_expr.expression());
                if !index_inf
                    .as_type(i_s)
                    .is_simple_sub_type_of(i_s, &Type::owned(i_s.db.python_state.int_db_type()))
                    .bool()
                {
                    Instance::new(i_s.db.python_state.tuple_class(i_s.db, self.content), None)
                        .lookup(
                            i_s,
                            slice_type.as_node_ref(),
                            "__getitem__",
                            LookupKind::OnlyType,
                        )
                        .into_inferred()
                        .execute(i_s, &slice_type.as_args(*i_s));
                    return Inferred::new_any();
                }
                match &self.content.args {
                    TupleTypeArguments::ArbitraryLength(t) => {
                        Inferred::execute_db_type(i_s, t.as_ref().clone())
                    }
                    args @ TupleTypeArguments::FixedLength(ts) => {
                        if args.has_type_var_tuple().is_some() {
                            todo!()
                        }
                        let out_of_range = || {
                            slice_type
                                .as_argument_node_ref()
                                .add_issue(i_s, IssueType::TupleIndexOutOfRange);
                            Some(Inferred::new_any())
                        };
                        index_inf
                            .run_on_int_literals(i_s, |index| {
                                let index = if index < 0 {
                                    let index = ts.len() as isize + index;
                                    match index.try_into() {
                                        Ok(index) => index,
                                        Err(_) => return out_of_range(),
                                    }
                                } else {
                                    index as usize
                                };
                                if let Some(t) = ts.as_ref().get(index) {
                                    Some(match t {
                                        TypeOrTypeVarTuple::Type(t) => {
                                            Inferred::execute_db_type(i_s, t.clone())
                                        }
                                        TypeOrTypeVarTuple::TypeVarTuple(t) => unreachable!(),
                                    })
                                } else {
                                    return out_of_range();
                                }
                            })
                            .unwrap_or_else(|| {
                                Inferred::from_type(simplified_union_of_tuple_entries(i_s, ts))
                            })
                    }
                }
            }
            SliceTypeContent::Slices(slices) => {
                todo!()
            }
            SliceTypeContent::Slice(slice) => match &self.content.args {
                TupleTypeArguments::ArbitraryLength(t) => {
                    todo!()
                }
                args @ TupleTypeArguments::FixedLength(ts) => slice
                    .callback_on_tuple_indexes(i_s, ts, |start, end, step| {
                        Inferred::from_type(DbType::Tuple(Rc::new(TupleContent::new_fixed_length(
                            match step {
                                1 => ts[start..end].into(),
                                n if n > 1 => {
                                    ts[start..end].iter().step_by(n as usize).cloned().collect()
                                }
                                n if n < 0 => {
                                    todo!()
                                }
                                _ => unreachable!(),
                            },
                        ))))
                    })
                    .unwrap_or_else(|| {
                        Inferred::from_type(DbType::Tuple(Rc::new(
                            TupleContent::new_arbitrary_length(simplified_union_of_tuple_entries(
                                i_s, ts,
                            )),
                        )))
                    }),
            },
        }
    }
}

fn simplified_union_of_tuple_entries(
    i_s: &InferenceState,
    entries: &[TypeOrTypeVarTuple],
) -> DbType {
    let iter = || {
        entries.iter().map(|t_or| match t_or {
            TypeOrTypeVarTuple::Type(t) => t,
            TypeOrTypeVarTuple::TypeVarTuple(_) => unreachable!(),
        })
    };
    let highest_union_format_index = iter()
        .map(|t| t.highest_union_format_index())
        .max()
        .unwrap_or(0);
    simplified_union_from_iterators(
        i_s,
        iter().cloned().enumerate(),
        highest_union_format_index,
        false,
    )
}

fn tuple_add<'db>(
    i_s: &InferenceState<'db, '_>,
    args: &dyn Arguments<'db>,
    result_context: &mut ResultContext,
    on_type_error: OnTypeError<'db, '_>,
    bound: Option<&DbType>,
) -> Inferred {
    let DbType::Tuple(tuple) = bound.unwrap() else {
        unreachable!();
    };
    method_with_fallback(
        i_s,
        args,
        result_context,
        on_type_error,
        tuple.clone(),
        "__add__",
        tuple_add_internal,
        || Instance::new(i_s.db.python_state.tuple_class(i_s.db, tuple), None),
    )
}

fn tuple_add_internal<'db>(
    i_s: &InferenceState<'db, '_>,
    tuple1: Rc<TupleContent>,
    args: &dyn Arguments<'db>,
) -> Option<Inferred> {
    let first = args.maybe_single_positional_arg(i_s, &mut ResultContext::Unknown)?;
    if let TupleTypeArguments::FixedLength(ts1) = &tuple1.args {
        if let DbType::Tuple(tuple2) = first.as_type(i_s).as_ref() {
            if let TupleTypeArguments::FixedLength(ts2) = &tuple2.args {
                return Some(Inferred::from_type(DbType::Tuple(Rc::new(
                    TupleContent::new_fixed_length(ts1.iter().chain(ts2.iter()).cloned().collect()),
                ))));
            }
        }
    }
    None
}
fn tuple_mul<'db>(
    i_s: &InferenceState<'db, '_>,
    args: &dyn Arguments<'db>,
    result_context: &mut ResultContext,
    on_type_error: OnTypeError<'db, '_>,
    bound: Option<&DbType>,
) -> Inferred {
    let DbType::Tuple(tuple) = bound.unwrap() else {
        unreachable!();
    };
    method_with_fallback(
        i_s,
        args,
        result_context,
        on_type_error,
        tuple.clone(),
        "__mul__",
        tuple_mul_internal,
        || Instance::new(i_s.db.python_state.tuple_class(i_s.db, tuple), None),
    )
}

fn tuple_mul_internal<'db>(
    i_s: &InferenceState<'db, '_>,
    tuple: Rc<TupleContent>,
    args: &dyn Arguments<'db>,
) -> Option<Inferred> {
    let first = args.maybe_single_positional_arg(i_s, &mut ResultContext::Unknown)?;
    if let TupleTypeArguments::FixedLength(ts) = &tuple.args {
        first.run_on_int_literals(i_s, |int| {
            let int = int.max(0) as usize;
            if int > 10 {
                todo!("Do we really want extremely large tuples?")
            }
            Some(Inferred::from_type(DbType::Tuple(Rc::new(
                TupleContent::new_fixed_length(
                    ts.iter().cycle().take(int * ts.len()).cloned().collect(),
                ),
            ))))
        })
    } else {
        Some(Inferred::from_type(DbType::Tuple(tuple)))
    }
}
