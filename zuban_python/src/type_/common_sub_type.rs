use std::rc::Rc;

use parsa_python_ast::ParamKind;

use crate::{
    inference_state::InferenceState,
    type_::{TupleContent, TupleTypeArguments, TypeOrTypeVarTuple},
};

use super::{
    CallableContent, CallableParam, CallableParams, DoubleStarredParamSpecific, ParamSpecific,
    StarredParamSpecific, Type,
};

impl Type {
    pub fn common_sub_type(&self, i_s: &InferenceState, other: &Self) -> Option<Type> {
        match (self, other) {
            (Type::Union(union), _) => {
                for t in union.iter() {
                    // TODO what about multiple items?
                    if let Some(found) = t.common_sub_type(i_s, other) {
                        return Some(found);
                    }
                }
                None
            }
            (_, Type::Union(union)) => {
                for t in union.iter() {
                    // TODO what about multiple items?
                    if let Some(found) = t.common_sub_type(i_s, self) {
                        return Some(found);
                    }
                }
                None
            }
            (Type::Tuple(tup1), Type::Tuple(tup2)) => {
                if tup1.args.has_type_var_tuple().is_some()
                    || tup2.args.has_type_var_tuple().is_some()
                {
                    todo!()
                }
                use TupleTypeArguments::*;
                Some(match (&tup1.args, &tup2.args) {
                    (FixedLength(ts1), FixedLength(ts2)) => {
                        if ts1.len() != ts2.len() {
                            return None;
                        }
                        let mut entries = vec![];
                        for (t1, t2) in ts1.iter().zip(ts2.iter()) {
                            match (t1, t2) {
                                (TypeOrTypeVarTuple::Type(t1), TypeOrTypeVarTuple::Type(t2)) => {
                                    entries.push(TypeOrTypeVarTuple::Type(
                                        t1.common_sub_type(i_s, t2)?,
                                    ))
                                }
                                _ => todo!(),
                            }
                        }
                        Type::Tuple(Rc::new(TupleContent::new_fixed_length(entries.into())))
                    }
                    (ArbitraryLength(t1), ArbitraryLength(t2)) => t1.common_sub_type(i_s, t2)?,
                    (ArbitraryLength(t2), FixedLength(ts1))
                    | (FixedLength(ts1), ArbitraryLength(t2)) => {
                        let mut entries = vec![];
                        for type_or1 in ts1.iter() {
                            if let TypeOrTypeVarTuple::Type(t1) = type_or1 {
                                entries
                                    .push(TypeOrTypeVarTuple::Type(t1.common_sub_type(i_s, &t2)?))
                            } else {
                                return None;
                            }
                        }
                        Type::Tuple(Rc::new(TupleContent::new_fixed_length(entries.into())))
                    }
                })
            }
            (Type::TypedDict(td1), Type::TypedDict(td2)) => Some(td1.union(i_s, &td2)),
            (Type::Callable(c1), Type::Callable(c2)) => {
                Some(Type::Callable(common_sub_type_for_callables(i_s, c1, c2)))
            }
            _ => {
                if self.is_simple_sub_type_of(i_s, other).bool() {
                    Some(self.clone())
                } else if other.is_simple_sub_type_of(i_s, self).bool() {
                    Some(other.clone())
                } else {
                    None
                }
            }
        }
    }
}

fn common_sub_type_for_callables(
    i_s: &InferenceState,
    c1: &CallableContent,
    c2: &CallableContent,
) -> Rc<CallableContent> {
    if c1.kind != c2.kind {
        todo!()
    }
    match &c1.params {
        CallableParams::Simple(params1) => match &c2.params {
            CallableParams::Simple(params2) => {
                if let Some(params) = common_sub_type_params(i_s, &params1, &params2) {
                    if let Some(result_type) = c1.result_type.common_sub_type(i_s, &c2.result_type)
                    {
                        return Rc::new(CallableContent {
                            name: None,
                            class_name: None,
                            defined_at: c1.defined_at,
                            kind: c1.kind,
                            type_vars: i_s.db.python_state.empty_type_var_likes.clone(),
                            params,
                            result_type,
                        });
                    }
                }
            }
            CallableParams::WithParamSpec(_, _) => todo!(),
            CallableParams::Any => todo!(),
        },
        CallableParams::WithParamSpec(_, _) => todo!(),
        CallableParams::Any => todo!(),
    }
    Rc::new(CallableContent::new_any(
        i_s.db.python_state.empty_type_var_likes.clone(),
    ))
    //return i_s.db.python_state.function_type();
}

fn common_sub_type_params(
    i_s: &InferenceState,
    params1: &[CallableParam],
    params2: &[CallableParam],
) -> Option<CallableParams> {
    if params1.len() == params2.len() {
        let mut new_params = vec![];
        for (p1, p2) in params1.iter().zip(params2.iter()) {
            if p1.name != p2.name || p1.has_default != p2.has_default {
                return None;
            }
            if p1.param_specific.param_kind() != p2.param_specific.param_kind() {
                return None;
            }
            let t1 = p1.param_specific.maybe_positional_type()?;
            let t2 = p2.param_specific.maybe_positional_type()?;
            let new_t = t1.common_base_type(i_s, t2);
            new_params.push(CallableParam {
                param_specific: match &p1.param_specific.param_kind() {
                    ParamKind::PositionalOnly => ParamSpecific::PositionalOnly(new_t),
                    ParamKind::PositionalOrKeyword => ParamSpecific::PositionalOrKeyword(new_t),
                    ParamKind::KeywordOnly => ParamSpecific::KeywordOnly(new_t),
                    ParamKind::Starred => {
                        ParamSpecific::Starred(StarredParamSpecific::ArbitraryLength(new_t))
                    }
                    ParamKind::DoubleStarred => {
                        ParamSpecific::DoubleStarred(DoubleStarredParamSpecific::ValueType(new_t))
                    }
                },
                name: p1.name.clone(),
                has_default: p1.has_default,
            });
        }
        Some(CallableParams::Simple(new_params.into()))
    } else {
        todo!()
    }
}
