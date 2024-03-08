use std::rc::Rc;

use parsa_python_ast::ParamKind;

use super::{
    AnyCause, CallableContent, CallableParam, CallableParams, ParamType, StarParamType,
    StarStarParamType, Type, UnionType,
};
use crate::{
    inference_state::InferenceState,
    type_::{Tuple, TupleArgs},
};

impl Type {
    pub fn common_sub_type(&self, i_s: &InferenceState, other: &Self) -> Option<Type> {
        match (self, other) {
            (Type::Union(union), _) => common_sub_type_for_union(i_s, union, other),
            (_, Type::Union(union)) => common_sub_type_for_union(i_s, union, self),
            (Type::Tuple(tup1), Type::Tuple(tup2)) => {
                use TupleArgs::*;
                Some(match (&tup1.args, &tup2.args) {
                    (FixedLen(ts1), FixedLen(ts2)) => {
                        if ts1.len() != ts2.len() {
                            return None;
                        }
                        let mut entries = vec![];
                        for (t1, t2) in ts1.iter().zip(ts2.iter()) {
                            entries.push(t1.common_sub_type(i_s, t2)?)
                        }
                        Type::Tuple(Tuple::new_fixed_length(entries.into()))
                    }
                    (ArbitraryLen(t1), ArbitraryLen(t2)) => t1.common_sub_type(i_s, t2)?,
                    (ArbitraryLen(t2), FixedLen(ts1)) | (FixedLen(ts1), ArbitraryLen(t2)) => {
                        let mut entries = vec![];
                        for t1 in ts1.iter() {
                            entries.push(t1.common_sub_type(i_s, &t2)?)
                        }
                        Type::Tuple(Tuple::new_fixed_length(entries.into()))
                    }
                    _ => todo!(),
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

impl CallableParams {
    pub fn common_sub_type(
        &self,
        i_s: &InferenceState,
        other: &CallableParams,
    ) -> Option<CallableParams> {
        match &self {
            CallableParams::Simple(params1) => match &other {
                CallableParams::Simple(params2) => common_sub_type_params(i_s, &params1, &params2),
                CallableParams::WithParamSpec(_, _) => todo!(),
                CallableParams::Any(_) => todo!(),
            },
            CallableParams::WithParamSpec(_, _) => todo!(),
            CallableParams::Any(_) => todo!(),
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
    if let Some(return_type) = c1.return_type.common_sub_type(i_s, &c2.return_type) {
        if let Some(params) = c1.params.common_sub_type(i_s, &c2.params) {
            return Rc::new(CallableContent {
                name: None,
                class_name: None,
                defined_at: c1.defined_at,
                kind: c1.kind,
                type_vars: i_s.db.python_state.empty_type_var_likes.clone(),
                params,
                return_type,
            });
        }
    }
    Rc::new(CallableContent::new_any(
        i_s.db.python_state.empty_type_var_likes.clone(),
        AnyCause::Todo,
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
            if p1.type_.param_kind() != p2.type_.param_kind() {
                return None;
            }
            let t1 = p1.type_.maybe_positional_type()?;
            let t2 = p2.type_.maybe_positional_type()?;
            let new_t = t1.common_base_type(i_s, t2);
            new_params.push(CallableParam {
                type_: match &p1.type_.param_kind() {
                    ParamKind::PositionalOnly => ParamType::PositionalOnly(new_t),
                    ParamKind::PositionalOrKeyword => ParamType::PositionalOrKeyword(new_t),
                    ParamKind::KeywordOnly => ParamType::KeywordOnly(new_t),
                    ParamKind::Star => ParamType::Star(StarParamType::ArbitraryLen(new_t)),
                    ParamKind::StarStar => ParamType::StarStar(StarStarParamType::ValueType(new_t)),
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

fn common_sub_type_for_union(
    i_s: &InferenceState,
    union: &UnionType,
    other: &Type,
) -> Option<Type> {
    let mut result: Option<Type> = None;
    for t in union.iter() {
        if let Some(found) = t.common_sub_type(i_s, other) {
            if let Some(result) = &mut result {
                result.union_in_place(i_s.db, found)
            } else {
                result = Some(found)
            }
        }
    }
    result
}
