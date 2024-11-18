use std::rc::Rc;

use parsa_python_cst::ParamKind;

use super::{
    AnyCause, CallableContent, CallableLike, CallableParam, CallableParams, ParamType,
    StarParamType, StarStarParamType, Type, TypeGuardInfo, UnionType,
};
use crate::{
    debug,
    inference_state::InferenceState,
    type_::{self, Tuple, TupleArgs, TupleUnpack},
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
                    (ArbitraryLen(t1), ArbitraryLen(t2)) => {
                        Type::Tuple(Tuple::new_arbitrary_length(t1.common_sub_type(i_s, t2)?))
                    }
                    (ArbitraryLen(t2), FixedLen(ts1)) | (FixedLen(ts1), ArbitraryLen(t2)) => {
                        let mut entries = vec![];
                        for t1 in ts1.iter() {
                            entries.push(t1.common_sub_type(i_s, t2)?)
                        }
                        Type::Tuple(Tuple::new_fixed_length(entries.into()))
                    }
                    (FixedLen(ts), WithUnpack(w_u)) | (WithUnpack(w_u), FixedLen(ts)) => {
                        let fetch_in_between =
                            ts.len().checked_sub(w_u.before.len() + w_u.after.len())?;
                        let mut entries = vec![];
                        let middle_t = match &w_u.unpack {
                            TupleUnpack::TypeVarTuple(_) => return None,
                            TupleUnpack::ArbitraryLen(t) => t,
                        };
                        let between = std::iter::repeat(middle_t).take(fetch_in_between);
                        for (t1, t2) in ts
                            .iter()
                            .zip(w_u.before.iter().chain(between).chain(w_u.after.iter()))
                        {
                            entries.push(t1.common_sub_type(i_s, t2)?)
                        }
                        Type::Tuple(Tuple::new_fixed_length(entries.into()))
                    }
                    (WithUnpack(w), ArbitraryLen(t)) | (ArbitraryLen(t), WithUnpack(w)) => {
                        Type::Tuple(Tuple::new(TupleArgs::WithUnpack(type_::WithUnpack {
                            before: w
                                .before
                                .iter()
                                .map(|t2| t2.common_sub_type(i_s, t))
                                .collect::<Option<_>>()?,
                            unpack: TupleUnpack::ArbitraryLen(match &w.unpack {
                                TupleUnpack::TypeVarTuple(_) => return None,
                                TupleUnpack::ArbitraryLen(t2) => t2.common_sub_type(i_s, t)?,
                            }),
                            after: w
                                .after
                                .iter()
                                .map(|t2| t2.common_sub_type(i_s, t))
                                .collect::<Option<_>>()?,
                        })))
                    }
                    (WithUnpack(w1), WithUnpack(w2)) => {
                        if w1 == w2 {
                            Type::Tuple(Tuple::new(WithUnpack(w1.clone())))
                        } else {
                            return None;
                        }
                    }
                })
            }
            (Type::TypedDict(td1), Type::TypedDict(td2)) => Some(td1.union(i_s, td2)),
            (Type::Callable(c1), _) => common_sub_type_for_callable_against_type(i_s, c1, other),
            (_, Type::Callable(c2)) => common_sub_type_for_callable_against_type(i_s, c2, self),
            (Type::Any(_), _) => Some(other.clone()),
            (_, Type::Any(_)) => Some(self.clone()),
            (Type::Type(t1), Type::Type(t2)) => {
                let new = t1.common_sub_type(i_s, t2)?;
                if &new == t1.as_ref() {
                    Some(self.clone())
                } else if &new == t2.as_ref() {
                    Some(other.clone())
                } else {
                    Some(Type::Type(Rc::new(new)))
                }
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
        /*
        let m = &mut Matcher::default().with_ignore_positional_param_names();
        if matches_params(i_s, m, self, other).bool() {
            Some(other.clone())
        } else if matches_params(i_s, m, other, self).bool() {
            Some(self.clone())
        } else {
        */
        match self {
            CallableParams::Simple(params1) => match &other {
                CallableParams::Simple(params2) => common_sub_type_params(i_s, params1, params2),
                CallableParams::Any(_) => Some(self.clone()),
                CallableParams::Never(_) => None,
            },
            CallableParams::Any(_) => Some(other.clone()),
            CallableParams::Never(_) => None,
        }
    }
}

fn common_sub_type_for_callable_against_type(
    i_s: &InferenceState,
    c1: &CallableContent,
    other: &Type,
) -> Option<Type> {
    match other.maybe_callable(i_s)? {
        CallableLike::Callable(c2) => {
            Some(Type::Callable(common_sub_type_for_callables(i_s, c1, &c2)))
        }
        CallableLike::Overload(_) => None, // TODO we should probably implement this
    }
}

fn common_sub_type_for_callables(
    i_s: &InferenceState,
    c1: &CallableContent,
    c2: &CallableContent,
) -> Rc<CallableContent> {
    if c1.kind != c2.kind {
        debug!("TODO when a callable kind does not match should there still be a subtype?");
        return i_s.db.python_state.any_callable_from_error.clone();
    }
    if let Some(return_type) = c1.return_type.common_sub_type(i_s, &c2.return_type) {
        if let Some(params) = c1.params.common_sub_type(i_s, &c2.params) {
            return Rc::new(CallableContent {
                name: None,
                class_name: None,
                defined_at: c1.defined_at,
                kind: c1.kind,
                type_vars: i_s.db.python_state.empty_type_var_likes.clone(),
                guard: common_sub_type_for_guard(i_s, &c1.guard, &c2.guard),
                is_abstract: c1.is_abstract && c2.is_abstract,
                is_final: c1.is_final && c2.is_final,
                no_type_check: false,
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
            let k1 = p1.type_.param_kind();
            if k1 != p2.type_.param_kind() {
                return None;
            }
            if p1.name != p2.name && !matches!(k1, ParamKind::PositionalOnly)
                || p1.has_default != p2.has_default
            {
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
        Some(CallableParams::new_simple(new_params.into()))
    } else {
        None
    }
}

fn common_sub_type_for_guard(
    _i_s: &InferenceState,
    _guard1: &Option<TypeGuardInfo>,
    _guard2: &Option<TypeGuardInfo>,
) -> Option<TypeGuardInfo> {
    // For now do nothing.
    None
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
                result.union_in_place(found)
            } else {
                result = Some(found)
            }
        }
    }
    result
}
