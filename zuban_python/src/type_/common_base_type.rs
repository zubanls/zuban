use std::{borrow::Cow, rc::Rc};

use parsa_python_cst::ParamKind;

use super::{
    CallableContent, CallableParam, CallableParams, ClassGenerics, GenericItem, GenericsList,
    NeverCause, ParamType, ParamTypeDetails, StarParamType, StarStarParamType, Tuple, TupleArgs,
    TupleUnpack, Type, TypeGuardInfo, TypeVarLike, Variance, WithUnpack,
};
use crate::{
    database::Database,
    inference_state::InferenceState,
    matching::{Match, Matcher},
    type_::CallableLike,
    type_helpers::{Class, TypeOrClass},
};

impl Type {
    pub fn common_base_type(&self, i_s: &InferenceState, other: &Self) -> Type {
        let check_both_sides = |t1: &_, t2: &Type| match t1 {
            /*
            Type::Union(u) if u.iter().any(|t| matches!(t, Type::None)) => {
                return self.clone().union(i_s.db, other.clone()).into_type()
            }
            */
            Type::None | Type::Union(_) => Some(self.simplified_union(i_s, other)),
            Type::Any(cause) => Some(Type::Any(*cause)),
            Type::Never(_) => Some(t2.clone()),
            _ => None,
        };

        if let Some(new) = check_both_sides(self, other) {
            return new;
        }
        if let Some(new) = check_both_sides(other, self) {
            return new;
        }
        for (_, c1) in self.mro(i_s.db) {
            for (_, c2) in other.mro(i_s.db) {
                match &c1 {
                    TypeOrClass::Type(t1) => match c2 {
                        TypeOrClass::Class(c2) => {
                            if let Some(base) = class_against_non_class(i_s, c2, t1) {
                                return base;
                            }
                        }
                        TypeOrClass::Type(t2) => {
                            if let Some(base) = common_base_type_for_non_class(i_s, t1, &t2) {
                                return base;
                            }
                        }
                    },
                    TypeOrClass::Class(c1) => match c2 {
                        TypeOrClass::Class(c2) => {
                            if let Some(t) = common_base_class(i_s, *c1, c2) {
                                return t;
                            }
                        }
                        TypeOrClass::Type(t2) => {
                            if let Some(base) = class_against_non_class(i_s, *c1, &t2) {
                                return base;
                            }
                        }
                    },
                }
            }
        }
        if let Some(first) = self.maybe_class(i_s.db) {
            if first.is_protocol(i_s.db)
                && first
                    .check_protocol_match(i_s, &mut Matcher::default(), other)
                    .bool()
            {
                return self.clone();
            }
        }
        if let Some(second) = other.maybe_class(i_s.db) {
            if second.is_protocol(i_s.db)
                && second
                    .check_protocol_match(i_s, &mut Matcher::default(), self)
                    .bool()
            {
                return other.clone();
            }
        }
        // Needed for protocols, because they don't inherit from object.
        i_s.db.python_state.object_type()
    }
}

pub fn common_base_type<'x, I: Iterator<Item = &'x Type>>(i_s: &InferenceState, mut ts: I) -> Type {
    if let Some(first) = ts.next() {
        let mut result = Cow::Borrowed(first);
        for t in ts {
            result = Cow::Owned(result.common_base_type(i_s, t));
        }
        result.into_owned()
    } else {
        Type::Never(NeverCause::Other)
    }
}

fn check_promotion(db: &Database, promote: Class, other: Class) -> Option<Type> {
    if let Some(promote_to) = promote.class_storage.promote_to.get() {
        let promoted = Class::from_non_generic_link(db, promote_to);
        if promoted.node_ref == other.node_ref {
            Some(Type::new_class(
                promoted.node_ref.as_link(),
                ClassGenerics::None,
            ))
        } else {
            check_promotion(db, promoted, other)
        }
    } else {
        None
    }
}

fn common_base_class(i_s: &InferenceState, c1: Class, c2: Class) -> Option<Type> {
    common_base_class_basic(i_s, c1, c2)
        .or_else(|| check_promotion(i_s.db, c1, c2))
        .or_else(|| check_promotion(i_s.db, c2, c1))
}
fn common_base_class_basic(i_s: &InferenceState, c1: Class, c2: Class) -> Option<Type> {
    if c1.node_ref != c2.node_ref {
        return None;
    }
    let mut generics = vec![];
    for ((type_var_like, generic1), generic2) in c1
        .type_vars(i_s)
        .iter()
        .zip(c1.generics().iter(i_s.db))
        .zip(c2.generics().iter(i_s.db))
    {
        match type_var_like {
            TypeVarLike::TypeVar(type_var) => {
                let inner_t1 = generic1.expect_type_argument();
                let inner_t2 = generic2.expect_type_argument();
                match type_var.variance {
                    Variance::Invariant => {
                        let matches = inner_t1.is_simple_same_type(i_s, &inner_t2);
                        // TODO this with_any check is not very precise and a structure
                        // like T[Any, int] & T[int, Any] should become T[Any, Any]
                        match matches {
                            Match::True { with_any: false } => {
                                generics.push(GenericItem::TypeArg(inner_t1.into_owned()));
                            }
                            Match::True { with_any: true } => {
                                generics.push(GenericItem::TypeArg(inner_t2.into_owned()));
                            }
                            _ => return None,
                        }
                    }
                    Variance::Covariant => {
                        generics.push(GenericItem::TypeArg(
                            inner_t1.common_base_type(i_s, &inner_t2),
                        ));
                    }
                    Variance::Contravariant => {
                        if let Some(t) = inner_t1.common_sub_type(i_s, &inner_t2) {
                            generics.push(GenericItem::TypeArg(t));
                        } else {
                            return None;
                        }
                    }
                }
            }
            TypeVarLike::TypeVarTuple(_) => todo!(),
            TypeVarLike::ParamSpec(spec) => {
                // TODO Common base types of param specs should united somehow?
                generics.push(generic1.into_generic_item(i_s.db));
            }
        }
    }
    Some(Type::new_class(
        c1.node_ref.as_link(),
        ClassGenerics::List(GenericsList::generics_from_vec(generics)),
    ))
}

fn class_against_non_class(i_s: &InferenceState, c1: Class, t2: &Type) -> Option<Type> {
    None
}

fn common_base_type_for_non_class(
    i_s: &InferenceState,
    type1: &Type,
    type2: &Type,
) -> Option<Type> {
    match type1 {
        Type::Callable(c1) => {
            // TODO this should also be done for function/callable and callable/function and
            // not only callable/callable
            if let Some(CallableLike::Callable(c2)) = type2.maybe_callable(i_s) {
                return Some(common_base_for_callables(i_s, c1, &c2));
            }
        }
        Type::Tuple(tup1) => return common_base_for_tuple_against_type(i_s, tup1, type2),
        Type::NamedTuple(nt1) => {
            if let Type::NamedTuple(nt2) = type2 {
                if nt1.__new__.defined_at == nt2.__new__.defined_at {
                    return Some(Type::NamedTuple(nt1.clone()));
                }
            }
            return common_base_for_tuple_against_type(i_s, &nt1.as_tuple(), type2);
        }
        Type::TypedDict(td1) => {
            if let Type::TypedDict(td2) = &type2 {
                return Some(Type::TypedDict(td1.intersection(i_s, td2)));
            }
        }
        Type::Type(t1) => match type2 {
            Type::Type(t2) => return Some(Type::Type(Rc::new(t1.common_base_type(i_s, t2)))),
            Type::Callable(c2) => return common_base_type_for_non_class(i_s, type2, type1),
            _ => (),
        },
        _ => {
            if type1.is_simple_same_type(i_s, type2).bool() {
                return Some(type1.clone());
            }
        }
    }
    None
}

fn common_base_for_callables(
    i_s: &InferenceState,
    c1: &CallableContent,
    c2: &CallableContent,
) -> Type {
    if !c1.kind.is_same_base_kind(c2.kind) {
        todo!("{:?} {:?}", c1.kind, c2.kind)
    }
    match &c1.params {
        CallableParams::Simple(params1) => match &c2.params {
            CallableParams::Simple(params2) => {
                if let Some(params) = common_params(i_s, params1, params2) {
                    return Type::Callable(Rc::new(CallableContent {
                        name: None,
                        class_name: None,
                        defined_at: c1.defined_at,
                        kind: c1.kind,
                        // TODO why do we just use the first type vars here???
                        type_vars: c1.type_vars.clone(),
                        guard: common_base_guard(i_s, &c1.guard, &c2.guard),
                        is_abstract: c1.is_abstract && c2.is_abstract,
                        params,
                        return_type: c1.return_type.common_base_type(i_s, &c2.return_type),
                    }));
                }
            }
            CallableParams::WithParamSpec(_, _) => (),
            CallableParams::Any(_) | CallableParams::Never(_) => todo!(),
        },
        CallableParams::WithParamSpec(pre1, spec1) => match &c2.params {
            CallableParams::WithParamSpec(pre2, spec2) => {
                if !pre1.is_empty() || !pre2.is_empty() {
                    todo!()
                }
                if spec1 == spec2 {
                    return Type::Callable(Rc::new(CallableContent {
                        name: None,
                        class_name: None,
                        defined_at: c1.defined_at,
                        kind: c1.kind,
                        type_vars: c1.type_vars.clone(),
                        guard: common_base_guard(i_s, &c1.guard, &c2.guard),
                        is_abstract: c1.is_abstract && c2.is_abstract,
                        params: CallableParams::WithParamSpec(pre1.clone(), spec1.clone()),
                        return_type: c1.return_type.common_base_type(i_s, &c2.return_type),
                    }));
                }
            }
            _ => (),
        },
        CallableParams::Any(_) | CallableParams::Never(_) => todo!(),
    }
    i_s.db.python_state.function_type()
}

fn common_params<'x>(
    i_s: &InferenceState,
    params1: &'x [CallableParam],
    params2: &'x [CallableParam],
) -> Option<CallableParams> {
    fn maybe_unpack_typed_dict_params<'y: 'z, 'z>(
        i_s: &InferenceState,
        params: &'y [CallableParam],
        td_params: &'z mut Vec<CallableParam>,
    ) -> Option<(usize, impl Iterator<Item = &'z CallableParam>)> {
        if let Some(p) = params.last() {
            if let ParamType::StarStar(StarStarParamType::UnpackTypedDict(td)) = &p.type_ {
                let mut params = params.iter();
                params.next_back();
                *td_params = td
                    .members(i_s.db)
                    .iter()
                    .map(|m| m.as_keyword_param())
                    .collect();
                return Some((
                    params.len() + td_params.len(),
                    params.chain(td_params.iter()),
                ));
            }
        }
        None
    }
    let mut new1 = vec![];
    let mut new2 = vec![];
    let result = if let Some((len_p1, new_p1)) =
        maybe_unpack_typed_dict_params(i_s, params1, &mut new1)
    {
        if let Some((len_p2, new_p2)) = maybe_unpack_typed_dict_params(i_s, params2, &mut new2) {
            common_params_by_iterable(i_s, len_p1, len_p2, new_p1, new_p2)
        } else {
            common_params_by_iterable(i_s, len_p1, params2.len(), new_p1, params2.iter())
        }
    } else if let Some((len_p2, new_p2)) = maybe_unpack_typed_dict_params(i_s, params2, &mut new2) {
        common_params_by_iterable(i_s, params1.len(), len_p2, params1.iter(), new_p2)
    } else {
        common_params_by_iterable(
            i_s,
            params1.len(),
            params2.len(),
            params1.iter(),
            params2.iter(),
        )
    };
    result
}

fn common_params_by_iterable<'x>(
    i_s: &InferenceState,
    p1_len: usize,
    p2_len: usize,
    params1: impl Iterator<Item = &'x CallableParam>,
    params2: impl Iterator<Item = &'x CallableParam>,
) -> Option<CallableParams> {
    let mut new_params = vec![];
    if p1_len == p2_len {
        for (p1, p2) in params1.zip(params2) {
            let mut kind = p1.type_.param_kind();
            let p2_kind = p2.type_.param_kind();
            let p1_name = p1.name.as_ref().map(|n| n.as_str(i_s.db));
            let p2_name = p2.name.as_ref().map(|n| n.as_str(i_s.db));
            if p1_name != p2_name {
                if matches!(
                    kind,
                    ParamKind::PositionalOnly | ParamKind::PositionalOrKeyword
                ) && matches!(
                    p2_kind,
                    ParamKind::PositionalOnly | ParamKind::PositionalOrKeyword
                ) {
                    kind = ParamKind::PositionalOnly;
                } else {
                    return None;
                }
            }
            let new_param = |type_| CallableParam {
                type_,
                name: (p1_name == p2_name).then(|| p1.name.clone()).flatten(),
                has_default: p1.has_default & p2.has_default,
            };

            let t1 = match p1.type_.details() {
                ParamTypeDetails::Type(t) => t,
                ParamTypeDetails::UnpackedTuple(u1) => match p2.type_.details() {
                    ParamTypeDetails::UnpackedTuple(u2) => {
                        new_params.push(new_param(ParamType::Star(StarParamType::UnpackedTuple(
                            common_base_for_tuples(i_s, &u1, &u2),
                        ))));
                        continue;
                    }
                    _ => return None,
                },
                _ => return None,
            };
            let t2 = p2.type_.maybe_type()?;
            let new_t = t1.common_sub_type(i_s, t2)?;
            new_params.push(new_param(match &kind {
                ParamKind::PositionalOnly => ParamType::PositionalOnly(new_t),
                ParamKind::PositionalOrKeyword => ParamType::PositionalOrKeyword(new_t),
                ParamKind::KeywordOnly => ParamType::KeywordOnly(new_t),
                ParamKind::Star => ParamType::Star(StarParamType::ArbitraryLen(new_t)),
                ParamKind::StarStar => ParamType::StarStar(StarStarParamType::ValueType(new_t)),
            }));
        }
        Some(CallableParams::Simple(new_params.into()))
    } else {
        None
    }
}

fn common_base_guard(
    i_s: &InferenceState,
    guard1: &Option<TypeGuardInfo>,
    guard2: &Option<TypeGuardInfo>,
) -> Option<TypeGuardInfo> {
    // For now do nothing.
    None
}

fn common_base_for_tuple_against_type(
    i_s: &InferenceState,
    tup1: &Tuple,
    t2: &Type,
) -> Option<Type> {
    Some(match t2 {
        Type::Tuple(tup2) => Type::Tuple(common_base_for_tuples(i_s, tup1, tup2)),
        Type::NamedTuple(nt2) => Type::Tuple(common_base_for_tuples(i_s, tup1, &nt2.as_tuple())),
        _ => return None,
    })
}

fn common_base_for_tuples(i_s: &InferenceState, tup1: &Tuple, tup2: &Tuple) -> Rc<Tuple> {
    Tuple::new(tup1.args.common_base_type(i_s, &tup2.args))
}

impl TupleArgs {
    pub fn common_base_type(&self, i_s: &InferenceState, tup2: &TupleArgs) -> TupleArgs {
        match &tup2 {
            TupleArgs::FixedLen(ts2) => {
                let mut new_args = self.clone();
                common_base_type_of_type_var_tuple_with_items(&mut new_args, i_s, ts2.iter());
                new_args
            }
            TupleArgs::ArbitraryLen(t2) => match self {
                TupleArgs::FixedLen(ts1) => {
                    let mut new_args = tup2.clone();
                    common_base_type_of_type_var_tuple_with_items(&mut new_args, i_s, ts1.iter());
                    new_args
                }
                TupleArgs::ArbitraryLen(t1) => todo!(),
                TupleArgs::WithUnpack(_) => todo!(),
            },
            TupleArgs::WithUnpack(w1) => match self {
                TupleArgs::FixedLen(ts1) => todo!(),
                TupleArgs::ArbitraryLen(t1) => todo!(),
                TupleArgs::WithUnpack(w2) => {
                    if w1.before.len() != w2.before.len() || w1.after.len() != w2.after.len() {
                        todo!()
                    }
                    let new_unpack = match (&w1.unpack, &w2.unpack) {
                        (TupleUnpack::ArbitraryLen(t1), TupleUnpack::ArbitraryLen(t2)) => {
                            TupleUnpack::ArbitraryLen(
                                t1.common_sub_type(i_s, t2)
                                    .unwrap_or(Type::Never(NeverCause::Other)),
                            )
                        }
                        (TupleUnpack::TypeVarTuple(tvt1), TupleUnpack::TypeVarTuple(tvt2)) => {
                            if tvt1.in_definition == tvt2.in_definition && tvt1.index == tvt2.index
                            {
                                TupleUnpack::TypeVarTuple(tvt1.clone())
                            } else {
                                todo!()
                            }
                        }
                        _ => todo!("{w1:?} {w2:?}"),
                    };
                    TupleArgs::WithUnpack(WithUnpack {
                        before: w1
                            .before
                            .iter()
                            .zip(w2.before.iter())
                            .map(|(t1, t2)| {
                                t1.common_sub_type(i_s, t2)
                                    .unwrap_or(Type::Never(NeverCause::Other))
                            })
                            .collect(),
                        unpack: new_unpack,
                        after: w1
                            .after
                            .iter()
                            .zip(w2.after.iter())
                            .map(|(t1, t2)| {
                                t1.common_sub_type(i_s, t2)
                                    .unwrap_or(Type::Never(NeverCause::Other))
                            })
                            .collect(),
                    })
                }
            },
        }
    }
}

pub fn common_base_type_of_type_var_tuple_with_items<'x, I: ExactSizeIterator<Item = &'x Type>>(
    args: &mut TupleArgs,
    i_s: &InferenceState,
    items: I,
) {
    match args {
        TupleArgs::FixedLen(calc_ts) => {
            if items.len() == calc_ts.len() {
                let mut new = vec![];
                for (t1, t2) in calc_ts.iter().zip(items) {
                    new.push(t1.common_base_type(i_s, t2));
                }
                *calc_ts = new.into();
            } else {
                // We use map to make an iterator with covariant lifetimes.
                #[allow(clippy::map_identity)]
                let t = common_base_type(i_s, calc_ts.iter().chain(items.map(|x| x)));
                *args = TupleArgs::ArbitraryLen(Box::new(t));
            }
        }
        TupleArgs::WithUnpack(_) => todo!(),
        TupleArgs::ArbitraryLen(calc_t) => {
            if items.len() == 0 {
                // args is already ok, because we have an empty tuple here that can be anything.
                return;
            }
            let base = common_base_type(i_s, items).common_base_type(i_s, calc_t);
            *args = TupleArgs::ArbitraryLen(Box::new(base));
        }
    }
}
