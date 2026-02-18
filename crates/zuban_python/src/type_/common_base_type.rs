use std::sync::Arc;

use parsa_python_cst::ParamKind;

use super::{
    CallableContent, CallableParam, CallableParams, ClassGenerics, GenericItem, GenericsList,
    NeverCause, ParamType, ParamTypeDetails, StarParamType, StarStarParamType, Tuple, TupleArgs,
    Type, TypeGuardInfo, TypeVarLike, Variance,
};
use crate::{
    database::Database,
    inference_state::InferenceState,
    match_::Match,
    matching::{CheckedTypeRecursion, Matcher},
    type_::{AnyCause, CallableLike, ParamSpecArg, TupleUnpack, TypeArgs, WithUnpack},
    type_helpers::{Class, TypeOrClass},
};

impl Type {
    pub fn gather_types(&self, i_s: &InferenceState, other: &Self) -> Type {
        self.gather_types_maybe_with_joins(i_s, other, i_s.flags().use_joins)
    }

    pub fn gather_types_maybe_with_joins(
        &self,
        i_s: &InferenceState,
        other: &Self,
        use_joins: bool,
    ) -> Type {
        if use_joins {
            self.common_base_type(i_s, other)
        } else {
            self.simplified_union(i_s, other)
        }
    }

    pub fn common_base_type(&self, i_s: &InferenceState, other: &Self) -> Type {
        self.common_base_type_internal(i_s, other, None)
    }

    fn common_base_type_internal(
        &self,
        i_s: &InferenceState,
        other: &Self,
        checked_recursions: Option<CheckedTypeRecursion>,
    ) -> Type {
        let checked_recursions = CheckedTypeRecursion {
            current: (self, other),
            previous: checked_recursions.as_ref(),
        };
        if checked_recursions.is_cycle() {
            return i_s.db.python_state.object_type();
        }

        let check_both_sides = |t1: &_, t2: &Type, is_reverse| match t1 {
            /*
            Type::Union(u) if u.iter().any(|t| matches!(t, Type::None)) => {
                return self.clone().union(i_s.db, other.clone()).into_type()
            }
            */
            Type::None | Type::Union(_) => {
                if other.is_object(i_s.db) {
                    Some(other.clone())
                } else {
                    Some(self.simplified_union(i_s, other))
                }
            }
            Type::Any(AnyCause::UnknownTypeParam) => Some(t2.clone()),
            Type::Any(cause) => Some(Type::Any(*cause)),
            Type::Never(_) => Some(t2.clone()),
            Type::Callable(c1) => {
                common_base_for_callable_against_type(i_s, c1, t2, checked_recursions)
            }
            Type::EnumMember(_) => match t2 {
                Type::EnumMember(_) | Type::Enum(_) => {
                    if is_reverse {
                        Some(t2.simplified_union(i_s, t1))
                    } else {
                        Some(t1.simplified_union(i_s, t2))
                    }
                }
                _ => None,
            },
            Type::LiteralString { .. } if !matches!(t2, Type::LiteralString { .. }) => {
                Some(i_s.db.python_state.str_type().common_base_type_internal(
                    i_s,
                    t2,
                    Some(checked_recursions),
                ))
            }
            Type::RecursiveType(r1) => Some({
                let mut t1 = r1.calculated_type(i_s.db);
                let mut t2 = t2;
                if is_reverse {
                    (t1, t2) = (t2, t1);
                }
                t1.common_base_type_internal(i_s, t2, Some(checked_recursions))
            }),
            _ => None,
        };

        if let Some(new) = check_both_sides(self, other, false) {
            return new;
        }
        if let Some(new) = check_both_sides(other, self, true) {
            return new;
        }
        for (_, c1) in self.mro(i_s.db) {
            for (_, c2) in other.mro(i_s.db) {
                match &c1 {
                    TypeOrClass::Type(t1) => match c2 {
                        TypeOrClass::Class(_) => (),
                        TypeOrClass::Type(t2) => {
                            if let Some(base) =
                                common_base_type_for_non_class(i_s, t1, &t2, checked_recursions)
                            {
                                return base;
                            }
                        }
                    },
                    TypeOrClass::Class(c1) => match c2 {
                        TypeOrClass::Class(c2) => {
                            if let Some(t) = common_base_class(i_s, *c1, c2, checked_recursions)
                                // Protocols are handled later.
                                && !(c1.is_object_class(i_s.db)
                                    && (self.is_protocol(i_s.db) || other.is_protocol(i_s.db)))
                            {
                                return t;
                            }
                        }
                        TypeOrClass::Type(_) => (),
                    },
                }
            }
        }
        if let Some(first) = self.maybe_class(i_s.db)
            && first.is_protocol(i_s.db)
            && first
                .check_protocol_match(i_s, &mut Matcher::default(), other)
                .bool()
        {
            return self.clone();
        }
        if let Some(second) = other.maybe_class(i_s.db)
            && second.is_protocol(i_s.db)
            && second
                .check_protocol_match(i_s, &mut Matcher::default(), self)
                .bool()
        {
            return other.clone();
        }
        // Needed for protocols, because they don't inherit from object.
        i_s.db.python_state.object_type()
    }

    pub fn is_protocol(&self, db: &Database) -> bool {
        self.maybe_class(db).is_some_and(|c| c.is_protocol(db))
    }
}

fn check_promotion(db: &Database, promote: Class, other: Class) -> Option<Type> {
    if let Some(promote_to) = promote.use_cached_class_infos(db).promote_to() {
        let promoted = Class::from_non_generic_link(db, promote_to);
        if promoted.node_ref == other.node_ref {
            Some(Type::new_class(
                promoted.node_ref.as_link(),
                ClassGenerics::new_none(),
            ))
        } else {
            check_promotion(db, promoted, other)
        }
    } else {
        None
    }
}

fn common_base_class(
    i_s: &InferenceState,
    c1: Class,
    c2: Class,
    checked_recursions: CheckedTypeRecursion,
) -> Option<Type> {
    common_base_class_basic(i_s, c1, c2, checked_recursions)
        .or_else(|| check_promotion(i_s.db, c1, c2))
        .or_else(|| check_promotion(i_s.db, c2, c1))
}

fn common_base_class_basic(
    i_s: &InferenceState,
    c1: Class,
    c2: Class,
    checked_recursions: CheckedTypeRecursion,
) -> Option<Type> {
    if c1.node_ref != c2.node_ref {
        return None;
    }
    let type_vars = c1.type_vars(i_s);
    if type_vars.is_empty() {
        // If there are no generics, return early
        return Some(c1.as_type(i_s.db));
    }
    let mut generics = vec![];
    for ((type_var_like, generic1), generic2) in type_vars
        .iter()
        .zip(c1.generics().iter(i_s.db))
        .zip(c2.generics().iter(i_s.db))
    {
        match type_var_like {
            TypeVarLike::TypeVar(type_var) => {
                let inner_t1 = generic1.expect_type_argument();
                let inner_t2 = generic2.expect_type_argument();
                match type_var.inferred_variance(i_s.db, &c1) {
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
                        generics.push(GenericItem::TypeArg(inner_t1.common_base_type_internal(
                            i_s,
                            &inner_t2,
                            Some(checked_recursions),
                        )));
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
            TypeVarLike::TypeVarTuple(_) => {
                let ts1 = generic1.expect_type_arguments();
                let ts2 = generic2.expect_type_arguments();
                let new = ts1
                    .args
                    .common_base_type(i_s, &ts2.args, Some(checked_recursions));
                generics.push(GenericItem::TypeArgs(TypeArgs::new(new)));
            }
            TypeVarLike::ParamSpec(_) => {
                let p1 = generic1.expect_param_spec_arg();
                let p2 = generic2.expect_param_spec_arg();
                if p1.type_vars.is_some() || p2.type_vars.is_some() {
                    return None;
                }
                let new = p1
                    .params
                    .common_base_type(i_s, &p2.params, Some(checked_recursions))?;
                generics.push(GenericItem::ParamSpecArg(ParamSpecArg::new(new, None)));
            }
        }
    }
    Some(Type::new_class(
        c1.node_ref.as_link(),
        ClassGenerics::List(GenericsList::generics_from_vec(generics)),
    ))
}

fn common_base_type_for_non_class(
    i_s: &InferenceState,
    type1: &Type,
    type2: &Type,
    checked_recursions: CheckedTypeRecursion,
) -> Option<Type> {
    match type1 {
        Type::Tuple(tup1) => {
            return common_base_for_tuple_against_type(i_s, tup1, type2, checked_recursions);
        }
        Type::NamedTuple(nt1) => {
            if let Type::NamedTuple(nt2) = type2
                && nt1.__new__.defined_at == nt2.__new__.defined_at
            {
                return Some(Type::NamedTuple(nt1.clone()));
            }
            return common_base_for_tuple_against_type(
                i_s,
                &nt1.as_tuple(),
                type2,
                checked_recursions,
            );
        }
        Type::TypedDict(td1) => {
            if let Type::TypedDict(td2) = &type2 {
                return Some(Type::TypedDict(td1.intersection(i_s, td2)));
            }
        }
        Type::Type(t1) => {
            if let Type::Type(t2) = type2 {
                return Some(Type::Type(Arc::new(t1.common_base_type_internal(
                    i_s,
                    t2,
                    Some(checked_recursions),
                ))));
            }
        }
        _ => {
            if type1.is_simple_same_type(i_s, type2).bool() {
                return Some(type1.clone());
            }
        }
    }
    None
}

impl CallableParams {
    pub fn common_base_type(
        &self,
        i_s: &InferenceState,
        other: &CallableParams,
        checked_recursions: Option<CheckedTypeRecursion>,
    ) -> Option<CallableParams> {
        match self {
            CallableParams::Simple(params1) => match other {
                CallableParams::Simple(params2) => {
                    common_params(i_s, params1, params2, checked_recursions)
                }
                CallableParams::Any(_) => Some(other.clone()),
            },
            CallableParams::Any(_) => Some(self.clone()),
        }
    }
}

fn common_base_for_callable_against_type(
    i_s: &InferenceState,
    c1: &CallableContent,
    other: &Type,
    checked_recursions: CheckedTypeRecursion,
) -> Option<Type> {
    match other.maybe_callable(i_s)? {
        CallableLike::Callable(c2) => {
            Some(common_base_for_callables(i_s, c1, &c2, checked_recursions))
        }
        CallableLike::Overload(_) => None,
    }
}
fn common_base_for_callables(
    i_s: &InferenceState,
    c1: &CallableContent,
    c2: &CallableContent,
    checked_recursions: CheckedTypeRecursion,
) -> Type {
    if !c1.kind.is_same_base_kind(&c2.kind) {
        return i_s.db.python_state.function_type();
    }
    if let Some(params) = c1
        .params
        .common_base_type(i_s, &c2.params, Some(checked_recursions))
    {
        Type::Callable(Arc::new(CallableContent {
            name: None,
            class_name: None,
            defined_at: c1.defined_at,
            kind: c1.kind.clone(),
            // TODO why do we just use the first type vars here???
            type_vars: c1.type_vars.clone(),
            guard: common_base_guard(i_s, &c1.guard, &c2.guard),
            is_abstract: c1.is_abstract && c2.is_abstract,
            is_abstract_from_super: false,
            is_final: c1.is_final && c2.is_final,
            deprecated_reason: None,
            params,
            return_type: c1.return_type.common_base_type_internal(
                i_s,
                &c2.return_type,
                Some(checked_recursions),
            ),
        }))
    } else {
        if Matcher::default().matches_callable(i_s, c1, c2).bool() {
            return Type::Callable(Arc::new(c2.clone()));
        }
        if Matcher::default().matches_callable(i_s, c2, c1).bool() {
            return Type::Callable(Arc::new(c1.clone()));
        }
        i_s.db.python_state.function_type()
    }
}

fn common_params<'x>(
    i_s: &InferenceState,
    params1: &'x [CallableParam],
    params2: &'x [CallableParam],
    checked_recursions: Option<CheckedTypeRecursion>,
) -> Option<CallableParams> {
    fn maybe_unpack_typed_dict_params<'y: 'z, 'z>(
        i_s: &InferenceState,
        params: &'y [CallableParam],
        td_params: &'z mut Vec<CallableParam>,
    ) -> Option<(usize, impl Iterator<Item = &'z CallableParam>)> {
        if let Some(p) = params.last()
            && let ParamType::StarStar(StarStarParamType::UnpackTypedDict(td)) = &p.type_
        {
            let mut params = params.iter();
            params.next_back();
            // TODO extra_items: handle
            *td_params = td
                .members(i_s.db)
                .named
                .iter()
                .map(|m| m.as_keyword_param())
                .collect();
            return Some((
                params.len() + td_params.len(),
                params.chain(td_params.iter()),
            ));
        }
        None
    }
    let mut new1 = vec![];
    let mut new2 = vec![];

    if let Some((len_p1, new_p1)) = maybe_unpack_typed_dict_params(i_s, params1, &mut new1) {
        if let Some((len_p2, new_p2)) = maybe_unpack_typed_dict_params(i_s, params2, &mut new2) {
            common_params_by_iterable(i_s, len_p1, len_p2, new_p1, new_p2, checked_recursions)
        } else {
            common_params_by_iterable(
                i_s,
                len_p1,
                params2.len(),
                new_p1,
                params2.iter(),
                checked_recursions,
            )
        }
    } else if let Some((len_p2, new_p2)) = maybe_unpack_typed_dict_params(i_s, params2, &mut new2) {
        common_params_by_iterable(
            i_s,
            params1.len(),
            len_p2,
            params1.iter(),
            new_p2,
            checked_recursions,
        )
    } else {
        common_params_by_iterable(
            i_s,
            params1.len(),
            params2.len(),
            params1.iter(),
            params2.iter(),
            checked_recursions,
        )
    }
}

fn common_params_by_iterable<'x>(
    i_s: &InferenceState,
    p1_len: usize,
    p2_len: usize,
    params1: impl Iterator<Item = &'x CallableParam>,
    params2: impl Iterator<Item = &'x CallableParam>,
    checked_recursions: Option<CheckedTypeRecursion>,
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
                might_have_type_vars: p1.might_have_type_vars || p2.might_have_type_vars,
            };

            let t1 = match p1.type_.details() {
                ParamTypeDetails::Type(t) => t,
                ParamTypeDetails::UnpackedTuple(u1) => match p2.type_.details() {
                    ParamTypeDetails::UnpackedTuple(u2) => {
                        new_params.push(new_param(ParamType::Star(StarParamType::UnpackedTuple(
                            common_base_for_tuples(i_s, &u1, &u2, checked_recursions),
                        ))));
                        continue;
                    }
                    _ => return None,
                },
                ParamTypeDetails::ParamSpecUsage(_) => {
                    if p1.type_ == p2.type_ {
                        new_params.push(p1.clone());
                        continue;
                    } else {
                        return None;
                    }
                }
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
        Some(CallableParams::new_simple(new_params.into()))
    } else {
        None
    }
}

fn common_base_guard(
    _i_s: &InferenceState,
    _guard1: &Option<TypeGuardInfo>,
    _guard2: &Option<TypeGuardInfo>,
) -> Option<TypeGuardInfo> {
    // For now do nothing.
    None
}

fn common_base_for_tuple_against_type(
    i_s: &InferenceState,
    tup1: &Tuple,
    t2: &Type,
    checked_recursions: CheckedTypeRecursion,
) -> Option<Type> {
    Some(match t2 {
        Type::Tuple(tup2) => Type::Tuple(common_base_for_tuples(
            i_s,
            tup1,
            tup2,
            Some(checked_recursions),
        )),
        Type::NamedTuple(nt2) => Type::Tuple(common_base_for_tuples(
            i_s,
            tup1,
            &nt2.as_tuple(),
            Some(checked_recursions),
        )),
        _ => return None,
    })
}

fn common_base_for_tuples(
    i_s: &InferenceState,
    tup1: &Tuple,
    tup2: &Tuple,
    checked_recursions: Option<CheckedTypeRecursion>,
) -> Arc<Tuple> {
    if let Some(tup1) = tup1.maybe_avoid_implicit_literal(i_s.db) {
        common_base_for_tuples(i_s, &tup1, tup2, checked_recursions)
    } else if let Some(tup2) = tup2.maybe_avoid_implicit_literal(i_s.db) {
        common_base_for_tuples(i_s, tup1, &tup2, checked_recursions)
    } else {
        Tuple::new(
            tup1.args
                .common_base_type(i_s, &tup2.args, checked_recursions),
        )
    }
}

fn common_base_type_from_iterator<'x>(
    i_s: &InferenceState,
    types: impl Iterator<Item = &'x Type>,
    checked_recursions: Option<CheckedTypeRecursion>,
) -> Type {
    let mut out: Option<Type> = None;
    for t in types {
        if let Some(o) = out.take() {
            out = Some(o.common_base_type_internal(i_s, t, checked_recursions))
        } else {
            out = Some(t.clone());
        }
    }
    out.unwrap_or_else(|| Type::Never(NeverCause::Other))
}

impl TupleArgs {
    fn common_base_type(
        &self,
        i_s: &InferenceState,
        other: &Self,
        checked_recursions: Option<CheckedTypeRecursion>,
    ) -> Self {
        if self == other {
            return self.clone();
        }
        if self.maybe_any().is_some() {
            return self.clone();
        } else if other.maybe_any().is_some() {
            return other.clone();
        }
        match (self, other) {
            (Self::FixedLen(ts1), Self::FixedLen(ts2)) => {
                if ts1.len() == ts2.len() {
                    Self::FixedLen(
                        ts1.iter()
                            .zip(ts2.iter())
                            .map(|(t1, t2)| {
                                t1.common_base_type_internal(i_s, t2, checked_recursions)
                            })
                            .collect(),
                    )
                } else {
                    Self::ArbitraryLen(Arc::new(common_base_type_from_iterator(
                        i_s,
                        ts1.iter().chain(ts2.iter()),
                        checked_recursions,
                    )))
                }
            }
            (Self::ArbitraryLen(t1), Self::ArbitraryLen(t2)) => Self::ArbitraryLen(Arc::from(
                t1.common_base_type_internal(i_s, t2, checked_recursions),
            )),
            (Self::ArbitraryLen(t), Self::FixedLen(ts))
            | (Self::FixedLen(ts), Self::ArbitraryLen(t)) => {
                Self::ArbitraryLen(Arc::new(common_base_type_from_iterator(
                    i_s,
                    std::iter::once(t.as_ref()).chain(ts.iter()),
                    checked_recursions,
                )))
            }
            (TupleArgs::WithUnpack(w1), TupleArgs::WithUnpack(w2))
                if w1.before.len() == w2.before.len() && w1.after.len() == w2.after.len() =>
            {
                TupleArgs::WithUnpack(WithUnpack {
                    before: w1
                        .before
                        .iter()
                        .zip(w2.before.iter())
                        .map(|(t1, t2)| t1.simplified_union(i_s, t2))
                        .collect(),
                    unpack: match (&w1.unpack, &w2.unpack) {
                        (TupleUnpack::ArbitraryLen(t1), TupleUnpack::ArbitraryLen(t2)) => {
                            TupleUnpack::ArbitraryLen(t1.simplified_union(i_s, t2))
                        }
                        (TupleUnpack::TypeVarTuple(tvt1), TupleUnpack::TypeVarTuple(tvt2))
                            if tvt1 == tvt2 =>
                        {
                            TupleUnpack::TypeVarTuple(tvt1.clone())
                        }
                        _ => {
                            if w1.unpack.is_any() {
                                w1.unpack.clone()
                            } else if w2.unpack.is_any() {
                                w2.unpack.clone()
                            } else {
                                TupleUnpack::ArbitraryLen(i_s.db.python_state.object_type())
                            }
                        }
                    },
                    after: w1
                        .after
                        .iter()
                        .zip(w2.after.iter())
                        .map(|(t1, t2)| t1.simplified_union(i_s, t2))
                        .collect(),
                })
            }
            (_, _) => TupleArgs::ArbitraryLen(Arc::new(
                self.simplified_union_of_tuple_entries(i_s)
                    .simplified_union(i_s, &other.simplified_union_of_tuple_entries(i_s)),
            )),
        }
    }
}
