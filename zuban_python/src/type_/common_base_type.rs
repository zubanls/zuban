use std::rc::Rc;

use parsa_python_cst::ParamKind;

use super::{
    CallableContent, CallableParam, CallableParams, ClassGenerics, GenericItem, GenericsList,
    ParamType, ParamTypeDetails, StarParamType, StarStarParamType, Tuple, Type, TypeGuardInfo,
    TypeVarLike, Variance,
};
use crate::{
    database::Database,
    inference_state::InferenceState,
    matching::{CheckedTypeRecursion, Match, Matcher},
    type_::CallableLike,
    type_helpers::{Class, TypeOrClass},
};

impl Type {
    pub fn common_base_type(&self, i_s: &InferenceState, other: &Self) -> Type {
        self.common_base_type_internal(i_s, other, None)
    }

    fn common_base_type_internal(
        &self,
        i_s: &InferenceState,
        other: &Self,
        checked_recursions: Option<CheckedTypeRecursion>,
    ) -> Type {
        let check_both_sides = |t1: &_, t2: &Type| match t1 {
            /*
            Type::Union(u) if u.iter().any(|t| matches!(t, Type::None)) => {
                return self.clone().union(i_s.db, other.clone()).into_type()
            }
            */
            Type::None | Type::Union(_) => Some(self.simplified_union(i_s, other)),
            Type::Any(cause) => Some(Type::Any(*cause)),
            Type::Never(_) => Some(t2.clone()),
            Type::Callable(c1) => common_base_for_callable_against_type(i_s, c1, t2),
            Type::EnumMember(_) => match t2 {
                Type::EnumMember(_) | Type::Enum(_) => Some(t1.simplified_union(i_s, t2)),
                _ => None,
            },
            _ => None,
        };

        let checked_recursions = CheckedTypeRecursion {
            current: (self, other),
            previous: checked_recursions.as_ref(),
        };
        if checked_recursions.is_cycle() {
            return i_s.db.python_state.object_type();
        }

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
                            if let Some(base) =
                                class_against_non_class(i_s, c2, t1, checked_recursions)
                            {
                                return base;
                            }
                        }
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
                            if let Some(t) = common_base_class(i_s, *c1, c2, checked_recursions) {
                                return t;
                            }
                        }
                        TypeOrClass::Type(t2) => {
                            if let Some(base) =
                                class_against_non_class(i_s, *c1, &t2, checked_recursions)
                            {
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

fn class_against_non_class(
    i_s: &InferenceState,
    c1: Class,
    t2: &Type,
    checked_recursions: CheckedTypeRecursion,
) -> Option<Type> {
    if let Type::RecursiveType(r2) = t2 {
        if let Type::Class(c2) = r2.calculated_type(i_s.db) {
            return common_base_class(i_s, c1, c2.class(i_s.db), checked_recursions);
        }
    }
    None
}

fn common_base_type_for_non_class(
    i_s: &InferenceState,
    type1: &Type,
    type2: &Type,
    checked_recursions: CheckedTypeRecursion,
) -> Option<Type> {
    match type1 {
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
            Type::Type(t2) => {
                return Some(Type::Type(Rc::new(t1.common_base_type_internal(
                    i_s,
                    t2,
                    Some(checked_recursions),
                ))))
            }
            _ => (),
        },
        Type::RecursiveType(r1) => match type2 {
            Type::RecursiveType(r2) => {
                return Some(r1.calculated_type(i_s.db).common_base_type_internal(
                    i_s,
                    r2.calculated_type(i_s.db),
                    Some(checked_recursions),
                ))
            }
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

impl CallableParams {
    pub fn common_base_type(
        &self,
        i_s: &InferenceState,
        other: &CallableParams,
    ) -> Option<CallableParams> {
        match self {
            CallableParams::Simple(params1) => match other {
                CallableParams::Simple(params2) => common_params(i_s, params1, params2),
                CallableParams::Any(_) => Some(other.clone()),
                CallableParams::Never(_) => todo!(),
            },
            CallableParams::Any(_) => Some(self.clone()),
            CallableParams::Never(_) => todo!(),
        }
    }
}

fn common_base_for_callable_against_type(
    i_s: &InferenceState,
    c1: &CallableContent,
    other: &Type,
) -> Option<Type> {
    match other.maybe_callable(i_s)? {
        CallableLike::Callable(c2) => Some(common_base_for_callables(i_s, c1, &c2)),
        CallableLike::Overload(_) => None,
    }
}
fn common_base_for_callables(
    i_s: &InferenceState,
    c1: &CallableContent,
    c2: &CallableContent,
) -> Type {
    if !c1.kind.is_same_base_kind(c2.kind) {
        return i_s.db.python_state.function_type();
    }
    if let Some(params) = c1.params.common_base_type(i_s, &c2.params) {
        Type::Callable(Rc::new(CallableContent {
            name: None,
            class_name: None,
            defined_at: c1.defined_at,
            kind: c1.kind,
            // TODO why do we just use the first type vars here???
            type_vars: c1.type_vars.clone(),
            guard: common_base_guard(i_s, &c1.guard, &c2.guard),
            is_abstract: c1.is_abstract && c2.is_abstract,
            is_final: c1.is_final && c2.is_final,
            params,
            return_type: c1.return_type.common_base_type(i_s, &c2.return_type),
            no_type_check: false,
        }))
    } else {
        if Matcher::default().matches_callable(i_s, c1, c2).bool() {
            return Type::Callable(Rc::new(c2.clone()));
        }
        if Matcher::default().matches_callable(i_s, c2, c1).bool() {
            return Type::Callable(Rc::new(c1.clone()));
        }
        i_s.db.python_state.function_type()
    }
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
                ParamTypeDetails::ParamSpecUsage(u1) => {
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
    Tuple::new(tup1.args.simplified_union(i_s, &tup2.args))
}
