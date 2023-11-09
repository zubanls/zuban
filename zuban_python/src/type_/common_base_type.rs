use std::{borrow::Cow, rc::Rc};

use parsa_python_ast::ParamKind;

use crate::{
    inference_state::InferenceState,
    matching::Match,
    type_::CallableLike,
    type_helpers::{Class, TypeOrClass},
};

use super::{
    CallableContent, CallableParam, CallableParams, ClassGenerics, GenericItem, GenericsList,
    ParamType, StarParamType, StarStarParamType, Tuple, TupleTypeArguments, Type,
    TypeOrTypeVarTuple, TypeVarLike, Variance,
};

impl Type {
    pub fn common_base_type(&self, i_s: &InferenceState, other: &Self) -> Type {
        let check_both_sides = |t1: &_, t2: &Type| match t1 {
            /*
            Type::Union(u) if u.iter().any(|t| matches!(t, Type::None)) => {
                return self.clone().union(i_s.db, other.clone()).into_type()
            }
            */
            Type::None | Type::Union(_) => return Some(self.simplified_union(i_s, other)),
            Type::Class(c) if c.class(i_s.db).is_calculating_class_infos() => {
                Some(t1.clone().union(i_s.db, t2.clone()))
            }
            Type::Any(cause) => return Some(Type::Any(*cause)),
            Type::Never => return Some(t2.clone()),
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
                            if let Some(base) = class_against_non_class(i_s, c2, &t1) {
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
        unreachable!("object is always a common base class")
    }
}

pub fn common_base_type<'x, I: Iterator<Item = &'x TypeOrTypeVarTuple>>(
    i_s: &InferenceState,
    mut ts: I,
) -> Type {
    if let Some(first) = ts.next() {
        let mut result = match first {
            TypeOrTypeVarTuple::Type(t) => Cow::Borrowed(t),
            TypeOrTypeVarTuple::TypeVarTuple(_) => return i_s.db.python_state.object_type(),
        };
        for t in ts {
            let t = match t {
                TypeOrTypeVarTuple::Type(t) => t,
                TypeOrTypeVarTuple::TypeVarTuple(_) => return i_s.db.python_state.object_type(),
            };
            result = Cow::Owned(result.common_base_type(i_s, t));
        }
        result.into_owned()
    } else {
        Type::Never
    }
}

fn common_base_class(i_s: &InferenceState, c1: Class, c2: Class) -> Option<Type> {
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
                                generics.push(GenericItem::TypeArgument(inner_t1.into_owned()));
                            }
                            Match::True { with_any: true } => {
                                generics.push(GenericItem::TypeArgument(inner_t2.into_owned()));
                            }
                            _ => return None,
                        }
                    }
                    Variance::Covariant => {
                        generics.push(GenericItem::TypeArgument(
                            inner_t1.common_base_type(i_s, &inner_t2),
                        ));
                    }
                    Variance::Contravariant => {
                        if let Some(t) = inner_t1.common_sub_type(i_s, &inner_t2) {
                            generics.push(GenericItem::TypeArgument(t));
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
    if let Type::RecursiveAlias(r2) = t2 {
        if let Type::Class(c2) = r2.calculated_type(i_s.db) {
            return common_base_class(i_s, c1, c2.class(i_s.db));
        }
    }
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
                if let Some(params) = common_params(i_s, &params1, &params2) {
                    return Type::Callable(Rc::new(CallableContent {
                        name: None,
                        class_name: None,
                        defined_at: c1.defined_at,
                        kind: c1.kind,
                        // TODO why do we just remove type vars here???
                        type_vars: i_s.db.python_state.empty_type_var_likes.clone(),
                        params,
                        result_type: c1.result_type.common_base_type(i_s, &c2.result_type),
                    }));
                }
            }
            CallableParams::WithParamSpec(_, _) => (),
            CallableParams::Any(_) => todo!(),
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
                        params: CallableParams::WithParamSpec(pre1.clone(), spec1.clone()),
                        result_type: c1.result_type.common_base_type(i_s, &c2.result_type),
                    }));
                }
            }
            _ => (),
        },
        CallableParams::Any(_) => todo!(),
    }
    i_s.db.python_state.function_type()
}

fn common_params(
    i_s: &InferenceState,
    params1: &[CallableParam],
    params2: &[CallableParam],
) -> Option<CallableParams> {
    if params1.len() == params2.len() {
        let mut new_params = vec![];
        for (p1, p2) in params1.iter().zip(params2.iter()) {
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
            let t1 = p1.type_.maybe_positional_type()?;
            let t2 = p2.type_.maybe_positional_type()?;
            let new_t = t1.common_sub_type(i_s, t2)?;
            new_params.push(CallableParam {
                type_: match &kind {
                    ParamKind::PositionalOnly => ParamType::PositionalOnly(new_t),
                    ParamKind::PositionalOrKeyword => ParamType::PositionalOrKeyword(new_t),
                    ParamKind::KeywordOnly => ParamType::KeywordOnly(new_t),
                    ParamKind::Star => ParamType::Star(StarParamType::ArbitraryLength(new_t)),
                    ParamKind::StarStar => ParamType::StarStar(StarStarParamType::ValueType(new_t)),
                },
                name: (p1_name == p2_name).then(|| p1.name.clone()).flatten(),
                has_default: p1.has_default & p2.has_default,
            });
        }
        Some(CallableParams::Simple(new_params.into()))
    } else {
        todo!()
    }
}

fn common_base_for_tuple_against_type(
    i_s: &InferenceState,
    tup1: &Tuple,
    t2: &Type,
) -> Option<Type> {
    Some(match t2 {
        Type::Tuple(tup2) => Type::Tuple(Rc::new(common_base_for_tuples(i_s, tup1, tup2))),
        Type::NamedTuple(nt2) => {
            Type::Tuple(Rc::new(common_base_for_tuples(i_s, tup1, &nt2.as_tuple())))
        }
        _ => return None,
    })
}

fn common_base_for_tuples(i_s: &InferenceState, tup1: &Tuple, tup2: &Tuple) -> Tuple {
    Tuple::new(match &tup2.args {
        TupleTypeArguments::FixedLength(ts2) => {
            let mut new_args = tup1.args.clone();
            common_base_type_of_type_var_tuple_with_items(
                &mut new_args,
                i_s,
                ts2.len(),
                ts2.iter(),
            );
            new_args
        }
        TupleTypeArguments::ArbitraryLength(t2) => match &tup1.args {
            TupleTypeArguments::FixedLength(ts1) => {
                let mut new_args = tup2.args.clone();
                common_base_type_of_type_var_tuple_with_items(
                    &mut new_args,
                    i_s,
                    ts1.len(),
                    ts1.iter(),
                );
                new_args
            }
            TupleTypeArguments::ArbitraryLength(t1) => todo!(),
        },
    })
}

pub fn common_base_type_of_type_var_tuple_with_items<
    'x,
    I: ExactSizeIterator<Item = &'x TypeOrTypeVarTuple>,
>(
    args: &mut TupleTypeArguments,
    i_s: &InferenceState,
    length: usize,
    items: I,
) {
    match args {
        TupleTypeArguments::FixedLength(calc_ts) => {
            if length == calc_ts.len() {
                let mut new = vec![];
                for (t1, t2) in calc_ts.iter().zip(items) {
                    match (t1, t2) {
                        (TypeOrTypeVarTuple::Type(t1), TypeOrTypeVarTuple::Type(t2)) => {
                            new.push(TypeOrTypeVarTuple::Type(t1.common_base_type(i_s, t2)));
                        }
                        _ => todo!(),
                    }
                }
                *calc_ts = new.into();
            } else {
                // We use map to make an iterator with covariant lifetimes.
                #[allow(clippy::map_identity)]
                let t = common_base_type(i_s, calc_ts.iter().chain(items.map(|x| x)));
                *args = TupleTypeArguments::ArbitraryLength(Box::new(t));
            }
        }
        TupleTypeArguments::ArbitraryLength(calc_t) => {
            if items.len() == 0 {
                // args is already ok, because we have an empty tuple here that can be anything.
                return;
            }
            let base = common_base_type(i_s, items).common_base_type(i_s, calc_t);
            *args = TupleTypeArguments::ArbitraryLength(Box::new(base));
        }
    }
}
