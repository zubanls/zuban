use std::{borrow::Cow, rc::Rc};

use parsa_python_ast::ParamKind;

use crate::{
    inference_state::InferenceState,
    matching::{Match, Type},
    type_helpers::{Class, TypeOrClass},
};

use super::{
    CallableContent, CallableParam, CallableParams, ClassGenerics, DbType,
    DoubleStarredParamSpecific, GenericItem, GenericsList, ParamSpecific, StarredParamSpecific,
    TupleContent, TupleTypeArguments, TypeOrTypeVarTuple, TypeVarLike, Variance,
};

impl DbType {
    pub fn common_base_type(&self, i_s: &InferenceState, other: &Self) -> DbType {
        let check_both_sides = |t1: &_, t2: &DbType| match t1 {
            /*
            DbType::Union(u) if u.iter().any(|t| matches!(t, DbType::None)) => {
                return self.clone().union(i_s.db, other.clone()).into_db_type()
            }
            */
            DbType::None | DbType::Union(_) => return Some(self.simplified_union(i_s, other)),
            DbType::Class(c) if c.class(i_s.db).is_calculating_class_infos() => {
                Some(t1.clone().union(i_s.db, t2.clone()))
            }
            DbType::Any => return Some(DbType::Any),
            DbType::Never => return Some(t2.clone()),
            _ => None,
        };

        if let Some(new) = check_both_sides(self, other) {
            return new;
        }
        if let Some(new) = check_both_sides(other, self) {
            return new;
        }
        for (_, c1) in Type::new(self).mro(i_s.db) {
            for (_, c2) in Type::new(other).mro(i_s.db) {
                match &c1 {
                    TypeOrClass::Type(t1) => {
                        let TypeOrClass::Type(t2) = c2 else {
                            continue
                        };
                        if let Some(base) = common_base_type_for_non_class(i_s, t1, &t2) {
                            return base;
                        }
                    }
                    TypeOrClass::Class(c1) => {
                        let TypeOrClass::Class(c2) = c2 else {
                            continue
                        };
                        if let Some(t) = common_base_class(i_s, *c1, c2) {
                            return t;
                        }
                    }
                }
            }
        }
        unreachable!("object is always a common base class")
    }
}

pub fn common_base_type<'x, I: Iterator<Item = &'x TypeOrTypeVarTuple>>(
    i_s: &InferenceState,
    mut ts: I,
) -> DbType {
    if let Some(first) = ts.next() {
        let mut result = match first {
            TypeOrTypeVarTuple::Type(t) => Cow::Borrowed(t),
            TypeOrTypeVarTuple::TypeVarTuple(_) => return i_s.db.python_state.object_db_type(),
        };
        for t in ts {
            let t = match t {
                TypeOrTypeVarTuple::Type(t) => t,
                TypeOrTypeVarTuple::TypeVarTuple(_) => return i_s.db.python_state.object_db_type(),
            };
            result = Cow::Owned(result.common_base_type(i_s, &Type::new(t)));
        }
        result.into_owned()
    } else {
        DbType::Never
    }
}

fn common_base_class(i_s: &InferenceState, c1: Class, c2: Class) -> Option<DbType> {
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
                                generics.push(GenericItem::TypeArgument(inner_t1.into_db_type()));
                            }
                            Match::True { with_any: true } => {
                                generics.push(GenericItem::TypeArgument(inner_t2.into_db_type()));
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
            _ => todo!(),
        }
    }
    Some(DbType::new_class(
        c1.node_ref.as_link(),
        ClassGenerics::List(GenericsList::generics_from_vec(generics)),
    ))
}

fn common_base_type_for_non_class(
    i_s: &InferenceState,
    t1: &DbType,
    t2: &DbType,
) -> Option<DbType> {
    match t1 {
        DbType::Callable(c1) => {
            // TODO this should also be done for function/callable and callable/function and
            // not only callable/callable
            if let DbType::Callable(c2) = t2 {
                return Some(common_base_for_callables(i_s, c1, c2));
            }
        }
        DbType::Tuple(tup1) => return common_base_for_tuple_against_db_type(i_s, tup1, t2),
        DbType::NamedTuple(nt1) => {
            if let DbType::NamedTuple(nt2) = t2 {
                if nt1.__new__.defined_at == nt2.__new__.defined_at {
                    return Some(DbType::NamedTuple(nt1.clone()));
                }
            }
            return common_base_for_tuple_against_db_type(i_s, &nt1.as_tuple(), t2);
        }
        DbType::TypedDict(td1) => {
            if let DbType::TypedDict(td2) = &t2 {
                return Some(DbType::TypedDict(td1.intersection(i_s, td2)));
            }
        }
        DbType::Type(t1) => {
            if let DbType::Type(t2) = t2 {
                return Some(DbType::Type(Rc::new(t1.common_base_type(i_s, t2))));
            }
        }
        _ => {
            if Type::new(t1)
                .is_simple_same_type(i_s, &Type::new(t2))
                .bool()
            {
                return Some(t1.clone());
            }
        }
    }
    None
}

fn common_base_for_callables(
    i_s: &InferenceState,
    c1: &CallableContent,
    c2: &CallableContent,
) -> DbType {
    if c1.kind != c2.kind {
        todo!()
    }
    match &c1.params {
        CallableParams::Simple(params1) => match &c2.params {
            CallableParams::Simple(params2) => {
                if let Some(params) = common_params(i_s, &params1, &params2) {
                    return DbType::Callable(Rc::new(CallableContent {
                        name: None,
                        class_name: None,
                        defined_at: c1.defined_at,
                        kind: c1.kind,
                        type_vars: i_s.db.python_state.empty_type_var_likes.clone(),
                        params,
                        result_type: Type::new(&c1.result_type)
                            .common_base_type(i_s, &Type::new(&c2.result_type)),
                    }));
                }
            }
            CallableParams::WithParamSpec(_, _) => (),
            CallableParams::Any => todo!(),
        },
        CallableParams::WithParamSpec(_, _) => (),
        CallableParams::Any => todo!(),
    }
    i_s.db.python_state.function_db_type()
}

fn common_params(
    i_s: &InferenceState,
    params1: &[CallableParam],
    params2: &[CallableParam],
) -> Option<CallableParams> {
    if params1.len() == params2.len() {
        let mut new_params = vec![];
        for (p1, p2) in params1.iter().zip(params2.iter()) {
            let mut kind = p1.param_specific.param_kind();
            let p2_kind = p2.param_specific.param_kind();
            let p1_name = p1.name.map(|n| n.as_str(i_s.db));
            let p2_name = p2.name.map(|n| n.as_str(i_s.db));
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
            let t1 = p1.param_specific.maybe_positional_db_type()?;
            let t2 = p2.param_specific.maybe_positional_db_type()?;
            let new_t = t1.common_sub_type(i_s, t2)?;
            new_params.push(CallableParam {
                param_specific: match &kind {
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
                name: (p1_name == p2_name).then(|| p1.name).flatten(),
                has_default: p1.has_default & p2.has_default,
            });
        }
        Some(CallableParams::Simple(new_params.into()))
    } else {
        todo!()
    }
}

fn common_base_for_tuple_against_db_type(
    i_s: &InferenceState,
    tup1: &TupleContent,
    t2: &DbType,
) -> Option<DbType> {
    Some(match t2 {
        DbType::Tuple(tup2) => DbType::Tuple(Rc::new(common_base_for_tuples(i_s, tup1, tup2))),
        DbType::NamedTuple(nt2) => {
            DbType::Tuple(Rc::new(common_base_for_tuples(i_s, tup1, &nt2.as_tuple())))
        }
        _ => return None,
    })
}

fn common_base_for_tuples(
    i_s: &InferenceState,
    tup1: &TupleContent,
    tup2: &TupleContent,
) -> TupleContent {
    TupleContent::new(match &tup2.args {
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
