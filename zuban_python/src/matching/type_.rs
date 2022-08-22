use std::borrow::Cow;

use super::params::has_overlapping_params;
use super::{
    matches_params, CalculatedTypeArguments, ClassLike, Generics, Match, MismatchReason,
    TypeVarMatcher,
};
use crate::database::{
    CallableContent, Database, DbType, FormatStyle, TupleContent, TypeVarUsage, UnionType, Variance,
};
use crate::debug;
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::node_ref::NodeRef;
use crate::value::Class;

#[derive(Debug, Clone)]
#[allow(clippy::enum_variant_names)]
pub enum Type<'db, 'a> {
    ClassLike(ClassLike<'db, 'a>),
    Type(Cow<'a, DbType>),
}

impl<'db, 'a> Type<'db, 'a> {
    pub fn new(t: &'a DbType) -> Self {
        Self::Type(Cow::Borrowed(t))
    }

    pub fn owned(t: DbType) -> Self {
        Self::Type(Cow::Owned(t))
    }

    pub fn from_db_type(db: &'db Database, db_type: &'a DbType) -> Self {
        match db_type {
            DbType::Class(link, generics) => {
                let node_ref = NodeRef::from_link(db, *link);
                Self::ClassLike(ClassLike::Class(
                    Class::from_position(node_ref, Generics::new_maybe_list(generics), None)
                        .unwrap(),
                ))
            }
            _ => Self::new(db_type),
        }
    }

    pub fn union(self, i_s: &mut InferenceState<'db, '_>, other: Self) -> Self {
        Self::owned(self.into_db_type(i_s).union(other.into_db_type(i_s)))
    }

    pub fn into_db_type(self, i_s: &mut InferenceState<'db, '_>) -> DbType {
        match self {
            Self::ClassLike(class_like) => class_like.as_db_type(i_s),
            Self::Type(t) => t.into_owned(),
        }
    }

    pub fn as_db_type(&self, i_s: &mut InferenceState<'db, '_>) -> DbType {
        match self {
            Self::ClassLike(class_like) => class_like.as_db_type(i_s),
            Self::Type(t) => t.clone().into_owned(),
        }
    }

    fn maybe_db_type(&self) -> Option<&DbType> {
        match self {
            Self::ClassLike(_) => None,
            Self::Type(t) => Some(t.as_ref()),
        }
    }

    pub fn overlaps(&self, i_s: &mut InferenceState<'db, '_>, other: &Self) -> bool {
        match other.maybe_db_type() {
            Some(DbType::TypeVar(t2)) => {
                return if let Some(bound) = &t2.type_var.bound {
                    self.overlaps(i_s, &Type::new(bound))
                } else if !t2.type_var.restrictions.is_empty() {
                    todo!("{self:?}")
                } else {
                    true
                };
            }
            _ => (),
        }

        match self {
            Self::ClassLike(class1) => match other {
                Self::ClassLike(class2) => class1.overlaps(i_s, class2),
                Self::Type(t1) => match t1.as_ref() {
                    DbType::Union(union_type) => union_type
                        .iter()
                        .any(|t| self.overlaps(i_s, &Type::from_db_type(i_s.db, t))),
                    _ => todo!(),
                },
            },
            Self::Type(t1) => match t1.as_ref() {
                DbType::Class(link, generics) => match other {
                    Self::Type(t2) => todo!(),
                    _ => todo!(),
                },
                DbType::Type(t1) => match other {
                    Self::Type(ref t2) => match t2.as_ref() {
                        DbType::Type(t2) => Type::new(t1).overlaps(i_s, &Type::new(t2)),
                        _ => false,
                    },
                    _ => false,
                },
                DbType::Callable(c1) => match other {
                    Self::Type(ref t2) => match t2.as_ref() {
                        DbType::Callable(c2) => {
                            Type::new(&c1.return_class).overlaps(i_s, &Type::new(&c2.return_class))
                                && has_overlapping_params(i_s, &c1.params, &c2.params)
                        }
                        DbType::Type(t2) => Type::new(t1).overlaps(i_s, &Type::new(t2)),
                        _ => false,
                    },
                    _ => false,
                },
                DbType::Any => true,
                DbType::Never => todo!(),
                DbType::None => {
                    matches!(other, Self::Type(t2) if matches!(t2.as_ref(), DbType::None))
                }
                DbType::TypeVar(t1) => {
                    if let Some(db_t) = &t1.type_var.bound {
                        Type::new(db_t).overlaps(i_s, other)
                    } else if !t1.type_var.restrictions.is_empty() {
                        todo!("{other:?}")
                    } else {
                        true
                    }
                }
                DbType::Tuple(t1) => match other {
                    Self::Type(t2) => match t2.as_ref() {
                        DbType::Tuple(t2) => Self::overlaps_tuple(i_s, t1, t2),
                        _ => false,
                    },
                    _ => false,
                },
                DbType::Union(union_type) => union_type
                    .iter()
                    .any(|t| Type::from_db_type(i_s.db, t).overlaps(i_s, other)),
            },
        }
    }

    pub fn matches(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        matcher: Option<&mut TypeVarMatcher<'db, '_>>,
        value_type: &Self,
        variance: Variance,
    ) -> Match {
        if let Type::Type(t2) = value_type {
            match t2.as_ref() {
                DbType::Any => {
                    if let Some(matcher) = matcher {
                        let t1 = match self {
                            Self::ClassLike(c) => Cow::Owned(c.as_db_type(i_s)),
                            Self::Type(t) => Cow::Borrowed(t.as_ref()),
                        };
                        matcher.set_all_contained_type_vars_to_any(i_s, t1.as_ref())
                    }
                    return Match::TrueWithAny;
                }
                DbType::None => match variance {
                    Variance::Contravariant => (), // TODO ? (matches!(self, Self::None)).into(),
                    _ => return Match::True,
                },
                DbType::TypeVar(t2) => {
                    return match self.maybe_db_type() {
                        Some(DbType::TypeVar(t1)) => {
                            if let Some(matcher) = matcher {
                                matcher.match_or_add_type_var(i_s, t1, value_type, variance)
                            } else {
                                self.matches_type_var(i_s, t2).into() // TODO does this check make sense?
                            }
                        }
                        _ => {
                            if self.matches_type_var(i_s, t2) {
                                // TODO does this check make sense?
                                Match::True
                            } else if let Some(bound) = &t2.type_var.bound {
                                self.matches(i_s, None, &Type::new(bound), variance)
                            } else if !t2.type_var.restrictions.is_empty() {
                                t2.type_var
                                    .restrictions
                                    .iter()
                                    .any(|r| {
                                        self.matches(i_s, None, &Type::new(r), variance).bool()
                                    })
                                    .into()
                            } else {
                                todo!() // self.is_object_class(i_s.db)
                            }
                        }
                    };
                }
                _ => (),
            }
        };
        match self {
            Self::ClassLike(class) => class.matches(i_s, value_type, matcher, variance),
            Self::Type(t1) => match t1.as_ref() {
                DbType::Class(link, generics) => match value_type {
                    Self::Type(t2) => todo!(),
                    _ => todo!(),
                },
                DbType::Type(t1) => match value_type {
                    Self::Type(ref t2) => match t2.as_ref() {
                        DbType::Type(t2) => {
                            Type::new(t1).matches(i_s, matcher, &Type::new(t2), variance)
                        }
                        _ => Match::new_false(),
                    },
                    _ => Match::new_false(),
                },
                DbType::TypeVar(t1) => match matcher {
                    Some(matcher) => matcher.match_or_add_type_var(i_s, t1, value_type, variance),
                    None => match value_type {
                        Self::Type(t2) => match t2.as_ref() {
                            DbType::TypeVar(t2) => (t1.index == t2.index
                                && t1.in_definition == t2.in_definition)
                                .into(),
                            _ => Match::new_false(),
                        },
                        _ => Match::new_false(),
                    },
                },
                DbType::Callable(c1) => match value_type {
                    Self::Type(ref t2) => match t2.as_ref() {
                        /*
                        DbType::Type(t2) => {
                            // TODO the __init__ should actually be looked up on the original class, not
                            // the subclass
                            if let LookupResult::GotoName(_, init) =
                                cls.lookup_internal(i_s, "__init__")
                            {
                                if let Type::ClassLike(ClassLike::FunctionType(f)) =
                                    init.class_as_type(i_s)
                                {
                                    // Since __init__ does not have a return, We need to check the params
                                    // of the __init__ functions and the class as a return type separately.
                                    return c1.result_type(i_s).matches(
                                        i_s,
                                        matcher.as_deref_mut(),
                                        &Type::ClassLike(ClassLike::Class(*cls)),
                                        Variance::Covariant,
                                    ) & matches_params(
                                        i_s,
                                        matcher,
                                        c1.param_iterator(),
                                        f.param_iterator().map(|i| i.skip(1)),
                                    );
                                }
                            }
                            Match::new_false()
                        }
                        Self::TypeWithDbType(t2) => {
                            if c1.content.params.is_some() {
                                todo!()
                            }
                            c1.result_type(i_s).matches(
                                i_s,
                                matcher.as_deref_mut(),
                                &Type::from_db_type(i_s.db, t2),
                                Variance::Covariant,
                            )
                            //todo!("{t2:?}")
                        }
                        */
                        DbType::Callable(c2) => Self::matches_callable(i_s, matcher, c1, c2),
                        _ => Match::new_false(),
                    },
                    _ => Match::new_false(),
                },
                DbType::None => {
                    matches!(value_type, Self::Type(ref t2) if matches!(t2.as_ref(), DbType::None))
                        .into()
                }
                DbType::Any => match value_type {
                    Self::Type(ref t2) if matches!(t2.as_ref(), DbType::Any) => Match::TrueWithAny,
                    _ => Match::True,
                },
                DbType::Never => todo!(),
                DbType::Tuple(t1) => match value_type {
                    Self::Type(t2) => match t2.as_ref() {
                        DbType::Tuple(t2) => {
                            let m: Match = Self::matches_tuple(i_s, matcher, t1, t2, variance);
                            m.similar_if_false()
                        }
                        _ => Match::new_false(),
                    },
                    _ => Match::False(MismatchReason::None),
                },
                DbType::Union(union_type1) => {
                    self.matches_union(i_s, matcher, union_type1, value_type, variance)
                }
            },
        }
    }

    fn matches_union(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        mut matcher: Option<&mut TypeVarMatcher<'db, '_>>,
        u1: &UnionType,
        value_type: &Self,
        variance: Variance,
    ) -> Match {
        match value_type.maybe_db_type() {
            // TODO this should use the variance argument
            Some(DbType::Union(u2)) => match variance {
                Variance::Covariant => {
                    let mut matches = true;
                    for g2 in u2.iter() {
                        let t2 = Type::from_db_type(i_s.db, g2);
                        matches &= u1.iter().any(|g1| {
                            Type::from_db_type(i_s.db, g1)
                                .matches(i_s, matcher.as_deref_mut(), &t2, variance)
                                .bool()
                        })
                    }
                    matches.into()
                }
                Variance::Invariant => {
                    self.matches(i_s, matcher, value_type, Variance::Covariant)
                        & self.matches(i_s, None, value_type, Variance::Contravariant)
                }
                Variance::Contravariant => u1
                    .iter()
                    .all(|g1| {
                        let t1 = Type::from_db_type(i_s.db, g1);
                        u2.iter().any(|g2| {
                            t1.matches(
                                i_s,
                                matcher.as_deref_mut(),
                                &Type::from_db_type(i_s.db, g2),
                                variance,
                            )
                            .bool()
                        })
                    })
                    .into(),
            },
            _ => match variance {
                Variance::Contravariant => Match::new_false(),
                Variance::Covariant | Variance::Invariant => u1
                    .iter()
                    .any(|g| {
                        Type::from_db_type(i_s.db, g)
                            .matches(i_s, matcher.as_deref_mut(), value_type, variance)
                            .bool()
                    })
                    .into(),
            },
        }
    }

    fn matches_callable(
        i_s: &mut InferenceState<'db, '_>,
        mut matcher: Option<&mut TypeVarMatcher<'db, '_>>,
        c1: &CallableContent,
        c2: &CallableContent,
    ) -> Match {
        Type::new(&c1.return_class).matches(
            i_s,
            matcher.as_deref_mut(),
            &Type::new(&c2.return_class),
            Variance::Covariant,
        ) & matches_params(
            i_s,
            matcher,
            c1.params.as_ref().map(|params| params.iter()),
            c2.params.as_ref().map(|params| params.iter()),
        )
    }

    fn matches_tuple(
        i_s: &mut InferenceState<'db, '_>,
        mut matcher: Option<&mut TypeVarMatcher<'db, '_>>,
        t1: &TupleContent,
        t2: &TupleContent,
        variance: Variance,
    ) -> Match {
        if let Some(generics1) = &t1.generics {
            if let Some(generics2) = &t2.generics {
                return match (t1.arbitrary_length, t2.arbitrary_length, variance) {
                    (false, false, _) | (true, true, _) => {
                        if generics1.len() != generics2.len() {
                            Match::new_false()
                        } else {
                            Generics::new_list(generics1).matches(
                                i_s,
                                matcher,
                                Generics::new_list(generics2),
                                variance,
                                None,
                            )
                        }
                    }
                    (false, true, Variance::Covariant)
                    | (true, false, Variance::Contravariant)
                    | (_, _, Variance::Invariant) => Match::new_false(),
                    (true, false, Variance::Covariant) => {
                        let t1 = Type::from_db_type(i_s.db, &generics1[0.into()]);
                        generics2
                            .iter()
                            .all(|g2| {
                                let t2 = Type::from_db_type(i_s.db, g2);
                                t1.matches(i_s, matcher.as_deref_mut(), &t2, variance)
                                    .bool()
                            })
                            .into()
                    }
                    (false, true, Variance::Contravariant) => {
                        let t2 = Type::from_db_type(i_s.db, &generics2[0.into()]);
                        generics1
                            .iter()
                            .all(|g1| {
                                let t1 = Type::from_db_type(i_s.db, g1);
                                t1.matches(i_s, matcher.as_deref_mut(), &t2, variance)
                                    .bool()
                            })
                            .into()
                    }
                };
            }
        }
        Match::True
    }

    fn overlaps_tuple(
        i_s: &mut InferenceState<'db, '_>,
        t1: &TupleContent,
        t2: &TupleContent,
    ) -> bool {
        if let Some(generics1) = &t1.generics {
            if let Some(generics2) = &t2.generics {
                return match (t1.arbitrary_length, t2.arbitrary_length) {
                    (false, false) | (true, true) => {
                        generics1.len() == generics2.len()
                            && Generics::new_list(generics1).overlaps(
                                i_s,
                                Generics::new_list(generics2),
                                None,
                            )
                    }
                    (false, true) => {
                        let t2 = Type::from_db_type(i_s.db, &generics2[0.into()]);
                        for g in generics1.iter() {
                            let t1 = Type::from_db_type(i_s.db, g);
                            if !t1.overlaps(i_s, &t2) {
                                dbg!();
                                return false;
                            }
                        }
                        true
                    }
                    (true, false) => {
                        let t1 = Type::from_db_type(i_s.db, &generics1[0.into()]);
                        for g in generics2.iter() {
                            let t2 = Type::from_db_type(i_s.db, g);
                            if !t1.overlaps(i_s, &t2) {
                                return false;
                            }
                        }
                        true
                    }
                };
            }
        }
        true
    }

    fn matches_type_var(&self, i_s: &mut InferenceState<'db, '_>, t2: &TypeVarUsage) -> bool {
        if let Some(DbType::TypeVar(t1)) = self.maybe_db_type() {
            if t1.index == t2.index && t1.in_definition == t2.in_definition {
                return true;
            }
        }
        if let Some(bound) = &t2.type_var.bound {
            self.matches(i_s, None, &Type::new(bound), Variance::Covariant)
                .bool()
        } else if !t2.type_var.restrictions.is_empty() {
            t2.type_var.restrictions.iter().any(|r| {
                self.matches(i_s, None, &Type::new(r), Variance::Covariant)
                    .bool()
            })
        } else {
            false
        }
    }

    pub fn error_if_not_matches<'x>(
        &self,
        i_s: &mut InferenceState<'db, 'x>,
        value: &Inferred<'db>,
        mut callback: impl FnMut(&mut InferenceState<'db, 'x>, Box<str>, Box<str>),
    ) {
        self.error_if_not_matches_with_matcher(
            i_s,
            None,
            value,
            Some(
                |i_s: &mut InferenceState<'db, 'x>, t1, t2, reason: &MismatchReason| {
                    callback(i_s, t1, t2)
                },
            ),
        );
    }

    pub fn error_if_not_matches_with_matcher<'x>(
        &self,
        i_s: &mut InferenceState<'db, 'x>,
        mut matcher: Option<&mut TypeVarMatcher<'db, '_>>,
        value: &Inferred<'db>,
        callback: Option<
            impl FnMut(&mut InferenceState<'db, 'x>, Box<str>, Box<str>, &MismatchReason),
        >,
    ) -> Match {
        let value_type = value.class_as_type(i_s);
        let matches = self.matches(
            i_s,
            matcher.as_deref_mut(),
            &value_type,
            Variance::Covariant,
        );
        if let Match::False(ref reason) | Match::FalseButSimilar(ref reason) = matches {
            let value_type = value.class_as_type(i_s);
            debug!(
                "Mismatch between {value_type:?} and {self:?} -> {:?}",
                matches.clone()
            );
            let input = value_type.format(i_s, None, FormatStyle::Short);
            let wanted = self.format(i_s, matcher.as_deref(), FormatStyle::Short);
            if let Some(mut callback) = callback {
                callback(i_s, input, wanted, reason)
            }
        }
        matches
    }

    pub fn execute_and_resolve_type_vars(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        class: Option<&Class<'db, '_>>,
        calculated_type_args: &CalculatedTypeArguments,
    ) -> Inferred<'db> {
        let db_type = self.internal_resolve_type_vars(i_s, class, calculated_type_args);
        debug!(
            "Resolved type vars: {}",
            db_type.format(i_s, None, FormatStyle::Short)
        );
        Inferred::execute_db_type(i_s, db_type)
    }

    fn internal_resolve_type_vars(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        class: Option<&Class<'db, '_>>,
        calculated_type_args: &CalculatedTypeArguments,
    ) -> DbType {
        match self {
            Self::ClassLike(c) => c.as_db_type(i_s).replace_type_vars(&mut |t| {
                calculated_type_args.lookup_type_var_usage(i_s, class, t)
            }),
            Self::Type(t) => t.replace_type_vars(&mut |t| {
                calculated_type_args.lookup_type_var_usage(i_s, class, t)
            }),
        }
    }

    pub fn any(
        &self,
        db: &'db Database,
        callable: &mut impl FnMut(&ClassLike<'db, '_>) -> bool,
    ) -> bool {
        match self {
            Self::ClassLike(class_like) => callable(class_like),
            Self::Type(t) => match t.as_ref() {
                DbType::Any => true,
                DbType::Union(union_type) => union_type
                    .iter()
                    .any(|t| Type::from_db_type(db, t).any(db, callable)),
                _ => todo!(),
            },
        }
    }

    pub fn common_base_class(&self, i_s: &mut InferenceState<'db, '_>, other: &Self) -> DbType {
        match (self, other) {
            (Self::ClassLike(ClassLike::Class(c1)), Self::ClassLike(ClassLike::Class(c2))) => {
                for (_, c1) in c1.mro(i_s) {
                    for (_, c2) in c2.mro(i_s) {
                        if c1
                            .matches(i_s, &Type::ClassLike(c2), None, Variance::Invariant)
                            .bool()
                        {
                            return c1.as_db_type(i_s);
                        }
                    }
                }
            }
            _ => return i_s.db.python_state.object_db_type(),
        }
        unreachable!("object is always a common base class")
    }

    pub fn is_any(&self) -> bool {
        matches!(self, Type::Type(t) if matches!(t.as_ref(), DbType::Any))
    }

    pub fn format(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        matcher: Option<&TypeVarMatcher<'db, '_>>,
        style: FormatStyle,
    ) -> Box<str> {
        match self {
            Self::ClassLike(c) => c.format(i_s, matcher, style),
            Self::Type(t) => t.format(i_s, matcher, style),
        }
    }
}
