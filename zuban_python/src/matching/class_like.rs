use super::{Match, MismatchReason, Type, TypeVarMatcher};
use crate::database::{Database, DbType, FormatStyle, TypeVarUsage, Variance};
use crate::inference_state::InferenceState;
use crate::value::{Class, LookupResult, MroIterator};

#[derive(Debug, Clone, Copy)]
pub enum ClassLike<'db, 'a> {
    Class(Class<'db, 'a>),
    TypeVar(&'a TypeVarUsage),
}

impl<'db, 'a> ClassLike<'db, 'a> {
    pub fn matches(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        value_type: &Type<'db, '_>,
        mut matcher: Option<&mut TypeVarMatcher<'db, '_>>,
        variance: Variance,
    ) -> Match {
        // Note: we need to handle the MRO _in order_, so we need to extract
        // the elements from the set first, then handle them, even if we put
        // them back in a set afterwards.
        match value_type {
            Type::ClassLike(ClassLike::TypeVar(t2)) => {
                match self {
                    Self::TypeVar(t1) => {
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
                            self.matches(i_s, &Type::from_db_type(i_s.db, bound), None, variance)
                        } else if !t2.type_var.restrictions.is_empty() {
                            t2.type_var
                                .restrictions
                                .iter()
                                .any(|r| {
                                    self.matches(
                                        i_s,
                                        &Type::from_db_type(i_s.db, r),
                                        None,
                                        variance,
                                    )
                                    .bool()
                                })
                                .into()
                        } else {
                            self.is_object_class(i_s.db)
                        }
                    }
                }
            }
            Type::ClassLike(c) => {
                let mut similarity = Match::new_false();
                match variance {
                    Variance::Covariant => {
                        for (i, (_, class_like)) in c.mro(i_s).enumerate() {
                            let m = self.check_match(
                                i_s,
                                matcher.as_deref_mut(),
                                &class_like,
                                variance,
                            );
                            if !matches!(m, Match::False(MismatchReason::None)) {
                                return m;
                            }
                        }
                    }
                    Variance::Invariant => {
                        similarity = self.check_match(i_s, matcher, c, variance);
                        if similarity.bool() {
                            return similarity;
                        }
                    }
                    Variance::Contravariant => {
                        for (_, class_like) in self.mro(i_s) {
                            let m =
                                class_like.check_match(i_s, matcher.as_deref_mut(), c, variance);
                            if !matches!(m, Match::False(MismatchReason::None)) {
                                return m;
                            }
                        }
                    }
                }
                // TODO this should probably be checked before normal mro checking?!
                if let Self::Class(c1) = self {
                    if c1.class_infos(i_s).is_protocol {
                        return match c {
                            ClassLike::Class(c2) => c1.check_protocol_match(i_s, *c2).into(),
                            _ => Match::new_false(),
                        };
                    }
                }
                similarity
            }
            Type::Type(t2) => {
                match t2.as_ref() {
                    DbType::Never => Match::True, // TODO is this correct?????
                    _ => todo!(),
                }
            }
            /*
                            Self::TypeVar(t) => match value_type {
                                Type::ClassLike(class) => {
                                    if let Some(matcher) = matcher {
                                        matcher.match_or_add_type_var(i_s, t, value_type)
                                    } else {
                                        class.matches_type_var(t)
                                    }
                                }
                                Type::TypeVar(t2) => {
                                    if let Some(matcher) = matcher {
                                        matcher.match_or_add_type_var(i_s, t, value_type)
                                    } else {
                                        t.index == t2.index && t.type_ == t2.type_
                                    }
                                }
                                Type::Union(ref list) => {
                                    if let Some(matcher) = matcher {
                                        matcher.match_or_add_type_var(i_s, t, value_type)
                                    } else {
                                        todo!()
                                    }
                                }
                                Type::Any => {
                                    if let Some(matcher) = matcher {
                                        matcher.match_or_add_type_var(i_s, t, value_type)
                                    } else {
                                        true
                                    }
                                }
                                Type::Never => {
                                    todo!()
                                }
                                Type::None => {
                                    if let Some(matcher) = matcher {
                                        todo!()
                                        //matcher.match_or_add_type_var(i_s, t, value_type)
                                    } else {
                                        true // TODO is this correct? Maybe depending on strict options?
                                    }
                                }
                            },
            */
            Type::Union(list) => match self {
                Self::Class(c1) if variance == Variance::Covariant => c1.is_object_class(i_s.db),
                _ => Match::new_false(),
            },
        }
    }

    fn check_match(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        matcher: Option<&mut TypeVarMatcher<'db, '_>>,
        other: &Self,
        variance: Variance,
    ) -> Match {
        match self {
            Self::Class(c1) => match other {
                Self::Class(c2) => {
                    if c1.node_ref == c2.node_ref {
                        let type_vars = c1.type_vars(i_s);
                        return c1
                            .generics()
                            .matches(i_s, matcher, c2.generics(), variance, type_vars)
                            .similar_if_false();
                    }
                    Match::new_false()
                }
                _ => Match::new_false(),
            },
            Self::TypeVar(t1) => match matcher {
                Some(matcher) => {
                    matcher.match_or_add_type_var(i_s, t1, &Type::ClassLike(*other), variance)
                }
                None => match other {
                    Self::TypeVar(t2) => {
                        (t1.index == t2.index && t1.in_definition == t2.in_definition).into()
                    }
                    _ => Match::False(MismatchReason::None),
                },
            },
        }
    }

    fn matches_type_var(&self, i_s: &mut InferenceState<'db, '_>, t2: &TypeVarUsage) -> bool {
        if let Self::TypeVar(t1) = self {
            if t1.index == t2.index && t1.in_definition == t2.in_definition {
                return true;
            }
        }
        if let Some(bound) = &t2.type_var.bound {
            self.matches(
                i_s,
                &Type::from_db_type(i_s.db, bound),
                None,
                Variance::Covariant,
            )
            .bool()
        } else if !t2.type_var.restrictions.is_empty() {
            t2.type_var.restrictions.iter().any(|r| {
                self.matches(
                    i_s,
                    &Type::from_db_type(i_s.db, r),
                    None,
                    Variance::Covariant,
                )
                .bool()
            })
        } else {
            false
        }
    }

    fn is_object_class(&self, db: &Database) -> Match {
        match self {
            Self::Class(c) => c.is_object_class(db),
            _ => Match::new_false(),
        }
    }

    pub fn format(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        matcher: Option<&TypeVarMatcher<'db, '_>>,
        style: FormatStyle,
    ) -> Box<str> {
        match self {
            Self::Class(c) => c.format(i_s, matcher, style),
            Self::TypeVar(t) => {
                if let Some(matcher) = matcher {
                    matcher.format(i_s, t, style)
                } else {
                    Box::from(t.type_var.name(i_s.db))
                }
            }
        }
    }

    fn mro(&self, i_s: &mut InferenceState<'db, '_>) -> MroIterator<'db, '_> {
        match self {
            Self::Class(c) => c.mro(i_s),
            _ => MroIterator::new(i_s.db, *self, None, [].iter()),
        }
    }

    pub fn lookup_symbol(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        name: &str,
    ) -> LookupResult<'db> {
        match self {
            Self::Class(c) => c.lookup_symbol(i_s, name),
            _ => todo!("{name:?} {self:?}"),
        }
    }

    pub fn as_db_type(&self, i_s: &mut InferenceState<'db, '_>) -> DbType {
        match self {
            Self::Class(c) => c.as_db_type(i_s),
            Self::TypeVar(t) => DbType::TypeVar((*t).clone()),
        }
    }

    pub fn overlaps(&self, i_s: &mut InferenceState<'db, '_>, other: &Self) -> bool {
        let check = {
            #[inline]
            |i_s: &mut _, c1: &_, c2: &_| match c1 {
                ClassLike::Class(c1) => match c2 {
                    ClassLike::Class(c2) if c1.node_ref == c2.node_ref => {
                        let type_vars = c1.type_vars(i_s);
                        c1.generics().overlaps(i_s, c2.generics(), type_vars)
                    }
                    _ => false,
                },
                ClassLike::TypeVar(t) => {
                    if let Some(db_t) = &t.type_var.bound {
                        Type::from_db_type(i_s.db, db_t).overlaps(i_s, &Type::ClassLike(*c2))
                    } else if !t.type_var.restrictions.is_empty() {
                        todo!("{c2:?}")
                    } else {
                        true
                    }
                }
            }
        };

        if let ClassLike::TypeVar(t) = other {
            return if let Some(bound) = &t.type_var.bound {
                Type::ClassLike(*self).overlaps(i_s, &Type::from_db_type(i_s.db, bound))
            } else if !t.type_var.restrictions.is_empty() {
                todo!("{self:?}")
            } else {
                true
            };
        }

        match self {
            Self::Class(c1) => match other {
                Self::Class(c2) => {
                    for (_, c1) in c1.mro(i_s) {
                        if check(i_s, &c1, other) {
                            return true;
                        }
                    }
                    for (_, c2) in c2.mro(i_s) {
                        if check(i_s, self, &c2) {
                            return true;
                        }
                    }
                    false
                }
                _ => false,
            },
            _ => check(i_s, self, other),
        }
    }
}
