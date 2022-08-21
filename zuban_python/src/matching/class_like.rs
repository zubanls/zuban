use super::{Match, MismatchReason, Type, TypeVarMatcher};
use crate::database::{Database, DbType, FormatStyle, TypeVarUsage, Variance};
use crate::inference_state::InferenceState;
use crate::value::{Class, LookupResult, MroIterator};

#[derive(Debug, Clone, Copy)]
pub enum ClassLike<'db, 'a> {
    Class(Class<'db, 'a>),
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
            }
        };

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
