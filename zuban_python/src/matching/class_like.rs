use super::params::{has_overlapping_params, matches_params};
use super::{Generics, Match, MismatchReason, Type, TypeVarMatcher};
use crate::database::{Database, DbType, FormatStyle, TypeVarUsage, Variance};
use crate::inference_state::InferenceState;
use crate::value::{
    CallableClass, Class, Function, LookupResult, MroIterator, TupleClass, TypingClass, Value,
};

#[derive(Debug, Clone, Copy)]
pub enum ClassLike<'db, 'a> {
    Class(Class<'db, 'a>),
    Tuple(TupleClass<'a>),
    Callable(CallableClass<'a>),
    FunctionType(Function<'db, 'a>),
    Type(Class<'db, 'a>),
    TypeWithDbType(&'a DbType),
    TypeVar(&'a TypeVarUsage),
    TypingClass(TypingClass),
    TypingClassType(TypingClass),
    None,
    Never,
}

macro_rules! matches_callable {
    ($i_s:ident, $matcher:ident, $c1:ident, $c2:ident) => {{
        let other_result = $c2.result_type($i_s);
        ($c1.result_type($i_s).matches(
            $i_s,
            $matcher.as_deref_mut(),
            &other_result,
            Variance::Covariant,
        ) & matches_params($i_s, $matcher, $c1.param_iterator(), $c2.param_iterator()))
        .similar_if_false()
    }};
}

macro_rules! overlaps_callable {
    ($i_s:ident, $c1:ident, $c2:ident) => {{
        let other_result = $c2.result_type($i_s);
        $c1.result_type($i_s).overlaps($i_s, &other_result)
            && has_overlapping_params($i_s, $c1.param_iterator(), $c2.param_iterator())
    }};
}

impl<'db, 'a> ClassLike<'db, 'a> {
    pub fn matches(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        value_class: &Type<'db, '_>,
        mut matcher: Option<&mut TypeVarMatcher<'db, '_>>,
        variance: Variance,
    ) -> Match {
        // Note: we need to handle the MRO _in order_, so we need to extract
        // the elements from the set first, then handle them, even if we put
        // them back in a set afterwards.
        match value_class {
            Type::ClassLike(ClassLike::TypeVar(t2)) => {
                match self {
                    Self::TypeVar(t1) => {
                        if let Some(matcher) = matcher {
                            matcher.match_or_add_type_var(i_s, t1, value_class, variance)
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
            Type::ClassLike(ClassLike::None) => match variance {
                Variance::Contravariant => (matches!(self, Self::None)).into(),
                _ => Match::True,
            },
            Type::ClassLike(c) => {
                let mut similarity = Match::new_false();
                match variance {
                    Variance::Covariant => {
                        for (_, class_like) in c.mro(i_s) {
                            let m = self.check_match(
                                i_s,
                                matcher.as_deref_mut(),
                                &class_like,
                                variance,
                            );
                            if !matches!(m, Match::False(MismatchReason::None)) {
                                // The other mismatch reasons mean that the class kind of matched,
                                // but some generics had issues.
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
            /*
                            Self::TypeVar(t) => match value_class {
                                Type::ClassLike(class) => {
                                    if let Some(matcher) = matcher {
                                        matcher.match_or_add_type_var(i_s, t, value_class)
                                    } else {
                                        class.matches_type_var(t)
                                    }
                                }
                                Type::TypeVar(t2) => {
                                    if let Some(matcher) = matcher {
                                        matcher.match_or_add_type_var(i_s, t, value_class)
                                    } else {
                                        t.index == t2.index && t.type_ == t2.type_
                                    }
                                }
                                Type::Union(ref list) => {
                                    if let Some(matcher) = matcher {
                                        matcher.match_or_add_type_var(i_s, t, value_class)
                                    } else {
                                        todo!()
                                    }
                                }
                                Type::Any => {
                                    if let Some(matcher) = matcher {
                                        matcher.match_or_add_type_var(i_s, t, value_class)
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
                                        //matcher.match_or_add_type_var(i_s, t, value_class)
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
            Type::Any => Match::TrueWithAny,
        }
    }

    fn check_match(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        mut matcher: Option<&mut TypeVarMatcher<'db, '_>>,
        other: &Self,
        variance: Variance,
    ) -> Match {
        let matches = match self {
            Self::Class(c1) => match other {
                Self::Class(c2) => {
                    if c1.node_ref == c2.node_ref {
                        let type_vars = c1.type_vars(i_s);
                        return c1
                            .generics()
                            .matches(i_s, matcher, c2.generics(), variance, type_vars)
                            .similar_if_false();
                    }
                    false
                }
                _ => false,
            },
            Self::Type(_) | Self::TypeWithDbType(_) => {
                matches!(other, Self::Type(_) | Self::TypeWithDbType(_))
            }
            Self::TypeVar(t1) => {
                return match matcher {
                    Some(matcher) => {
                        matcher.match_or_add_type_var(i_s, t1, &Type::ClassLike(*other), variance)
                    }
                    None => match other {
                        Self::TypeVar(t2) => {
                            (t1.index == t2.index && t1.in_definition == t2.in_definition).into()
                        }
                        _ => Match::False(MismatchReason::None),
                    },
                }
            }
            Self::Tuple(t1) => {
                return match other {
                    Self::Tuple(t2) => {
                        let m: Match = t1.matches(i_s, t2, matcher, variance).into();
                        m.similar_if_false()
                    }
                    _ => Match::False(MismatchReason::None),
                }
            }
            Self::FunctionType(f1) => {
                return match other {
                    Self::Callable(c2) => matches_callable!(i_s, matcher, f1, c2),
                    Self::FunctionType(f2) => matches_callable!(i_s, matcher, f1, f2),
                    _ => Match::new_false(),
                };
            }
            Self::Callable(c1) => {
                return match other {
                    Self::Type(cls) => {
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
                        return Match::new_false();
                    }
                    Self::Callable(c2) => matches_callable!(i_s, matcher, c1, c2),
                    Self::FunctionType(f2) => matches_callable!(i_s, matcher, c1, f2),
                    _ => Match::new_false(),
                };
            }
            Self::TypingClass(c) => todo!(),
            Self::TypingClassType(c) => todo!(),
            Self::None => match variance {
                Variance::Contravariant => matches!(other, Self::None),
                _ => true,
            },
            Self::Never => todo!(),
        };
        if matches {
            let g1 = self.generics(i_s);
            let g2 = other.generics(i_s);
            g1.matches(i_s, matcher.as_deref_mut(), g2, variance, None)
                .similar_if_false()
        } else {
            Match::new_false()
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

    fn generics(&self, i_s: &mut InferenceState<'db, '_>) -> Generics<'db, '_> {
        match self {
            Self::Class(c) => c.generics(),
            Self::Type(c) => Generics::Class(c),
            Self::TypeWithDbType(g) => Generics::DbType(g),
            Self::Tuple(c) => c.generics(),
            Self::Callable(c) => unreachable!(),
            Self::FunctionType(f) => unreachable!(),
            Self::TypingClass(_)
            | Self::TypeVar(_)
            | Self::TypingClassType(_)
            | Self::Never
            | Self::None => Generics::None,
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
            Self::Type(c) => format!("Type[{}]", c.format(i_s, matcher, style)).into(),
            Self::TypeVar(t) => {
                if let Some(matcher) = matcher {
                    matcher.format(i_s, t, style)
                } else {
                    Box::from(t.type_var.name(i_s.db))
                }
            }
            Self::TypeWithDbType(g) => format!("Type[{}]", g.format(i_s, matcher, style)).into(),
            Self::Tuple(c) => c.format(i_s, matcher, style),
            Self::Callable(c) => c.format(i_s, matcher, style),
            Self::FunctionType(f) => f.format(i_s, matcher, style),
            Self::TypingClass(c) => todo!(),
            Self::TypingClassType(c) => todo!(),
            Self::None => Box::from("None"),
            // TODO this does not respect formatstyle
            Self::Never => Box::from("<nothing>"),
        }
    }

    pub fn mro(&self, i_s: &mut InferenceState<'db, '_>) -> MroIterator<'db, '_> {
        match self {
            Self::Class(c) => c.mro(i_s),
            Self::Tuple(t) => t.mro(i_s),
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
            Self::Type(c) => todo!(),
            _ => todo!("{name:?} {self:?}"),
        }
    }

    pub fn as_db_type(&self, i_s: &mut InferenceState<'db, '_>) -> DbType {
        match self {
            Self::Class(c) => c.as_db_type(i_s),
            Self::Type(c) => DbType::Type(Box::new(c.as_db_type(i_s))),
            Self::TypeWithDbType(g) => DbType::Type(Box::new((*g).clone())),
            Self::TypeVar(t) => DbType::TypeVar((*t).clone()),
            Self::Tuple(t) => t.as_db_type(),
            Self::Callable(c) => c.as_db_type(),
            Self::FunctionType(f) => f.as_db_type(i_s),
            Self::TypingClass(c) => c.as_db_type(),
            Self::TypingClassType(c) => DbType::Type(Box::new(c.as_db_type())),
            Self::None => DbType::None,
            Self::Never => DbType::Never,
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
                ClassLike::Type(c) => todo!("{c2:?}"),
                ClassLike::TypeWithDbType(d1) => match c2 {
                    ClassLike::Type(c) => todo!("{c2:?}"),
                    ClassLike::TypeWithDbType(d2) => {
                        let t2 = Type::from_db_type(i_s.db, d2);
                        Type::from_db_type(i_s.db, d1).overlaps(i_s, &t2)
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
                ClassLike::Tuple(t1) => match c2 {
                    ClassLike::Tuple(t2) => t1.overlaps(i_s, t2),
                    _ => false,
                },
                ClassLike::Callable(c1) => match c2 {
                    ClassLike::Callable(c2) => overlaps_callable!(i_s, c1, c2),
                    ClassLike::FunctionType(f2) => todo!(),
                    _ => todo!(),
                },
                ClassLike::FunctionType(f) => todo!("{c2:?}"),
                ClassLike::TypingClass(c) => todo!("{c2:?}"),
                ClassLike::TypingClassType(c) => todo!("{c2:?}"),
                ClassLike::None => matches!(other, Self::None),
                ClassLike::Never => todo!(),
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
