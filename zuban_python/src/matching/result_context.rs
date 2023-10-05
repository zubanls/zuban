use std::fmt;

use super::{Matcher, Type};
use crate::database::{DbType, TupleTypeArguments, TypeOrTypeVarTuple};
use crate::{debug, InferenceState};

pub enum ResultContext<'a, 'b> {
    Known(&'a DbType),
    WithMatcher {
        matcher: &'a mut Matcher<'b>,
        type_: &'a DbType,
    },
    AssignmentNewDefinition,
    Unknown,
    ExpectLiteral,
    ExpectUnused,
    RevealType,
}

impl<'a> ResultContext<'a, '_> {
    pub fn with_type_if_exists_and_replace_type_var_likes<'db, T>(
        &self,
        i_s: &InferenceState<'db, '_>,
        callable: impl FnOnce(&InferenceState<'db, '_>, Type<'_>) -> T,
    ) -> Option<T> {
        match self {
            Self::Known(type_) => Some(callable(i_s, Type::new(type_))),
            Self::WithMatcher { matcher, type_ } => {
                let t = matcher.replace_type_var_likes_for_nested_context(i_s.db, type_);
                Some(callable(i_s, Type::new(&t)))
            }
            Self::Unknown
            | Self::AssignmentNewDefinition
            | Self::ExpectLiteral
            | Self::ExpectUnused
            | Self::RevealType => None,
        }
    }

    pub fn with_type_if_exists<'db, T>(
        &mut self,
        i_s: &InferenceState<'db, '_>,
        callable: impl FnOnce(&InferenceState<'db, '_>, Type<'_>, &mut Matcher) -> T,
    ) -> Option<T> {
        match self {
            Self::Known(type_) => Some(callable(i_s, Type::new(type_), &mut Matcher::default())),
            Self::WithMatcher { matcher, type_ } => Some(callable(i_s, Type::new(type_), matcher)),
            Self::Unknown
            | Self::AssignmentNewDefinition
            | Self::ExpectLiteral
            | Self::ExpectUnused
            | Self::RevealType => None,
        }
    }

    pub fn has_explicit_type(&self) -> bool {
        matches!(self, Self::Known(_) | Self::WithMatcher { .. })
    }

    pub fn is_literal_context<'db>(&self, i_s: &InferenceState<'db, '_>) -> bool {
        if matches!(self, Self::ExpectLiteral | Self::RevealType)
            || i_s.is_calculating_enum_members()
        {
            return true;
        }
        self.with_type_if_exists_and_replace_type_var_likes(
            i_s,
            |i_s: &InferenceState<'db, '_>, type_| match type_.as_ref() {
                DbType::Literal(_) | DbType::EnumMember(_) => true,
                DbType::Union(items) => items
                    .iter()
                    .any(|i| matches!(i, DbType::Literal(_) | DbType::EnumMember(_))),
                _ => false,
            },
        )
        .unwrap_or(false)
    }

    pub fn expects_union(&self, i_s: &InferenceState) -> bool {
        match self {
            Self::Known(type_) | Self::WithMatcher { type_, .. } => {
                matches!(type_, DbType::Union(_))
            }
            Self::Unknown
            | Self::ExpectLiteral
            | Self::ExpectUnused
            | Self::RevealType
            | Self::AssignmentNewDefinition => false,
        }
    }

    pub fn expect_not_none(&mut self, i_s: &InferenceState) -> bool {
        self.with_type_if_exists(i_s, |i_s, type_, matcher| {
            !matches!(type_.as_ref(), DbType::None)
        })
        .unwrap_or_else(|| !matches!(self, Self::ExpectUnused | Self::RevealType))
    }

    pub fn with_tuple_context_iterator<T>(
        &mut self,
        i_s: &InferenceState,
        mut callable: impl FnMut(TupleContextIterator) -> T,
    ) -> T {
        self.with_type_if_exists_and_replace_type_var_likes(i_s, |i_s: &InferenceState, type_| {
            match type_.as_ref() {
                DbType::Tuple(tup) => tup.args.as_ref().map(|args| match args {
                    TupleTypeArguments::FixedLength(ts) => {
                        callable(TupleContextIterator::FixedLength(ts.iter()))
                    }
                    TupleTypeArguments::ArbitraryLength(t) => {
                        callable(TupleContextIterator::ArbitraryLength(t))
                    }
                }),
                DbType::Union(items) => {
                    debug!("TODO union tuple inference context ignored");
                    None
                }
                // Case x: Iterable[int] = (1, 1)
                DbType::Class(c) if c.link == i_s.db.python_state.iterable_link() => {
                    let t = c.class(i_s.db).nth_type_argument(i_s.db, 0);
                    Some(callable(TupleContextIterator::ArbitraryLength(&t)))
                }
                _ => None,
            }
        })
        .flatten()
        .unwrap_or_else(|| {
            callable(match self {
                Self::ExpectLiteral | Self::RevealType => TupleContextIterator::ExpectLiterals,
                _ => TupleContextIterator::Unknown,
            })
        })
    }
}

impl fmt::Debug for ResultContext<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Known(t) => write!(f, "Known({t:?})"),
            Self::WithMatcher { type_, .. } => write!(f, "WithMatcher(_, {type_:?})"),
            Self::Unknown => write!(f, "Unknown"),
            Self::ExpectLiteral => write!(f, "ExpectLiteral"),
            Self::ExpectUnused => write!(f, "ExpectUnused"),
            Self::RevealType => write!(f, "RevealType"),
            Self::AssignmentNewDefinition => write!(f, "AssignmentNewDefinition"),
        }
    }
}

pub enum TupleContextIterator<'a> {
    ArbitraryLength(&'a DbType),
    FixedLength(std::slice::Iter<'a, TypeOrTypeVarTuple>),
    ExpectLiterals,
    Unknown,
}

impl<'a> Iterator for TupleContextIterator<'a> {
    type Item = ResultContext<'a, 'a>;

    fn next(&mut self) -> Option<Self::Item> {
        Some(match self {
            Self::ArbitraryLength(t) => ResultContext::Known(t),
            Self::FixedLength(items) => {
                match items.next() {
                    Some(TypeOrTypeVarTuple::Type(t)) => ResultContext::Known(t),
                    Some(TypeOrTypeVarTuple::TypeVarTuple(_)) => {
                        // Clear the remaining items, because the order of the following items is
                        // unclear.
                        *items = [].iter();
                        todo!("Probably return ResultContext::Unknown here")
                    }
                    None => ResultContext::Unknown,
                }
            }
            Self::ExpectLiterals => ResultContext::ExpectLiteral,
            Self::Unknown => ResultContext::Unknown,
        })
    }
}
