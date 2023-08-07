use std::fmt;

use super::{Matcher, Type};
use crate::database::DbType;
use crate::InferenceState;

pub enum ResultContext<'a, 'b> {
    Known(&'a Type<'a>),
    WithMatcher {
        matcher: &'a mut Matcher<'b>,
        type_: &'a Type<'a>,
    },
    AssignmentNewDefinition,
    Unknown,
    ExpectLiteral,
}

impl<'a> ResultContext<'a, '_> {
    pub fn with_type_if_exists_and_replace_type_var_likes<'db, T>(
        &self,
        i_s: &InferenceState<'db, '_>,
        callable: impl FnOnce(&InferenceState<'db, '_>, &Type<'_>) -> T,
    ) -> Option<T> {
        match self {
            Self::Known(type_) => Some(callable(i_s, type_)),
            Self::WithMatcher { matcher, type_ } => {
                let t = type_.as_db_type();
                let t = matcher.replace_type_var_likes_for_nested_context(i_s.db, &t);
                Some(callable(i_s, &Type::new(&t)))
            }
            Self::Unknown | Self::AssignmentNewDefinition | Self::ExpectLiteral => None,
        }
    }

    pub fn with_type_if_exists<'db, T>(
        &mut self,
        i_s: &InferenceState<'db, '_>,
        callable: impl FnOnce(&InferenceState<'db, '_>, &Type<'_>, &mut Matcher) -> T,
    ) -> Option<T> {
        match self {
            Self::Known(type_) => Some(callable(i_s, type_, &mut Matcher::default())),
            Self::WithMatcher { matcher, type_ } => Some(callable(i_s, type_, matcher)),
            Self::Unknown | Self::AssignmentNewDefinition | Self::ExpectLiteral => None,
        }
    }

    pub fn is_literal_context<'db>(&self, i_s: &InferenceState<'db, '_>) -> bool {
        if matches!(self, Self::ExpectLiteral) || i_s.is_calculating_enum_members() {
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
                matches!(type_.as_ref(), DbType::Union(_))
            }
            Self::Unknown | Self::ExpectLiteral | Self::AssignmentNewDefinition => false,
        }
    }
}

impl fmt::Debug for ResultContext<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Known(t) => write!(f, "Known({t:?})"),
            Self::WithMatcher { type_, .. } => write!(f, "WithMatcher(_, {type_:?})"),
            Self::Unknown => write!(f, "Unknown"),
            Self::ExpectLiteral => write!(f, "ExpectLiteral"),
            Self::AssignmentNewDefinition => write!(f, "AssignmentNewDefinition"),
        }
    }
}
