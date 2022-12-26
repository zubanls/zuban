use std::fmt;

use super::{Matcher, Type};
use crate::InferenceState;

pub enum ResultContext<'a, 'b> {
    Known(&'a Type<'a>),
    WithMatcher {
        matcher: &'a mut Matcher<'b>,
        type_: &'a Type<'a>,
    },
    Unknown,
}

impl<'a> ResultContext<'a, '_> {
    pub fn with_type_if_exists_and_replace_type_var_likes<'db, T>(
        &mut self,
        i_s: &mut InferenceState<'db, '_>,
        callable: impl FnOnce(&mut InferenceState<'db, '_>, &Type<'_>) -> T,
    ) -> Option<T> {
        match self {
            Self::Known(type_) => Some(callable(i_s, type_)),
            Self::WithMatcher { matcher, type_ } => {
                let t = type_.as_db_type(i_s);
                let t = matcher.replace_type_var_likes_for_nested_context(i_s, &t);
                Some(callable(i_s, &Type::new(&t)))
            }
            Self::Unknown => None,
        }
    }

    pub fn with_type_if_exists<'db, T>(
        &mut self,
        i_s: &mut InferenceState<'db, '_>,
        callable: impl FnOnce(&mut InferenceState<'db, '_>, &Type<'_>, &mut Matcher) -> T,
    ) -> Option<T> {
        match self {
            Self::Known(type_) => Some(callable(i_s, type_, &mut Matcher::default())),
            Self::WithMatcher { matcher, type_ } => Some(callable(i_s, type_, matcher)),
            Self::Unknown => None,
        }
    }
}

impl fmt::Debug for ResultContext<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Known(t) => write!(f, "Known({t:?})"),
            Self::WithMatcher { type_, .. } => write!(f, "WithMatcher(_, {type_:?})"),
            Self::Unknown => write!(f, "Unknown"),
        }
    }
}
