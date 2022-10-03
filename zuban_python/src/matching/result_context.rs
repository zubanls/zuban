use std::fmt;

use super::{Type, TypeVarMatcher};
use crate::InferenceState;

pub enum ResultContext<'a, 'b> {
    Known(&'a Type<'a>),
    WithMatcher {
        matcher: &'a mut TypeVarMatcher<'b>,
        type_: &'a Type<'a>,
    },
    Unknown,
}

impl<'a> ResultContext<'a, '_> {
    pub fn with_type_if_exists<'db, T>(
        &mut self,
        i_s: &mut InferenceState<'db, '_>,
        callable: impl FnOnce(&mut InferenceState<'db, '_>, &Type<'_>, Option<&mut TypeVarMatcher>) -> T,
    ) -> Option<T> {
        match self {
            Self::Known(t) => Some(callable(i_s, t, None)),
            Self::WithMatcher { matcher, type_ } => {
                let t = type_.as_db_type(i_s);
                let t = matcher.replace_type_vars_for_nested_context(i_s, &t);
                Some(callable(i_s, &Type::new(&t), Some(matcher)))
            }
            Self::Unknown => None,
        }
    }
}

impl fmt::Debug for ResultContext<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Known(t) => write!(f, "Known({t:?})"),
            Self::WithMatcher { .. } => write!(f, "WithMatcher(_)"),
            Self::Unknown => write!(f, "UnKnown"),
        }
    }
}
