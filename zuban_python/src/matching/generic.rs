use super::{FormatData, Match, Matcher, Type};
use crate::database::{GenericItem, Variance};
use crate::inference_state::InferenceState;

pub enum Generic<'a> {
    TypeArgument(Type<'a>),
    TypeVarTuple(()),
}

impl<'a> Generic<'a> {
    pub fn new(g: &'a GenericItem) -> Self {
        match g {
            GenericItem::TypeArgument(t) => Self::TypeArgument(Type::new(t)),
            GenericItem::TypeArguments(_) => todo!(),
        }
    }

    pub fn owned(g: GenericItem) -> Self {
        match g {
            GenericItem::TypeArgument(t) => Self::TypeArgument(Type::owned(t)),
            GenericItem::TypeArguments(_) => todo!(),
        }
    }

    pub fn into_generic_item(self, i_s: &mut InferenceState) -> GenericItem {
        match self {
            Self::TypeArgument(t) => GenericItem::TypeArgument(t.into_db_type(i_s)),
            Self::TypeVarTuple(_) => todo!(),
        }
    }

    pub fn format(&self, format_data: &FormatData) -> Box<str> {
        match self {
            Self::TypeArgument(t) => t.format(format_data),
            Self::TypeVarTuple(_) => todo!(),
        }
    }

    pub fn matches(
        &self,
        i_s: &mut InferenceState,
        matcher: &mut Matcher,
        other: Self,
        variance: Variance,
    ) -> Match {
        match self {
            Self::TypeArgument(t1) => match other {
                Self::TypeArgument(ref t2) => t1.matches(i_s, matcher, t2, variance),
                _ => todo!(),
            },
            Self::TypeVarTuple(_) => match other {
                Self::TypeVarTuple(ref t2) => todo!(),
                _ => todo!(),
            },
        }
    }

    pub fn overlaps(self, i_s: &mut InferenceState, other: Self) -> bool {
        match self {
            Self::TypeArgument(t1) => match other {
                Self::TypeArgument(ref t2) => t1.overlaps(i_s, t2),
                _ => todo!(),
            },
            Self::TypeVarTuple(_) => match other {
                Self::TypeVarTuple(ref t2) => todo!(),
                _ => todo!(),
            },
        }
    }

    pub fn expect_type_argument(self) -> Type<'a> {
        match self {
            Self::TypeArgument(t) => t,
            _ => todo!(),
        }
    }
}
