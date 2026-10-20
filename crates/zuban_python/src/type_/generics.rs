use std::{borrow::Cow, sync::Arc};

use crate::{
    params::matches_params_with_variance,
    prelude::*,
    type_::{
        TypeVarIndex, format_callable_params, format_params_as_param_spec,
        match_tuple_type_arguments,
    },
    utils::{arc_slice_into_vec, join_with_commas},
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct TypeArgs {
    pub args: TupleArgs,
}

impl TypeArgs {
    pub fn new(args: TupleArgs) -> Self {
        Self { args }
    }

    pub fn new_arbitrary_from_error() -> Self {
        TypeArgs {
            args: TupleArgs::new_arbitrary_from_error(),
        }
    }

    pub fn new_arbitrary_length(arg: Type) -> Self {
        Self::new(TupleArgs::ArbitraryLen(Arc::new(arg)))
    }

    pub fn format(&self, format_data: &FormatData) -> Option<Box<str>> {
        let result = self.args.format(format_data);
        if matches!(self.args, TupleArgs::ArbitraryLen(_)) {
            Some(format!("Unpack[Tuple[{result}]]").into())
        } else {
            (!self.args.is_empty()).then_some(result)
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum GenericItem {
    TypeArg(Type),
    // For TypeVarTuple
    TypeArgs(TypeArgs),
    // For ParamSpec
    ParamSpecArg(ParamSpecArg),
}

impl GenericItem {
    pub fn format(&self, format_data: &FormatData) -> Option<Box<str>> {
        match self {
            Self::TypeArg(t) => Some(t.format(format_data)),
            Self::TypeArgs(ts) => ts.format(format_data),
            Self::ParamSpecArg(args) => Some(match &args.params {
                CallableParams::Simple(params) => format_params_as_param_spec(format_data, params)
                    .unwrap_or_else(|| {
                        format!(
                            "[{}]",
                            &format_callable_params(format_data, false, params.iter(), false, None)
                        )
                        .into()
                    }),
                CallableParams::Any(_) => Box::from("[*Any, **Any]"),
            }),
        }
    }

    pub fn matches(
        &self,
        i_s: &InferenceState,
        matcher: &mut Matcher,
        other: &Self,
        variance: Variance,
    ) -> Match {
        if matcher.is_matching_reverse() {
            return matcher
                .match_reverse(|matcher| other.matches(i_s, matcher, self, variance.invert()));
        }
        match self {
            Self::TypeArg(t1) => match other {
                Self::TypeArg(t2) => t1.matches(i_s, matcher, t2, variance),
                _ => unreachable!(),
            },
            Self::TypeArgs(ts1) => match other {
                Self::TypeArgs(ts2) => {
                    match_tuple_type_arguments(i_s, matcher, &ts1.args, &ts2.args, variance)
                }
                _ => unreachable!(),
            },
            Self::ParamSpecArg(p1) => match other {
                Self::ParamSpecArg(p2) => {
                    matches_params_with_variance(i_s, matcher, &p1.params, &p2.params, variance)
                }
                _ => unreachable!(),
            },
        }
    }

    pub fn overlaps(&self, i_s: &InferenceState, matcher: &mut Matcher, other: &Self) -> bool {
        match self {
            Self::TypeArg(t1) => match other {
                Self::TypeArg(t2) => t1.overlaps(i_s, matcher, t2),
                _ => unreachable!(),
            },
            Self::TypeArgs(ts1) => match other {
                Self::TypeArgs(ts2) => ts1.args.overlaps(i_s, matcher, &ts2.args),
                _ => unreachable!(),
            },
            Self::ParamSpecArg(_) => match other {
                // I'm not sure why Mypy decided that ParamSpecs always overlap.
                Self::ParamSpecArg(_) => true,
                _ => unreachable!(),
            },
        }
    }

    pub fn merge_matching_parts(&self, db: &Database, other: &Self) -> GenericItem {
        match self {
            Self::TypeArg(t1) => {
                let Self::TypeArg(t2) = other else {
                    unreachable!()
                };
                Self::TypeArg(t1.merge_matching_parts(db, t2))
            }
            Self::TypeArgs(ts1) => {
                let Self::TypeArgs(ts2) = other else {
                    unreachable!()
                };
                Self::TypeArgs(TypeArgs::new(ts1.args.merge_matching_parts(db, &ts2.args)))
            }
            // TODO This is not correct, we could try to merge, but is it really important? It's
            // not a big issue that Any is returned here, because this is only for fallbacks in case
            // of errors.
            Self::ParamSpecArg(_) => Self::ParamSpecArg(ParamSpecArg::new_any(AnyCause::FromError)),
        }
    }

    pub fn find_in_type(&self, db: &Database, check: &mut impl FnMut(&Type) -> bool) -> bool {
        match self {
            Self::TypeArg(t) => t.find_in_type(db, check),
            Self::TypeArgs(ts) => match &ts.args {
                TupleArgs::FixedLen(ts) => ts.iter().any(|t| t.find_in_type(db, check)),
                TupleArgs::ArbitraryLen(t) => t.find_in_type(db, check),
                TupleArgs::WithUnpack(with_unpack) => with_unpack.find_in_type(db, check),
            },
            Self::ParamSpecArg(a) => a.params.find_in_type(db, check),
        }
    }

    pub fn maybe_any(&self) -> Option<AnyCause> {
        match self {
            Self::TypeArg(Type::Any(cause)) => Some(*cause),
            Self::TypeArg(_) => None,
            Self::TypeArgs(ts) => ts.args.maybe_any(),
            Self::ParamSpecArg(p) => match p.params {
                CallableParams::Any(cause) => Some(cause),
                _ => None,
            },
        }
    }
}

pub(crate) trait GenericItemCowExt<'a> {
    fn expect_type_argument(self) -> Cow<'a, Type>;
    fn expect_type_arguments(self) -> Cow<'a, TypeArgs>;
    fn expect_param_spec_arg(self) -> Cow<'a, ParamSpecArg>;
}

impl<'a> GenericItemCowExt<'a> for Cow<'a, GenericItem> {
    fn expect_type_argument(self) -> Cow<'a, Type> {
        match self {
            Cow::Borrowed(GenericItem::TypeArg(t)) => Cow::Borrowed(t),
            Cow::Owned(GenericItem::TypeArg(t)) => Cow::Owned(t),
            _ => unreachable!(),
        }
    }

    fn expect_type_arguments(self) -> Cow<'a, TypeArgs> {
        match self {
            Cow::Borrowed(GenericItem::TypeArgs(ts)) => Cow::Borrowed(ts),
            Cow::Owned(GenericItem::TypeArgs(ts)) => Cow::Owned(ts),
            _ => unreachable!(),
        }
    }

    fn expect_param_spec_arg(self) -> Cow<'a, ParamSpecArg> {
        match self {
            Cow::Borrowed(GenericItem::ParamSpecArg(p)) => Cow::Borrowed(p),
            Cow::Owned(GenericItem::ParamSpecArg(p)) => Cow::Owned(p),
            _ => unreachable!(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum ClassGenerics {
    List(GenericsList),
    // A class definition (no type vars or stuff like callables)
    ExpressionWithClassType(PointLink),
    // Multiple class definitions, e.g. [int, str], but not [T, str]
    SlicesWithClassTypes(PointLink),
    NotDefinedYet,
    None { might_be_promoted: bool },
}

impl ClassGenerics {
    pub const fn new_none() -> Self {
        Self::None {
            might_be_promoted: true,
        }
    }

    pub fn all_any(&self) -> bool {
        match self {
            Self::List(list) => list.iter().all(|g| g.maybe_any().is_some()),
            Self::NotDefinedYet => true,
            _ => false,
        }
    }

    pub fn all_any_with_unknown_type_params(&self) -> bool {
        match self {
            Self::List(list) => list
                .iter()
                .all(|g| g.maybe_any() == Some(AnyCause::UnknownTypeParam)),
            _ => false,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct GenericsList(Arc<[GenericItem]>);

impl GenericsList {
    pub fn new_generics(parts: Arc<[GenericItem]>) -> Self {
        debug_assert!(!parts.is_empty());
        Self(parts)
    }

    pub fn generics_from_vec(parts: Vec<GenericItem>) -> Self {
        Self::new_generics(Arc::from(parts))
    }

    pub fn nth(&self, index: TypeVarIndex) -> Option<&GenericItem> {
        self.0.get(index.0 as usize)
    }

    pub fn iter(&self) -> std::slice::Iter<'_, GenericItem> {
        self.0.iter()
    }

    pub fn format(&self, format_data: &FormatData) -> Box<str> {
        join_with_commas(self.0.iter().filter_map(|g| g.format(format_data))).into()
    }

    pub fn has_param_spec(&self) -> bool {
        self.iter()
            .any(|g| matches!(g, GenericItem::ParamSpecArg(_)))
    }

    pub fn has_type_vars(&self) -> bool {
        let mut result = false;
        self.search_type_vars(&mut |_| result = true);
        result
    }

    pub fn into_vec(self) -> Vec<GenericItem> {
        arc_slice_into_vec(self.0)
    }
}

impl std::ops::Index<TypeVarIndex> for GenericsList {
    type Output = GenericItem;

    fn index(&self, index: TypeVarIndex) -> &Self::Output {
        &self.0[index.0 as usize]
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct ParamSpecTypeVars {
    pub type_vars: TypeVarLikes,
    pub in_definition: PointLink,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct ParamSpecArg {
    pub params: CallableParams,
    pub type_vars: Option<ParamSpecTypeVars>,
}

impl ParamSpecArg {
    pub fn new(params: CallableParams, type_vars: Option<ParamSpecTypeVars>) -> Self {
        Self { params, type_vars }
    }

    pub fn new_any(cause: AnyCause) -> Self {
        Self {
            params: CallableParams::Any(cause),
            type_vars: None,
        }
    }
}
