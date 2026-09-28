use std::sync::Arc;

use crate::{
    database::PointLink,
    format_data::FormatData,
    matching::Generic,
    type_::{
        AnyCause, CallableParams, TupleArgs, Type, TypeVarIndex, TypeVarLikeUsage, TypeVarLikes,
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
        join_with_commas(
            self.0
                .iter()
                .filter_map(|g| Generic::new(g).format(format_data)),
        )
        .into()
    }

    pub fn has_param_spec(&self) -> bool {
        self.iter()
            .any(|g| matches!(g, GenericItem::ParamSpecArg(_)))
    }

    pub(super) fn search_type_vars<C: FnMut(TypeVarLikeUsage) + ?Sized>(
        &self,
        found_type_var: &mut C,
    ) {
        for g in self.iter() {
            match g {
                GenericItem::TypeArg(t) => t.search_type_vars(found_type_var),
                GenericItem::TypeArgs(ts) => ts.args.search_type_vars(found_type_var),
                GenericItem::ParamSpecArg(p) => p.params.search_type_vars(found_type_var),
            }
        }
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
