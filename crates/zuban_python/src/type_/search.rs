use super::{
    ClassGenerics, GenericClass, GenericsList, ParamType, StarParamType, StarStarParamType,
    TupleUnpack, TypedDictGenerics,
};

use crate::{prelude::*, type_::WithUnpack};

pub(crate) trait SearchTypeVars {
    fn search_type_vars<C: FnMut(TypeVarLikeUsage) + ?Sized>(&self, found_type_var: &mut C);
}

impl SearchTypeVars for Type {
    fn search_type_vars<C: FnMut(TypeVarLikeUsage) + ?Sized>(&self, found_type_var: &mut C) {
        match self {
            Self::Class(GenericClass {
                generics: ClassGenerics::List(generics),
                ..
            }) => generics.search_type_vars(found_type_var),
            Self::Union(u) => {
                for t in u.iter() {
                    t.search_type_vars(found_type_var);
                }
            }
            Self::FunctionOverload(intersection) => {
                for callable in intersection.iter_functions() {
                    callable.search_type_vars(found_type_var);
                }
            }
            Self::TypeVar(t) => found_type_var(TypeVarLikeUsage::TypeVar(t.clone())),
            Self::Type(type_) => type_.search_type_vars(found_type_var),
            Self::Tuple(tup) => tup.args.search_type_vars(found_type_var),
            Self::Callable(c) => c.search_type_vars(found_type_var),
            Self::Class(..)
            | Self::Any(_)
            | Self::None
            | Self::Never(_)
            | Self::Literal { .. }
            | Self::Module(_)
            | Self::Self_
            | Self::Namespace(_)
            | Self::Super { .. }
            | Self::CustomBehavior(_)
            | Self::DataclassTransformObj(_)
            | Self::Enum(_)
            | Self::EnumMember(_)
            | Self::NewType(_)
            | Self::Sentinel(_)
            | Self::LiteralString { .. } => (),
            Self::RecursiveType(rec) => {
                if let Some(generics) = rec.generics.as_ref() {
                    generics.search_type_vars(found_type_var)
                }
            }
            Self::ParamSpecArgs(usage) => {
                found_type_var(TypeVarLikeUsage::ParamSpec(usage.clone()))
            }
            Self::ParamSpecKwargs(usage) => {
                found_type_var(TypeVarLikeUsage::ParamSpec(usage.clone()))
            }
            Self::Dataclass(d) => {
                if let ClassGenerics::List(generics) = &d.class.generics {
                    generics.search_type_vars(found_type_var)
                }
            }
            Self::TypedDict(d) => d.search_type_vars(found_type_var),
            Self::NamedTuple(_) => {
                debug!("TODO do we need to support namedtuple searching for type vars?");
            }
            Self::Intersection(i) => {
                for t in i.iter_entries() {
                    t.search_type_vars(found_type_var)
                }
            }
            Self::TypeForm(tf) => tf.search_type_vars(found_type_var),
        }
    }
}

impl SearchTypeVars for GenericsList {
    fn search_type_vars<C: FnMut(TypeVarLikeUsage) + ?Sized>(&self, found_type_var: &mut C) {
        for g in self.iter() {
            match g {
                Generic::TypeArg(t) => t.search_type_vars(found_type_var),
                Generic::TypeArgs(ts) => ts.args.search_type_vars(found_type_var),
                Generic::ParamSpecArg(p) => p.params.search_type_vars(found_type_var),
            }
        }
    }
}

impl SearchTypeVars for TupleArgs {
    fn search_type_vars<C: FnMut(TypeVarLikeUsage) + ?Sized>(&self, found_type_var: &mut C) {
        match self {
            TupleArgs::FixedLen(ts) => {
                for t in ts.iter() {
                    t.search_type_vars(found_type_var)
                }
            }
            TupleArgs::ArbitraryLen(t) => t.search_type_vars(found_type_var),
            TupleArgs::WithUnpack(w) => w.search_type_vars(found_type_var),
        }
    }
}

impl SearchTypeVars for WithUnpack {
    fn search_type_vars<C: FnMut(TypeVarLikeUsage) + ?Sized>(&self, found_type_var: &mut C) {
        for t in self.before.iter() {
            t.search_type_vars(found_type_var)
        }
        match &self.unpack {
            TupleUnpack::TypeVarTuple(tvt) => {
                found_type_var(TypeVarLikeUsage::TypeVarTuple(tvt.clone()))
            }
            TupleUnpack::ArbitraryLen(t) => t.search_type_vars(found_type_var),
        }
        for t in self.after.iter() {
            t.search_type_vars(found_type_var)
        }
    }
}

impl SearchTypeVars for CallableParams {
    fn search_type_vars<C: FnMut(TypeVarLikeUsage) + ?Sized>(&self, found_type_var: &mut C) {
        match self {
            Self::Simple(params) => {
                for param in params.iter() {
                    match &param.type_ {
                        ParamType::PositionalOnly(t)
                        | ParamType::PositionalOrKeyword(t)
                        | ParamType::KeywordOnly(t)
                        | ParamType::Star(StarParamType::ArbitraryLen(t))
                        | ParamType::StarStar(StarStarParamType::ValueType(t)) => {
                            t.search_type_vars(found_type_var)
                        }
                        ParamType::Star(StarParamType::UnpackedTuple(u)) => {
                            u.args.search_type_vars(found_type_var)
                        }
                        ParamType::Star(StarParamType::ParamSpecArgs(u)) => {
                            found_type_var(TypeVarLikeUsage::ParamSpec(u.clone()))
                        }
                        ParamType::StarStar(StarStarParamType::UnpackTypedDict(t)) => {
                            t.search_type_vars(found_type_var)
                        }
                        ParamType::StarStar(StarStarParamType::ParamSpecKwargs(_)) => {
                            // Do nothing here, because we already found it above.
                        }
                    }
                }
            }
            Self::Any(_) => (),
        }
    }
}

impl SearchTypeVars for CallableContent {
    fn search_type_vars<C: FnMut(TypeVarLikeUsage) + ?Sized>(&self, found_type_var: &mut C) {
        self.params.search_type_vars(found_type_var);
        self.return_type.search_type_vars(found_type_var);
        if let Some(guard) = self.guard.as_ref() {
            guard.type_.search_type_vars(found_type_var)
        }
    }
}

impl SearchTypeVars for TypedDict {
    fn search_type_vars<C: FnMut(TypeVarLikeUsage) + ?Sized>(&self, found_type_var: &mut C) {
        if let TypedDictGenerics::Generics(list) = &self.generics {
            list.search_type_vars(found_type_var)
        }
    }
}
