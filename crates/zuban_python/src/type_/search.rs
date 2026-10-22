use super::{
    ClassGenerics, Generic, GenericClass, GenericsList, ParamType, StarParamType,
    StarStarParamType, TupleUnpack, TypedDictGenerics,
};

use crate::{prelude::*, type_::WithUnpack, type_helpers::Generics};

pub(crate) trait SearchTypeVars {
    fn search_type_vars<C: FnMut(TypeVarLikeUsage) + ?Sized>(&self, found_type_var: &mut C);
    fn find_in_type(&self, db: &Database, check: &mut impl FnMut(&Type) -> bool) -> bool;
    fn search_type_vars_with_condition<C: FnMut(TypeVarLikeUsage) -> bool>(
        &self,
        condition: &mut C,
    ) -> bool {
        let mut result = false;
        self.search_type_vars(&mut |usage| result |= condition(usage));
        result
    }
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

    fn find_in_type(&self, db: &Database, check: &mut impl FnMut(&Type) -> bool) -> bool {
        if check(self) {
            return true;
        }
        let mut search_in_generic_class = |c: &GenericClass| {
            Generics::from_class_generics(db, ClassNodeRef::from_link(db, c.link), &c.generics)
                .iter(db)
                .any(|generic| generic.find_in_type(db, check))
        };

        match self {
            Self::Class(c) => search_in_generic_class(c),
            Self::Dataclass(d) => search_in_generic_class(&d.class),
            Self::Union(u) => u.iter().any(|t| t.find_in_type(db, check)),
            Self::FunctionOverload(o) => o.iter_functions().any(|c| c.find_in_type(db, check)),
            Self::Type(t) => t.find_in_type(db, check),
            Self::Tuple(tup) => tup.args.find_in_type(db, check),
            Self::Callable(content) => content.find_in_type(db, check),
            Self::RecursiveType(recursive) => match &recursive.generics {
                Some(gs) => gs.iter().any(|g| g.find_in_type(db, check)),
                None => false,
            },
            Self::TypedDict(d) => d.find_in_type(db, check),
            Self::Intersection(intersection) => intersection
                .iter_entries()
                .any(|t| t.find_in_type(db, check)),
            Self::TypeForm(tf) => tf.find_in_type(db, check),
            _ => false,
        }
    }
}

impl SearchTypeVars for Generic {
    fn search_type_vars<C: FnMut(TypeVarLikeUsage) + ?Sized>(&self, found_type_var: &mut C) {
        match self {
            Self::TypeArg(t) => t.search_type_vars(found_type_var),
            Self::TypeArgs(ts) => ts.args.search_type_vars(found_type_var),
            Self::ParamSpecArg(p) => p.params.search_type_vars(found_type_var),
        }
    }

    fn find_in_type(&self, db: &Database, check: &mut impl FnMut(&Type) -> bool) -> bool {
        match self {
            Self::TypeArg(t) => t.find_in_type(db, check),
            Self::TypeArgs(ts) => ts.args.find_in_type(db, check),
            Self::ParamSpecArg(a) => a.params.find_in_type(db, check),
        }
    }
}

impl SearchTypeVars for GenericsList {
    fn search_type_vars<C: FnMut(TypeVarLikeUsage) + ?Sized>(&self, found_type_var: &mut C) {
        for g in self.iter() {
            g.search_type_vars(found_type_var);
        }
    }

    fn find_in_type(&self, db: &Database, check: &mut impl FnMut(&Type) -> bool) -> bool {
        self.iter().any(|g| g.find_in_type(db, check))
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

    fn find_in_type(&self, db: &Database, check: &mut impl FnMut(&Type) -> bool) -> bool {
        match self {
            TupleArgs::FixedLen(ts) => ts.iter().any(|t| t.find_in_type(db, check)),
            TupleArgs::ArbitraryLen(t) => t.find_in_type(db, check),
            TupleArgs::WithUnpack(with_unpack) => with_unpack.find_in_type(db, check),
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

    fn find_in_type(&self, db: &Database, check: &mut impl FnMut(&Type) -> bool) -> bool {
        self.before.iter().any(|t| t.find_in_type(db, check))
            || match &self.unpack {
                TupleUnpack::TypeVarTuple(_) => false,
                TupleUnpack::ArbitraryLen(t) => t.find_in_type(db, check),
            }
            || self.after.iter().any(|t| t.find_in_type(db, check))
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

    fn find_in_type(&self, db: &Database, check: &mut impl FnMut(&Type) -> bool) -> bool {
        match self {
            Self::Simple(params) => params.iter().any(|param| match &param.type_ {
                ParamType::PositionalOnly(t)
                | ParamType::PositionalOrKeyword(t)
                | ParamType::KeywordOnly(t)
                | ParamType::Star(StarParamType::ArbitraryLen(t))
                | ParamType::StarStar(StarStarParamType::ValueType(t)) => t.find_in_type(db, check),
                ParamType::Star(StarParamType::UnpackedTuple(t)) => {
                    Type::Tuple(t.clone()).find_in_type(db, check)
                }
                ParamType::Star(StarParamType::ParamSpecArgs(_))
                | ParamType::StarStar(StarStarParamType::ParamSpecKwargs(_)) => false,
                ParamType::StarStar(StarStarParamType::UnpackTypedDict(t)) => {
                    Type::TypedDict(t.clone()).find_in_type(db, check)
                }
            }),
            Self::Any(_) => false,
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

    fn find_in_type(&self, db: &Database, check: &mut impl FnMut(&Type) -> bool) -> bool {
        self.guard
            .as_ref()
            .is_some_and(|guard| guard.type_.find_in_type(db, check))
            || self.return_type.find_in_type(db, check)
            || self.params.find_in_type(db, check)
    }
}

impl SearchTypeVars for TypedDict {
    fn search_type_vars<C: FnMut(TypeVarLikeUsage) + ?Sized>(&self, found_type_var: &mut C) {
        if let TypedDictGenerics::Generics(list) = &self.generics {
            list.search_type_vars(found_type_var)
        }
    }

    fn find_in_type(&self, db: &Database, check: &mut impl FnMut(&Type) -> bool) -> bool {
        (match &self.generics {
            TypedDictGenerics::Generics(gs) => gs.iter().any(|g| g.find_in_type(db, check)),
            TypedDictGenerics::None | TypedDictGenerics::NotDefinedYet(_) => false,
        }) || {
            let Ok(members) = self.members_if_ready(db) else {
                return false;
            };
            if let Some(extra) = &members.extra_items
                && extra.t.find_in_type(db, check)
            {
                return true;
            }
            members
                .named
                .iter()
                .any(|t| t.type_.find_in_type(db, check))
        }
    }
}
