use std::{
    borrow::Cow,
    hash::{Hash, Hasher},
    ops::AddAssign,
    sync::{Arc, Mutex, OnceLock},
};

use parsa_python_cst::{FunctionDef, NodeIndex, ParamKind};

use super::{
    AnyCause, CallableContent, CallableParams, FormatStyle, GenericItem, GenericsList,
    ReplaceTypeVarLikes, TupleArgs, TupleUnpack, Type, TypeArgs, WithUnpack,
};
use crate::{
    database::{ComplexPoint, Database, ParentScope, PointLink},
    debug,
    diagnostics::IssueKind,
    file::{PythonFile, TypeVarTupleDefaultOrigin},
    format_data::{FormatData, ParamsStyle},
    inference_state::InferenceState,
    matching::Matcher,
    node_ref::NodeRef,
    type_helpers::Class,
    utils::join_with_commas,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Hash)]
pub(crate) struct TypeVarIndex(pub(super) u32);

impl TypeVarIndex {
    pub fn as_usize(&self) -> usize {
        self.0 as usize
    }
}

impl AddAssign<i32> for TypeVarIndex {
    fn add_assign(&mut self, other: i32) {
        self.0 = (self.0 as i32 + other) as u32;
    }
}

impl From<usize> for TypeVarIndex {
    fn from(item: usize) -> Self {
        Self(item as u32)
    }
}

#[derive(Debug)]
pub(crate) struct CallableWithParent<T> {
    pub defined_at: T,
    pub parent_callable: Option<T>,
}

struct CallableAncestors<'a, T> {
    callables: &'a [CallableWithParent<T>],
    next: Option<&'a T>,
}

impl<'a, T: CallableId> Iterator for CallableAncestors<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        // This algorithm seems a bit weird in terms of Big O, but it shouldn't matter at all,
        // because this will have at most 3-5 callables (more typical is 0-1).
        if let Some(next) = self.next {
            let result = next;
            for callable_with_parent in self.callables {
                if callable_with_parent.defined_at.is_same(next) {
                    self.next = callable_with_parent.parent_callable.as_ref();
                    return Some(result);
                }
            }
            self.next = None;
            Some(result)
        } else {
            None
        }
    }
}

#[derive(Debug)]
struct UnresolvedTypeVarLike<T> {
    pub type_var_like: TypeVarLike,
    pub most_outer_callable: Option<T>,
    pub defined_at: Option<NodeIndex>,
}

#[derive(Debug)]
pub(crate) struct TypeVarManager<T> {
    type_vars: Vec<UnresolvedTypeVarLike<T>>,
    callables: Vec<CallableWithParent<T>>,
}

impl<T: CallableId> TypeVarManager<T> {
    pub fn position(&self, type_var: &TypeVarLike) -> Option<usize> {
        self.type_vars
            .iter()
            .position(|t| &t.type_var_like == type_var)
    }

    pub fn add(
        &mut self,
        type_var_like: TypeVarLike,
        in_callable: Option<T>,
        defined_at: Option<NodeIndex>,
    ) -> TypeVarIndex {
        if let Some(index) = self.position(&type_var_like) {
            self.type_vars[index].most_outer_callable = self.calculate_most_outer_callable(
                self.type_vars[index].most_outer_callable.as_ref(),
                in_callable,
            );
            index.into()
        } else {
            self.type_vars.push(UnresolvedTypeVarLike {
                type_var_like,
                most_outer_callable: in_callable,
                defined_at,
            });
            (self.type_vars.len() - 1).into()
        }
    }

    pub fn register_callable(&mut self, c: CallableWithParent<T>) {
        self.callables.push(c)
    }

    pub fn is_callable_known(&self, callable: &Arc<CallableContent>) -> bool {
        self.callables
            .iter()
            .any(|c| c.defined_at.matches_callable(callable))
    }

    pub fn move_index(&mut self, old_index: TypeVarIndex, force_index: TypeVarIndex) {
        let removed = self.type_vars.remove(old_index.as_usize());
        self.type_vars.insert(force_index.as_usize(), removed);
    }

    pub fn has_late_bound_type_vars(&self) -> bool {
        self.type_vars
            .iter()
            .any(|t| t.most_outer_callable.is_some())
    }

    pub fn first_type_var_tuple(&self) -> Option<&Arc<TypeVarTuple>> {
        self.type_vars.iter().find_map(|t| match &t.type_var_like {
            TypeVarLike::TypeVarTuple(tvt) => Some(tvt),
            _ => None,
        })
    }

    pub fn into_type_vars(self) -> TypeVarLikes {
        TypeVarLikes(
            self.type_vars
                .into_iter()
                .filter_map(|t| t.most_outer_callable.is_none().then_some(t.type_var_like))
                .collect(),
        )
    }
    pub fn iter(&self) -> impl DoubleEndedIterator<Item = &TypeVarLike> + Clone {
        self.type_vars.iter().map(|u| &u.type_var_like)
    }

    pub fn type_vars_for_callable(&self, callable: &Arc<CallableContent>) -> TypeVarLikes {
        TypeVarLikes::new(
            self.type_vars
                .iter()
                .filter(|&t| {
                    t.most_outer_callable
                        .as_ref()
                        .is_some_and(|m| m.matches_callable(callable))
                })
                .map(|t| t.type_var_like.clone())
                .collect(),
        )
    }

    pub fn len(&self) -> usize {
        self.type_vars.len()
    }

    fn calculate_most_outer_callable(&self, first: Option<&T>, second: Option<T>) -> Option<T> {
        for ancestor1 in (CallableAncestors {
            callables: &self.callables,
            next: first,
        }) {
            for ancestor2 in (CallableAncestors {
                callables: &self.callables,
                next: second.as_ref(),
            }) {
                if ancestor1.is_same(ancestor2) {
                    return Some(ancestor1.clone());
                }
            }
        }
        None
    }

    fn remap_internal(
        &self,
        usage: &TypeVarLikeUsage,
    ) -> Option<(TypeVarIndex, Option<PointLink>)> {
        let mut index = 0;
        let mut in_definition: Option<Option<&T>> = None;
        for t in self.type_vars.iter().rev() {
            let matched = match &t.type_var_like {
                TypeVarLike::TypeVar(type_var) => match usage {
                    TypeVarLikeUsage::TypeVar(u) => type_var.as_ref() == u.type_var.as_ref(),
                    _ => false,
                },
                TypeVarLike::TypeVarTuple(t) => match usage {
                    TypeVarLikeUsage::TypeVarTuple(u) => t.as_ref() == u.type_var_tuple.as_ref(),
                    _ => false,
                },
                TypeVarLike::ParamSpec(p) => match usage {
                    TypeVarLikeUsage::ParamSpec(u) => p.as_ref() == u.param_spec.as_ref(),
                    _ => false,
                },
            };
            if let Some(in_def) = in_definition {
                if in_def.is_none() && t.most_outer_callable.is_none()
                    || in_def
                        .zip(t.most_outer_callable.as_ref())
                        .is_some_and(|(in_def, m)| in_def.is_same(m))
                {
                    index += 1;
                }
            } else if matched {
                in_definition = Some(t.most_outer_callable.as_ref());
                index = 0;
            }
        }
        in_definition.map(|d| (index.into(), d.map(|d| d.as_in_definition())))
    }

    pub fn remap_type_var(&self, usage: &TypeVarUsage) -> TypeVarUsage {
        if let Some((index, in_definition)) =
            self.remap_internal(&TypeVarLikeUsage::TypeVar(usage.clone()))
        {
            TypeVarUsage::new(
                usage.type_var.clone(),
                in_definition.unwrap_or(usage.in_definition),
                index,
            )
        } else {
            usage.clone()
        }
    }

    pub fn remap_type_var_tuple(&self, usage: &TypeVarTupleUsage) -> TypeVarTupleUsage {
        if let Some((index, in_definition)) =
            self.remap_internal(&TypeVarLikeUsage::TypeVarTuple(usage.clone()))
        {
            TypeVarTupleUsage::new(
                usage.type_var_tuple.clone(),
                in_definition.unwrap_or(usage.in_definition),
                index,
            )
        } else {
            usage.clone()
        }
    }

    pub fn remap_param_spec(&self, usage: &ParamSpecUsage) -> ParamSpecUsage {
        if let Some((index, in_definition)) =
            self.remap_internal(&TypeVarLikeUsage::ParamSpec(usage.clone()))
        {
            ParamSpecUsage::new(
                usage.param_spec.clone(),
                in_definition.unwrap_or(usage.in_definition),
                index,
            )
        } else {
            usage.clone()
        }
    }
}

impl TypeVarManager<PointLink> {
    pub fn into_type_vars_after_checking_type_var_tuples(
        mut self,
        db: &Database,
        in_file: &PythonFile,
    ) -> TypeVarLikes {
        let mut prev: Option<&mut UnresolvedTypeVarLike<PointLink>> = None;
        let mut has_default = false;
        for unfinished in self.type_vars.iter_mut() {
            let current_default = unfinished.type_var_like.has_default();
            if !current_default && has_default {
                unfinished.type_var_like = unfinished.type_var_like.set_any_default();
                NodeRef::new(in_file, unfinished.defined_at.unwrap()).add_type_issue(
                    db,
                    IssueKind::TypeVarDefaultWrongOrder {
                        type_var1: unfinished.type_var_like.name(db).into(),
                        type_var2: prev.unwrap().type_var_like.name(db).into(),
                    },
                );
                break;
            } else {
                has_default |= current_default
            }
            prev = Some(unfinished)
        }
        if has_default {
            for index in 0..self.type_vars.len() {
                let unfinished = &self.type_vars[index];
                let current = &unfinished.type_var_like;
                if current.default(db).is_some() {
                    if let Some(new) = current.replace_type_var_like_defaults_that_are_out_of_scope(
                        db,
                        self.iter().take(index),
                        &|kind| {
                            NodeRef::new(in_file, unfinished.defined_at.unwrap())
                                .add_type_issue(db, kind)
                        },
                    ) {
                        self.type_vars[index].type_var_like = new;
                    }
                }
            }
        }
        self.into_type_vars()
    }
}

impl Default for TypeVarManager<PointLink> {
    fn default() -> Self {
        Self {
            type_vars: vec![],
            callables: vec![],
        }
    }
}

impl Default for TypeVarManager<Arc<CallableContent>> {
    fn default() -> Self {
        Self {
            type_vars: vec![],
            callables: vec![],
        }
    }
}

pub trait CallableId: Clone {
    fn is_same(&self, other: &Self) -> bool;
    fn as_in_definition(&self) -> PointLink;
    fn matches_callable(&self, callable: &Arc<CallableContent>) -> bool;
}

impl CallableId for PointLink {
    fn is_same(&self, other: &Self) -> bool {
        self == other
    }

    fn as_in_definition(&self) -> PointLink {
        *self
    }

    fn matches_callable(&self, callable: &Arc<CallableContent>) -> bool {
        *self == callable.defined_at
    }
}

impl CallableId for Arc<CallableContent> {
    fn is_same(&self, other: &Self) -> bool {
        Arc::ptr_eq(self, other)
    }

    fn as_in_definition(&self) -> PointLink {
        self.defined_at
    }

    fn matches_callable(&self, callable: &Self) -> bool {
        self.is_same(callable)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Ord, PartialOrd)]
#[repr(u32)]
pub(crate) enum Variance {
    Invariant = 0,
    Covariant,
    Contravariant,
}

impl Variance {
    pub fn name(self) -> &'static str {
        match self {
            Self::Invariant => "Invariant",
            Self::Covariant => "Covariant",
            Self::Contravariant => "Contravariant",
        }
    }

    pub fn invert(self) -> Self {
        match self {
            Variance::Covariant => Variance::Contravariant,
            Variance::Contravariant => Variance::Covariant,
            Variance::Invariant => Variance::Invariant,
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub(crate) enum TypeVarVariance {
    Known(Variance),
    Inferred,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct TypeVarLikes(Arc<[TypeVarLike]>);

impl TypeVarLikes {
    pub fn new(arc: Arc<[TypeVarLike]>) -> Self {
        Self(arc)
    }

    pub fn from_vec(vec: Vec<TypeVarLike>) -> Self {
        Self(Arc::from(vec))
    }

    pub fn new_untyped_params(func: FunctionDef, skip_first: bool) -> Self {
        Self::new(
            func.params()
                .iter()
                .enumerate()
                .skip(skip_first as usize)
                .filter_map(|(i, param)| {
                    if param.kind() == ParamKind::StarStar {
                        return None;
                    }
                    Some(TypeVarLike::TypeVar(Arc::new(TypeVar::for_untyped_param(
                        i,
                    ))))
                })
                .collect(),
        )
    }

    pub fn as_vec(&self) -> Vec<TypeVarLike> {
        Vec::from(self.0.as_ref())
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn len_of_typed(&self) -> usize {
        if self.has_from_untyped_params() {
            return 0;
        }
        self.len()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn is_empty_or_untyped(&self) -> bool {
        self.0.is_empty() || self.has_from_untyped_params()
    }

    pub fn contains_non_default(&self) -> bool {
        self.iter().any(|tv| !tv.has_default())
    }

    pub fn has_constraints(&self, db: &Database) -> bool {
        self.iter().any(|tv| {
            matches!(tv, TypeVarLike::TypeVar(tv)
                          if matches!(&tv.kind(db), TypeVarKind::Constraints(_)))
        })
    }

    pub fn find(
        &self,
        type_var_like: &TypeVarLike,
        in_definition: PointLink,
    ) -> Option<TypeVarLikeUsage> {
        self.0
            .iter()
            .enumerate()
            .find(|(_, t)| *t == type_var_like)
            // We have to use the found TypeVarLike and not the one given, because the type vars
            // might have been changed (e.g. an invalid default might have changed from the
            // original definition)
            .map(|(index, tvl)| match tvl {
                TypeVarLike::TypeVar(type_var) => TypeVarLikeUsage::TypeVar(TypeVarUsage::new(
                    type_var.clone(),
                    in_definition,
                    index.into(),
                )),
                TypeVarLike::TypeVarTuple(tvt) => TypeVarLikeUsage::TypeVarTuple(
                    TypeVarTupleUsage::new(tvt.clone(), in_definition, index.into()),
                ),
                TypeVarLike::ParamSpec(p) => TypeVarLikeUsage::ParamSpec(ParamSpecUsage::new(
                    p.clone(),
                    in_definition,
                    index.into(),
                )),
            })
    }

    pub fn as_any_generic_list(&self) -> GenericsList {
        GenericsList::new_generics(self.iter().map(|tv| tv.as_any_generic_item()).collect())
    }

    pub fn as_self_generic_list(&self, defined_at: PointLink) -> GenericsList {
        GenericsList::new_generics(
            self.iter()
                .enumerate()
                .map(|(i, tv)| {
                    tv.as_type_var_like_usage(i.into(), defined_at)
                        .into_generic_item()
                })
                .collect(),
        )
    }

    pub fn as_default_or_any_generic_list(&self, db: &Database) -> GenericsList {
        GenericsList::new_generics(
            self.iter()
                .map(|tv| tv.as_default_or_any_generic_item(db))
                .collect(),
        )
    }

    pub fn iter(&self) -> std::slice::Iter<'_, TypeVarLike> {
        self.0.iter()
    }

    pub fn find_untyped_param_type_var(
        &self,
        in_definition: PointLink,
        param_index: usize,
    ) -> Option<TypeVarUsage> {
        for (index, x) in self.iter().enumerate() {
            if let TypeVarLike::TypeVar(tv) = x
                && let TypeVarName::UntypedParam { nth } = &tv.name
                && *nth == param_index
            {
                return Some(TypeVarUsage::new(tv.clone(), in_definition, index.into()));
            }
        }
        None
    }

    pub fn has_from_untyped_params(&self) -> bool {
        self.0.last().is_some_and(|tvl| match tvl {
            TypeVarLike::TypeVar(tv) => tv.is_untyped(),
            _ => false,
        })
    }

    pub fn format(&self, format_data: &FormatData) -> String {
        debug_assert!(!self.is_empty());
        format!(
            "[{}] ",
            join_with_commas(self.iter().map(|t| match t {
                TypeVarLike::TypeVar(t) => t.format(format_data),
                TypeVarLike::TypeVarTuple(tvt) => tvt.format(format_data),
                TypeVarLike::ParamSpec(s) => s.format(format_data),
            }))
        )
    }

    pub fn debug_info(&self, db: &Database) -> String {
        format!(
            "[{}]",
            join_with_commas(self.iter().map(|t| match t {
                TypeVarLike::TypeVar(t) => t.qualified_name(db).into_string(),
                TypeVarLike::TypeVarTuple(tvt) => tvt.name(db).to_string(),
                TypeVarLike::ParamSpec(s) => s.name(db).to_string(),
            }))
        )
    }

    pub fn load_saved_type_vars<'a>(db: &'a Database, node_ref: NodeRef<'a>) -> &'a TypeVarLikes {
        debug_assert!(node_ref.point().calculated());
        match node_ref.maybe_complex() {
            Some(ComplexPoint::TypeVarLikes(type_vars)) => type_vars,
            None => &db.python_state.empty_type_var_likes,
            _ => unreachable!(),
        }
    }

    pub fn add_error_if_default_after_type_var_tuple(&self, add_issue: impl FnOnce(IssueKind)) {
        let mut defaults_allowed = true;
        for tvl in self.iter() {
            match tvl {
                TypeVarLike::TypeVar(_) => {
                    if !defaults_allowed && tvl.has_default() {
                        add_issue(IssueKind::TypeVarDefaultsAmbiguousAfterTypeVarTuple);
                        break;
                    }
                }
                TypeVarLike::TypeVarTuple(_) => defaults_allowed = false,
                // TypeVars with defaults are allowed after ParamSpec again, because it clearly
                // separates the two.
                TypeVarLike::ParamSpec(_) => defaults_allowed = true,
            }
        }
    }
}

impl std::ops::Index<usize> for TypeVarLikes {
    type Output = TypeVarLike;

    fn index(&self, index: usize) -> &TypeVarLike {
        &self.0[index]
    }
}

#[derive(Debug, Clone, Eq, PartialOrd, Ord, PartialEq)]
pub(crate) enum TypeVarLike {
    TypeVar(Arc<TypeVar>),
    TypeVarTuple(Arc<TypeVarTuple>),
    ParamSpec(Arc<ParamSpec>),
}

impl TypeVarLike {
    pub fn name<'db>(&self, db: &'db Database) -> Cow<'db, str> {
        match self {
            Self::TypeVar(t) => t.name(db),
            Self::TypeVarTuple(t) => Cow::Borrowed(t.name(db)),
            Self::ParamSpec(s) => Cow::Borrowed(s.name(db)),
        }
    }

    pub fn has_default(&self) -> bool {
        match self {
            TypeVarLike::TypeVar(tv) => tv.default.is_some(),
            TypeVarLike::TypeVarTuple(tvt) => tvt.default.is_some(),
            TypeVarLike::ParamSpec(param_spec) => param_spec.default.is_some(),
        }
    }

    pub fn default(&self, db: &Database) -> Option<GenericItem> {
        match self {
            TypeVarLike::TypeVar(tv) => tv.default(db).cloned().map(GenericItem::TypeArg),
            TypeVarLike::TypeVarTuple(tvt) => tvt.default(db).cloned().map(GenericItem::TypeArgs),
            TypeVarLike::ParamSpec(p) => p
                .default(db)
                .cloned()
                .map(|default| GenericItem::ParamSpecArg(ParamSpecArg::new(default, None))),
        }
    }

    pub fn set_any_default(&self) -> Self {
        match self {
            TypeVarLike::TypeVar(tv) => {
                let mut new_tv = tv.as_ref().clone();
                new_tv.default = Some(TypeLikeInTypeVar::new_known(Type::ERROR));
                Self::TypeVar(Arc::new(new_tv))
            }
            TypeVarLike::TypeVarTuple(tvt) => {
                let mut new_tvt = tvt.as_ref().clone();
                new_tvt.default = Some(TypeLikeInTypeVar::new_known(
                    TypeArgs::new_arbitrary_from_error(),
                ));
                Self::TypeVarTuple(Arc::new(new_tvt))
            }
            TypeVarLike::ParamSpec(param_spec) => {
                let mut new_p = param_spec.as_ref().clone();
                new_p.default = Some(TypeLikeInTypeVar::new_known(CallableParams::ERROR));
                Self::ParamSpec(Arc::new(new_p))
            }
        }
    }

    fn replace_default_with_generic_item(&self, item: GenericItem) -> Self {
        match self {
            TypeVarLike::TypeVar(tv) => {
                let mut new_tv = tv.as_ref().clone();
                let GenericItem::TypeArg(t) = item else {
                    unreachable!()
                };
                new_tv.default = Some(TypeLikeInTypeVar::new_known(t));
                Self::TypeVar(Arc::new(new_tv))
            }
            TypeVarLike::TypeVarTuple(tvt) => {
                let mut new_tvt = tvt.as_ref().clone();
                let GenericItem::TypeArgs(ts) = item else {
                    unreachable!()
                };
                new_tvt.default = Some(TypeLikeInTypeVar::new_known(ts));
                Self::TypeVarTuple(Arc::new(new_tvt))
            }
            TypeVarLike::ParamSpec(param_spec) => {
                let mut new_p = param_spec.as_ref().clone();
                let GenericItem::ParamSpecArg(pa) = item else {
                    unreachable!()
                };
                new_p.default = Some(TypeLikeInTypeVar::new_known(pa.params));
                Self::ParamSpec(Arc::new(new_p))
            }
        }
    }

    pub fn as_type_var_like_usage(
        &self,
        index: TypeVarIndex,
        in_definition: PointLink,
    ) -> TypeVarLikeUsage {
        match self {
            Self::TypeVar(type_var) => {
                TypeVarLikeUsage::TypeVar(TypeVarUsage::new(type_var.clone(), in_definition, index))
            }
            Self::TypeVarTuple(t) => TypeVarLikeUsage::TypeVarTuple(TypeVarTupleUsage::new(
                t.clone(),
                in_definition,
                index,
            )),
            Self::ParamSpec(p) => {
                TypeVarLikeUsage::ParamSpec(ParamSpecUsage::new(p.clone(), in_definition, index))
            }
        }
    }

    pub fn as_any_generic_item(&self) -> GenericItem {
        match self {
            TypeVarLike::TypeVar(_) => GenericItem::TypeArg(Type::Any(AnyCause::Todo)),
            TypeVarLike::TypeVarTuple(_) => {
                GenericItem::TypeArgs(TypeArgs::new_arbitrary_length(Type::Any(AnyCause::Todo)))
            }
            TypeVarLike::ParamSpec(_) => {
                GenericItem::ParamSpecArg(ParamSpecArg::new_any(AnyCause::Todo))
            }
        }
    }

    pub fn as_default_or_any_generic_item(&self, db: &Database) -> GenericItem {
        match self {
            TypeVarLike::TypeVar(tv) => match tv.default(db) {
                Some(default) => {
                    GenericItem::TypeArg(default.clone()).resolve_recursive_defaults_or_set_any(db)
                }
                None => GenericItem::TypeArg(Type::Any(AnyCause::Todo)),
            },
            TypeVarLike::TypeVarTuple(tvt) => match tvt.default(db) {
                Some(default) => {
                    GenericItem::TypeArgs(default.clone()).resolve_recursive_defaults_or_set_any(db)
                }
                None => {
                    GenericItem::TypeArgs(TypeArgs::new_arbitrary_length(Type::Any(AnyCause::Todo)))
                }
            },
            TypeVarLike::ParamSpec(param_spec) => match param_spec.default(db) {
                Some(default) => {
                    GenericItem::ParamSpecArg(ParamSpecArg::new(default.clone(), None))
                        .resolve_recursive_defaults_or_set_any(db)
                }
                None => GenericItem::ParamSpecArg(ParamSpecArg::new_any(AnyCause::Todo)),
            },
        }
    }

    pub fn as_never_generic_item(&self, db: &Database) -> GenericItem {
        match self {
            TypeVarLike::TypeVar(tv) => match tv.default(db) {
                Some(default) => GenericItem::TypeArg(default.clone())
                    .resolve_recursive_defaults_or_set_never(db),
                // Untyped generics are not type params and should therefore simply be normal Any
                None if tv.is_untyped() => GenericItem::TypeArg(Type::ERROR),
                None => GenericItem::TypeArg(Type::Any(AnyCause::UnknownTypeParam)),
            },
            TypeVarLike::TypeVarTuple(tvt) => match tvt.default(db) {
                Some(default) => GenericItem::TypeArgs(default.clone())
                    .resolve_recursive_defaults_or_set_never(db),
                None => GenericItem::TypeArgs(TypeArgs::new_arbitrary_length(Type::Any(
                    AnyCause::UnknownTypeParam,
                ))),
            },
            TypeVarLike::ParamSpec(param_spec) => match param_spec.default(db) {
                Some(default) => {
                    GenericItem::ParamSpecArg(ParamSpecArg::new(default.clone(), None))
                        .resolve_recursive_defaults_or_set_never(db)
                }
                None => {
                    GenericItem::ParamSpecArg(ParamSpecArg::new_any(AnyCause::UnknownTypeParam))
                }
            },
        }
    }

    pub fn ensure_calculated_types(&self, db: &Database) {
        match self {
            Self::TypeVar(tv) => {
                if let TypeVarKind::Constraints(constraints) = tv.kind(db) {
                    // Consume the iterator for constraints to ensure it is calculated
                    constraints.for_each(|_| ())
                }
                tv.default(db);
            }
            Self::TypeVarTuple(tv) => {
                tv.default(db);
            }
            Self::ParamSpec(p) => {
                p.default(db);
            }
        }
    }

    pub fn replace_type_var_like_defaults_that_are_out_of_scope<'x>(
        &self,
        db: &Database,
        previous_type_vars: impl Iterator<Item = &'x TypeVarLike> + Clone,
        add_issue: impl Fn(IssueKind) -> bool,
    ) -> Option<Self> {
        if let Some(default) = self.default(db) {
            let mut had_issue = false;
            let replaced = default.replace_type_var_likes(db, &mut |usage| {
                let tvl_found = usage.as_type_var_like();
                if previous_type_vars.clone().any(|tvl| tvl == &tvl_found) {
                    None
                } else {
                    had_issue = true;
                    Some(usage.as_any_generic_item())
                }
            });
            if let Some(replaced) = replaced {
                // It is possible that something was replaced especially due to bugs, so we filter
                // and check if there was an actual issue.
                if had_issue {
                    add_issue(IssueKind::TypeVarDefaultTypeVarOutOfScope {
                        type_var: self.name(db).into(),
                    });
                    return Some(self.replace_default_with_generic_item(replaced));
                }
            }
        }
        None
    }

    pub fn is_untyped(&self) -> bool {
        match self {
            TypeVarLike::TypeVar(tv) => tv.is_untyped(),
            _ => false,
        }
    }
}

impl Hash for TypeVarLike {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            TypeVarLike::TypeVar(tv) => Arc::as_ptr(tv).hash(state),
            TypeVarLike::TypeVarTuple(tvt) => Arc::as_ptr(tvt).hash(state),
            TypeVarLike::ParamSpec(p) => Arc::as_ptr(p).hash(state),
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum TypeVarLikeName {
    InString {
        name_node: PointLink,
        string_node: PointLink,
    },
    SyntaxNode(PointLink),
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum TypeVarName {
    Name(TypeVarLikeName),
    UntypedParam { nth: usize },
    Self_,
}

impl TypeVarLikeName {
    fn file(self, db: &Database) -> &PythonFile {
        match self {
            Self::InString {
                string_node: link, ..
            }
            | Self::SyntaxNode(link) => db.loaded_python_file(link.file),
        }
    }

    fn as_str(self, db: &Database) -> &str {
        match self {
            Self::InString { string_node, .. } => NodeRef::from_link(db, string_node)
                .maybe_str()
                .unwrap()
                .content(),
            Self::SyntaxNode(link) => NodeRef::from_link(db, link).as_code(),
        }
    }
}

#[derive(Debug)]
pub(crate) struct TypeLikeInTypeVar<T> {
    node: Option<NodeIndex>,
    calculating: Mutex<bool>,
    pub t: OnceLock<T>,
}

impl<T: Clone> Clone for TypeLikeInTypeVar<T> {
    fn clone(&self) -> Self {
        Self {
            node: self.node,
            calculating: Mutex::new(*self.calculating.lock().unwrap()),
            t: self.t.clone(),
        }
    }
}

impl<T> TypeLikeInTypeVar<T> {
    pub fn new_lazy(node: NodeIndex) -> Self {
        Self {
            node: Some(node),
            calculating: Mutex::new(false),
            t: OnceLock::new(),
        }
    }

    pub fn new_known(t: T) -> Self {
        Self {
            node: None,
            calculating: Mutex::new(false),
            t: OnceLock::from(t),
        }
    }

    #[inline]
    fn get_type_like(
        &self,
        db: &Database,
        name: TypeVarLikeName,
        scope: ParentScope,
        calculate_type: impl FnOnce(&InferenceState, NodeRef) -> T,
    ) -> Result<&T, ()> {
        if *self.calculating.lock().unwrap() {
            return Err(());
        }
        Ok(self.t.get_or_init(|| {
            *self.calculating.lock().unwrap() = true;
            let node = self.node.unwrap();
            let file = name.file(db);
            let node_ref = NodeRef::new(file, node);
            InferenceState::run_with_parent_scope(db, file, scope, |i_s| {
                let t = calculate_type(&i_s, node_ref);
                *self.calculating.lock().unwrap() = false;
                t
            })
        }))
    }
}

impl TypeLikeInTypeVar<Type> {
    #[inline]
    fn get_type(
        &self,
        db: &Database,
        name: TypeVarName,
        scope: ParentScope,
        calculate_type: impl FnOnce(&InferenceState, NodeRef) -> Type,
    ) -> Result<&Type, ()> {
        let TypeVarName::Name(name) = name else {
            return Ok(self.t.get().unwrap());
        };
        self.get_type_like(db, name, scope, calculate_type)
    }
}

#[derive(Debug, Clone)]
pub(crate) enum TypeVarKindInfos {
    Unrestricted,
    Bound(TypeLikeInTypeVar<Type>),
    Constraints(Box<[TypeLikeInTypeVar<Type>]>),
}

pub(crate) enum TypeVarKind<'a, I: Iterator<Item = &'a Type> + Clone> {
    Unrestricted,
    Bound(&'a Type),
    Constraints(I),
}

#[derive(Debug, Clone)]
pub(crate) struct TypeVar {
    pub name: TypeVarName,
    scope: ParentScope,
    kind: TypeVarKindInfos,
    default: Option<TypeLikeInTypeVar<Type>>,
    pub variance: TypeVarVariance,
}

impl PartialEq for TypeVar {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name
    }
}

impl PartialOrd for TypeVar {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for TypeVar {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.name.cmp(&other.name)
    }
}

impl Eq for TypeVar {}

impl TypeVar {
    pub fn new(
        name: TypeVarLikeName,
        scope: ParentScope,
        kind: TypeVarKindInfos,
        default: Option<NodeIndex>,
        variance: TypeVarVariance,
    ) -> Self {
        Self {
            name: TypeVarName::Name(name),
            scope,
            kind,
            default: default.map(TypeLikeInTypeVar::new_lazy),
            variance,
        }
    }

    pub fn new_self(kind: TypeVarKindInfos) -> Self {
        Self {
            name: TypeVarName::Self_,
            scope: ParentScope::Module,
            kind,
            default: None,
            variance: TypeVarVariance::Known(Variance::Invariant),
        }
    }

    pub fn for_untyped_param(nth: usize) -> Self {
        Self {
            name: TypeVarName::UntypedParam { nth },
            scope: ParentScope::Module,
            kind: TypeVarKindInfos::Bound(TypeLikeInTypeVar::new_known(Type::Any(
                AnyCause::Unannotated,
            ))),
            default: None,
            variance: TypeVarVariance::Known(Variance::Invariant),
        }
    }

    pub fn inferred_variance(&self, db: &Database, class: &Class) -> Variance {
        match self.variance {
            TypeVarVariance::Known(variance) => variance,
            TypeVarVariance::Inferred => {
                let Some(class_infos) = class.maybe_cached_class_infos(db) else {
                    debug!(
                        "Using covariant variance for TypeVar {}, because of uncalculated class infos",
                        self.name(db)
                    );
                    return Variance::Covariant;
                };
                let variance = class_infos
                    .variance_map
                    .iter()
                    .find_map(|(n, variance)| (self.name == *n).then_some(variance))
                    .unwrap();
                variance.get().copied().unwrap_or_else(|| {
                    // Fallback to Covariant if it was not calculated yet. Mypy also falls back to it
                    // while calculating.
                    debug!(
                        "Using covariant variance for TypeVar {}, because the variance is not yet ready",
                        self.name(db)
                    );
                    Variance::Covariant
                })
            }
        }
    }

    pub fn name<'db>(&self, db: &'db Database) -> Cow<'db, str> {
        match &self.name {
            TypeVarName::Name(n) => Cow::Borrowed(n.as_str(db)),
            TypeVarName::Self_ => Cow::Borrowed("Self"),
            TypeVarName::UntypedParam { nth } => Cow::Owned(format!("T{}", nth + 1)),
        }
    }

    fn is_from_type_var_syntax(&self) -> bool {
        matches!(
            &self.name,
            TypeVarName::Name(TypeVarLikeName::SyntaxNode(_))
        )
    }

    pub fn is_self_name(&self) -> bool {
        matches!(self.name, TypeVarName::Self_)
    }

    pub fn kind<'a>(
        &'a self,
        db: &'a Database,
    ) -> TypeVarKind<'a, impl Iterator<Item = &'a Type> + Clone + 'a> {
        match &self.kind {
            TypeVarKindInfos::Unrestricted => TypeVarKind::Unrestricted,
            TypeVarKindInfos::Bound(bound) => TypeVarKind::Bound(
                bound
                    .get_type(db, self.name, self.scope, |i_s, node_ref| {
                        node_ref
                            .file
                            .name_resolution_for_types(i_s)
                            .compute_type_var_bound(
                                node_ref.expect_expression(),
                                self.is_from_type_var_syntax(),
                            )
                    })
                    // TODO add an error here
                    .unwrap_or(&Type::ERROR),
            ),
            TypeVarKindInfos::Constraints(constraints) => {
                TypeVarKind::Constraints(constraints.iter().map(|c| {
                    c.get_type(db, self.name, self.scope, |i_s, node_ref| {
                        node_ref
                            .file
                            .name_resolution_for_types(i_s)
                            .compute_type_var_value(
                                node_ref.expect_expression(),
                                self.is_from_type_var_syntax(),
                            )
                            .unwrap_or(Type::ERROR)
                    })
                    // TODO add an error here
                    .unwrap_or(&Type::ERROR)
                }))
            }
        }
    }

    pub fn default(&self, db: &Database) -> Option<&Type> {
        let default = self.default.as_ref()?;
        Some(
            default
                .get_type(db, self.name, self.scope, |i_s, node_ref| {
                    let default = if let Some(t) = node_ref
                        .file
                        .name_resolution_for_types(i_s)
                        .compute_type_var_default(node_ref.expect_expression())
                    {
                        t
                    } else {
                        node_ref.add_issue(i_s, IssueKind::TypeVarInvalidDefault);
                        Type::ERROR
                    };
                    match self.kind(db) {
                        TypeVarKind::Unrestricted => (),
                        TypeVarKind::Bound(bound) => {
                            if !default.is_simple_sub_type_of(i_s, bound).bool() {
                                node_ref
                                    .add_issue(i_s, IssueKind::TypeVarDefaultMustBeASubtypeOfBound);
                            }
                        }
                        TypeVarKind::Constraints(mut constraints) => {
                            if !default.unpack_type_var_constraint(i_s.db).all(|default| {
                                constraints.any(|constraint| {
                                    default
                                        .is_sub_type_of(
                                            i_s,
                                            &mut Matcher::with_ignored_promotions(),
                                            constraint,
                                        )
                                        .bool()
                                })
                            }) {
                                node_ref.add_issue(
                                    i_s,
                                    IssueKind::TypeVarDefaultMustBeASubtypeOfConstraints,
                                );
                            }
                        }
                    };
                    default
                })
                // TODO add an error here
                .unwrap_or(&Type::ERROR),
        )
    }

    pub fn is_unrestricted(&self) -> bool {
        matches!(self.kind, TypeVarKindInfos::Unrestricted)
    }

    pub fn is_untyped(&self) -> bool {
        matches!(&self.name, TypeVarName::UntypedParam { .. })
    }

    pub fn qualified_name(&self, db: &Database) -> Box<str> {
        match self.name {
            TypeVarName::Name(n) => {
                format!("{}.{}", n.file(db).qualified_name(db), self.name(db)).into()
            }

            TypeVarName::Self_ | TypeVarName::UntypedParam { .. } => self.name(db).into(),
        }
    }

    pub fn format(&self, format_data: &FormatData) -> String {
        let mut s = self.name(format_data.db).into_owned();
        match self.kind(format_data.db) {
            TypeVarKind::Unrestricted => (),
            TypeVarKind::Bound(bound) => {
                if format_data.style == FormatStyle::MypyRevealType {
                    s += " <: ";
                } else {
                    s += ": ";
                }
                s += &bound.format(format_data);
            }
            TypeVarKind::Constraints(constraints) => {
                if format_data.style == FormatStyle::MypyRevealType {
                    s += " in ";
                } else {
                    s += ": ";
                }
                s += &format!(
                    "({})",
                    join_with_commas(constraints.map(|t| t.format(format_data)))
                );
            }
        }
        if let Some(default) = self.default(format_data.db) {
            s += " = ";
            s += &default.format(format_data);
        }
        s
    }
}

impl Type {
    fn unpack_type_var_constraint<'a>(
        &'a self,
        db: &'a Database,
    ) -> impl Iterator<Item = &'a Type> {
        let result = match self {
            Type::TypeVar(tv) => match tv.type_var.kind(db) {
                TypeVarKind::Unrestricted => None,
                TypeVarKind::Bound(_) => None,
                TypeVarKind::Constraints(constraints) => Some(constraints),
            },
            _ => None,
        };
        result
            .is_none()
            .then_some(self)
            .into_iter()
            .chain(result.into_iter().flatten())
    }
}

#[derive(Debug, Clone)]
pub(crate) struct TypeVarTuple {
    name: TypeVarLikeName,
    scope: ParentScope,
    default: Option<TypeLikeInTypeVar<TypeArgs>>,
}

impl TypeVarTuple {
    pub fn new(name: TypeVarLikeName, scope: ParentScope, default: Option<NodeIndex>) -> Self {
        Self {
            name,
            scope,
            default: default.map(TypeLikeInTypeVar::new_lazy),
        }
    }

    pub fn name<'db>(&self, db: &'db Database) -> &'db str {
        self.name.as_str(db)
    }

    pub fn format(&self, format_data: &FormatData) -> String {
        if let Some(default) = self.default(format_data.db) {
            format!(
                "{} = Unpack[tuple[{}]]",
                self.name(format_data.db),
                default
                    .format(format_data)
                    .unwrap_or_else(|| "TODO format empty tuple".into())
            )
        } else {
            self.name(format_data.db).into()
        }
    }

    pub fn default<'a>(&'a self, db: &'a Database) -> Option<&'a TypeArgs> {
        Some(
            self.default
                .as_ref()?
                .get_type_like(db, self.name, self.scope, |i_s, node_ref| {
                    let origin = match node_ref.maybe_expression() {
                        Some(expr) => TypeVarTupleDefaultOrigin::OldSchool(expr),
                        None => {
                            TypeVarTupleDefaultOrigin::TypeParam(node_ref.expect_star_expression())
                        }
                    };
                    node_ref
                        .file
                        .name_resolution_for_types(i_s)
                        .compute_type_var_tuple_default(origin)
                        .unwrap_or_else(|| {
                            node_ref.add_issue(i_s, IssueKind::TypeVarTupleInvalidDefault);
                            TypeArgs::new_arbitrary_from_error()
                        })
                })
                // TODO add an error here
                .unwrap_or(&db.python_state.type_args_from_err),
        )
    }
}

impl PartialEq for TypeVarTuple {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name
    }
}

impl PartialOrd for TypeVarTuple {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for TypeVarTuple {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.name.cmp(&other.name)
    }
}

impl Eq for TypeVarTuple {}

#[derive(Debug, Clone)]
pub(crate) struct ParamSpec {
    pub name: TypeVarLikeName,
    scope: ParentScope,
    default: Option<TypeLikeInTypeVar<CallableParams>>,
}

impl ParamSpec {
    pub fn new(name: TypeVarLikeName, scope: ParentScope, default: Option<NodeIndex>) -> Self {
        Self {
            name,
            scope,
            default: default.map(TypeLikeInTypeVar::new_lazy),
        }
    }

    pub fn name<'db>(&self, db: &'db Database) -> &'db str {
        self.name.as_str(db)
    }

    fn format(&self, format_data: &FormatData) -> String {
        if let Some(default) = self.default(format_data.db) {
            format!(
                "{} = [{}]",
                self.name(format_data.db),
                default.format(format_data, ParamsStyle::Unreachable)
            )
        } else {
            self.name(format_data.db).into()
        }
    }

    pub fn has_default(&self) -> bool {
        self.default.is_some()
    }

    pub fn default(&self, db: &Database) -> Option<&CallableParams> {
        Some(
            self.default
                .as_ref()?
                .get_type_like(db, self.name, self.scope, |i_s, node_ref| {
                    node_ref
                        .file
                        .name_resolution_for_types(i_s)
                        .compute_param_spec_default(node_ref.expect_expression())
                        .unwrap_or_else(|| {
                            node_ref.add_issue(i_s, IssueKind::ParamSpecInvalidDefault);
                            CallableParams::ERROR
                        })
                })
                .unwrap_or(&CallableParams::ERROR),
        )
    }
}

impl PartialEq for ParamSpec {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name
    }
}

impl Ord for ParamSpec {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.name.cmp(&other.name)
    }
}

impl PartialOrd for ParamSpec {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Eq for ParamSpec {}

#[derive(Debug, Eq, Clone)]
pub(crate) struct TypeVarUsage {
    pub type_var: Arc<TypeVar>,
    pub in_definition: PointLink,
    pub index: TypeVarIndex,
    // This should only ever be used for type matching. This is also only used for stuff like
    // foo(foo) where the callable is used twice with type vars and polymorphic matching is needed
    // to negotiate the type vars. This is reset after type matching and should always be 0.
    pub temporary_matcher_id: u32,
}

impl TypeVarUsage {
    pub fn new(type_var: Arc<TypeVar>, in_definition: PointLink, index: TypeVarIndex) -> Self {
        Self {
            type_var,
            in_definition,
            index,
            temporary_matcher_id: 0,
        }
    }
}

impl std::cmp::PartialEq for TypeVarUsage {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.type_var, &other.type_var)
            && self.in_definition == other.in_definition
            && self.index == other.index
            && self.temporary_matcher_id == other.temporary_matcher_id
    }
}

impl Hash for TypeVarUsage {
    fn hash<H: Hasher>(&self, state: &mut H) {
        Arc::as_ptr(&self.type_var).hash(state);
        self.in_definition.hash(state);
        self.index.hash(state);
        self.temporary_matcher_id.hash(state);
    }
}

#[derive(Debug, PartialEq, Clone, Eq)]
pub(crate) struct TypeVarTupleUsage {
    pub type_var_tuple: Arc<TypeVarTuple>,
    pub in_definition: PointLink,
    pub index: TypeVarIndex,
    pub temporary_matcher_id: u32,
}

impl TypeVarTupleUsage {
    pub fn new(
        type_var_tuple: Arc<TypeVarTuple>,
        in_definition: PointLink,
        index: TypeVarIndex,
    ) -> Self {
        Self {
            type_var_tuple,
            in_definition,
            index,
            temporary_matcher_id: 0,
        }
    }
}

impl Hash for TypeVarTupleUsage {
    fn hash<H: Hasher>(&self, state: &mut H) {
        Arc::as_ptr(&self.type_var_tuple).hash(state);
        self.in_definition.hash(state);
        self.index.hash(state);
        self.temporary_matcher_id.hash(state);
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub(crate) struct ParamSpecUsage {
    pub param_spec: Arc<ParamSpec>,
    pub in_definition: PointLink,
    pub index: TypeVarIndex,
    pub temporary_matcher_id: u32,
}

impl ParamSpecUsage {
    pub fn new(param_spec: Arc<ParamSpec>, in_definition: PointLink, index: TypeVarIndex) -> Self {
        Self {
            param_spec,
            in_definition,
            index,
            temporary_matcher_id: 0,
        }
    }

    pub fn into_generic_item(self) -> GenericItem {
        GenericItem::ParamSpecArg(ParamSpecArg::new(
            CallableParams::new_param_spec(self),
            None,
        ))
    }
}

impl Hash for ParamSpecUsage {
    fn hash<H: Hasher>(&self, state: &mut H) {
        Arc::as_ptr(&self.param_spec).hash(state);
        self.in_definition.hash(state);
        self.index.hash(state);
        self.temporary_matcher_id.hash(state);
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

#[derive(Debug, PartialEq, Clone)]
pub(crate) enum TypeVarLikeUsage {
    TypeVar(TypeVarUsage),
    TypeVarTuple(TypeVarTupleUsage),
    ParamSpec(ParamSpecUsage),
}

impl TypeVarLikeUsage {
    pub fn in_definition(&self) -> PointLink {
        match self {
            Self::TypeVar(t) => t.in_definition,
            Self::TypeVarTuple(t) => t.in_definition,
            Self::ParamSpec(p) => p.in_definition,
        }
    }

    pub fn name_definition(&self) -> Option<PointLink> {
        let name = match self {
            Self::TypeVar(t) => match t.type_var.name {
                TypeVarName::Name(name) => name,
                TypeVarName::Self_ | TypeVarName::UntypedParam { .. } => return None,
            },
            Self::TypeVarTuple(t) => t.type_var_tuple.name,
            Self::ParamSpec(p) => p.param_spec.name,
        };
        match name {
            TypeVarLikeName::InString {
                string_node: link, ..
            }
            | TypeVarLikeName::SyntaxNode(link) => Some(link),
        }
    }

    pub fn add_to_index(&mut self, amount: i32) {
        match self {
            Self::TypeVar(t) => t.index += amount,
            Self::TypeVarTuple(t) => t.index += amount,
            Self::ParamSpec(p) => p.index += amount,
        }
    }

    pub fn index(&self) -> TypeVarIndex {
        match self {
            Self::TypeVar(t) => t.index,
            Self::TypeVarTuple(t) => t.index,
            Self::ParamSpec(p) => p.index,
        }
    }

    pub fn temporary_matcher_id(&self) -> u32 {
        match self {
            Self::TypeVar(t) => t.temporary_matcher_id,
            Self::TypeVarTuple(t) => t.temporary_matcher_id,
            Self::ParamSpec(p) => p.temporary_matcher_id,
        }
    }

    pub fn as_type_var_like(&self) -> TypeVarLike {
        match self {
            Self::TypeVar(t) => TypeVarLike::TypeVar(t.type_var.clone()),
            Self::TypeVarTuple(t) => TypeVarLike::TypeVarTuple(t.type_var_tuple.clone()),
            Self::ParamSpec(p) => TypeVarLike::ParamSpec(p.param_spec.clone()),
        }
    }

    pub fn as_any_generic_item(&self) -> GenericItem {
        self.as_type_var_like().as_any_generic_item()
    }

    pub fn as_default_or_any_generic_item(&self, db: &Database) -> GenericItem {
        self.as_type_var_like().as_default_or_any_generic_item(db)
    }

    pub fn into_generic_item(self) -> GenericItem {
        match self {
            TypeVarLikeUsage::TypeVar(usage) => GenericItem::TypeArg(Type::TypeVar(usage)),
            TypeVarLikeUsage::TypeVarTuple(usage) => GenericItem::TypeArgs(TypeArgs {
                args: TupleArgs::WithUnpack(WithUnpack {
                    before: Arc::from([]),
                    unpack: TupleUnpack::TypeVarTuple(usage),
                    after: Arc::from([]),
                }),
            }),
            TypeVarLikeUsage::ParamSpec(usage) => usage.into_generic_item(),
        }
    }

    pub fn into_generic_item_with_new_index(self, index: TypeVarIndex) -> GenericItem {
        match self {
            TypeVarLikeUsage::TypeVar(mut usage) => {
                usage.index = index;
                GenericItem::TypeArg(Type::TypeVar(usage))
            }
            TypeVarLikeUsage::TypeVarTuple(mut usage) => {
                usage.index = index;
                GenericItem::TypeArgs(TypeArgs {
                    args: TupleArgs::WithUnpack(WithUnpack {
                        before: Arc::from([]),
                        unpack: TupleUnpack::TypeVarTuple(usage),
                        after: Arc::from([]),
                    }),
                })
            }
            TypeVarLikeUsage::ParamSpec(mut usage) => {
                usage.index = index;
                GenericItem::ParamSpecArg(ParamSpecArg::new(
                    CallableParams::new_param_spec(usage),
                    None,
                ))
            }
        }
    }

    pub fn update_in_definition_and_index(
        &mut self,
        in_definition: PointLink,
        index: TypeVarIndex,
    ) {
        match self {
            Self::TypeVar(t) => {
                t.index = index;
                t.in_definition = in_definition;
            }
            Self::TypeVarTuple(t) => {
                t.index = index;
                t.in_definition = in_definition;
            }
            Self::ParamSpec(p) => {
                p.index = index;
                p.in_definition = in_definition;
            }
        }
    }

    pub fn update_temporary_matcher_index(&mut self, index: u32) {
        match self {
            Self::TypeVar(t) => {
                t.temporary_matcher_id = index;
            }
            Self::TypeVarTuple(t) => {
                t.temporary_matcher_id = index;
            }
            Self::ParamSpec(p) => {
                p.temporary_matcher_id = index;
            }
        }
    }

    pub fn format_without_matcher(&self, db: &Database, params_style: ParamsStyle) -> String {
        match self {
            Self::TypeVar(usage) => {
                let mut s = usage.type_var.name(db).into_owned();
                if let Some(default) = usage.type_var.default(db) {
                    s += " = ";
                    s += &default.format_short(db);
                }
                s
            }
            Self::TypeVarTuple(t) => format!(
                "Unpack[{}]",
                t.type_var_tuple.format(&FormatData::new_short(db))
            ),
            Self::ParamSpec(p) => match params_style {
                ParamsStyle::CallableParams => p.param_spec.format(&FormatData::new_short(db)),
                ParamsStyle::CallableParamsInner => format!("**{}", p.param_spec.name(db)),
                ParamsStyle::Unreachable => unreachable!(),
            },
        }
    }
}
