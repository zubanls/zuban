use std::{ops::AddAssign, rc::Rc};

use super::{
    replace::ReplaceTypeVarLike, AnyCause, CallableContent, CallableParams, GenericItem,
    GenericsList, ReplaceSelf, TupleArgs, TupleUnpack, Type, TypeArgs, WithUnpack,
};
use crate::{
    database::{Database, PointLink},
    matching::{FormatData, ParamsStyle},
    node_ref::NodeRef,
    utils::join_with_commas,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd)]
pub struct TypeVarIndex(pub(super) u32);

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
pub struct CallableWithParent<T> {
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
                if callable_with_parent.defined_at.is_same(&next) {
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
}

#[derive(Debug)]
pub struct TypeVarManager<T> {
    type_vars: Vec<UnresolvedTypeVarLike<T>>,
    callables: Vec<CallableWithParent<T>>,
}

impl<T: CallableId> TypeVarManager<T> {
    pub fn position(&self, type_var: &TypeVarLike) -> Option<usize> {
        self.type_vars
            .iter()
            .position(|t| &t.type_var_like == type_var)
    }

    pub fn add(&mut self, type_var_like: TypeVarLike, in_callable: Option<T>) -> TypeVarIndex {
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
            });
            (self.type_vars.len() - 1).into()
        }
    }

    pub fn register_callable(&mut self, c: CallableWithParent<T>) {
        self.callables.push(c)
    }

    pub fn is_callable_known(&self, callable: &Rc<CallableContent>) -> bool {
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

    pub fn has_type_vars(&self) -> bool {
        !self.type_vars.is_empty()
    }

    pub fn has_type_var_tuples(&self) -> bool {
        self.type_vars
            .iter()
            .any(|t| matches!(t.type_var_like, TypeVarLike::TypeVarTuple(_)))
    }

    pub fn into_type_vars(self) -> TypeVarLikes {
        TypeVarLikes(
            self.type_vars
                .into_iter()
                .filter_map(|t| t.most_outer_callable.is_none().then_some(t.type_var_like))
                .collect(),
        )
    }

    pub fn iter(&self) -> impl Iterator<Item = &TypeVarLike> {
        self.type_vars.iter().map(|u| &u.type_var_like)
    }

    pub fn type_vars_for_callable(&self, callable: &Rc<CallableContent>) -> TypeVarLikes {
        TypeVarLikes::new(
            self.type_vars
                .iter()
                .filter_map(|t| {
                    (t.most_outer_callable
                        .as_ref()
                        .is_some_and(|m| m.matches_callable(callable)))
                    .then(|| t.type_var_like.clone())
                })
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
                if ancestor1.is_same(&ancestor2) {
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
                        .is_some_and(|(in_def, m)| in_def.is_same(&m))
                {
                    index += 1;
                }
            } else if matched {
                in_definition = Some(t.most_outer_callable.as_ref());
                index = 0;
            }
        }
        in_definition.map(|d| (index.into(), d.clone().map(|d| d.as_in_definition())))
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

impl Default for TypeVarManager<PointLink> {
    fn default() -> Self {
        Self {
            type_vars: vec![],
            callables: vec![],
        }
    }
}

impl Default for TypeVarManager<Rc<CallableContent>> {
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
    fn matches_callable(&self, callable: &Rc<CallableContent>) -> bool;
}

impl CallableId for PointLink {
    fn is_same(&self, other: &Self) -> bool {
        self == other
    }

    fn as_in_definition(&self) -> PointLink {
        *self
    }

    fn matches_callable(&self, callable: &Rc<CallableContent>) -> bool {
        *self == callable.defined_at
    }
}

impl CallableId for Rc<CallableContent> {
    fn is_same(&self, other: &Self) -> bool {
        Rc::ptr_eq(self, other)
    }

    fn as_in_definition(&self) -> PointLink {
        self.defined_at
    }

    fn matches_callable(&self, callable: &Self) -> bool {
        self.is_same(callable)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u32)]
pub enum Variance {
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

#[derive(Debug, Clone, PartialEq)]
pub struct TypeVarLikes(Rc<[TypeVarLike]>);

impl TypeVarLikes {
    pub fn new(rc: Rc<[TypeVarLike]>) -> Self {
        Self(rc)
    }

    pub fn from_vec(vec: Vec<TypeVarLike>) -> Self {
        Self(Rc::from(vec))
    }

    pub fn as_vec(&self) -> Vec<TypeVarLike> {
        Vec::from(self.0.as_ref())
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn find(
        &self,
        type_var_like: TypeVarLike,
        in_definition: PointLink,
    ) -> Option<TypeVarLikeUsage> {
        self.0
            .iter()
            .position(|t| t == &type_var_like)
            .map(|index| match type_var_like {
                TypeVarLike::TypeVar(type_var) => TypeVarLikeUsage::TypeVar(TypeVarUsage::new(
                    type_var,
                    in_definition,
                    index.into(),
                )),
                TypeVarLike::TypeVarTuple(type_var_tuple) => TypeVarLikeUsage::TypeVarTuple(
                    TypeVarTupleUsage::new(type_var_tuple, in_definition, index.into()),
                ),
                TypeVarLike::ParamSpec(param_spec) => TypeVarLikeUsage::ParamSpec(
                    ParamSpecUsage::new(param_spec, in_definition, index.into()),
                ),
            })
    }

    pub fn as_any_generic_list(&self) -> GenericsList {
        GenericsList::new_generics(self.iter().map(|tv| tv.as_any_generic_item()).collect())
    }

    pub fn iter(&self) -> std::slice::Iter<TypeVarLike> {
        self.0.iter()
    }

    pub fn format(&self, format_data: &FormatData) -> String {
        debug_assert!(!self.is_empty());
        format!(
            "[{}] ",
            join_with_commas(self.iter().map(|t| match t {
                TypeVarLike::TypeVar(t) => {
                    let mut s = t.name(format_data.db).to_owned();
                    match &t.kind {
                        TypeVarKind::Unrestricted => (),
                        TypeVarKind::Bound(bound) => {
                            s += &format!(" <: {}", bound.format(format_data));
                        }
                        TypeVarKind::Constraints(constraints) => {
                            s += &format!(
                                " in ({})",
                                join_with_commas(
                                    constraints.iter().map(|t| t.format(format_data).into())
                                )
                            );
                        }
                    }
                    s
                }
                TypeVarLike::TypeVarTuple(tvt) => tvt.name(format_data.db).into(),
                TypeVarLike::ParamSpec(s) => s.name(format_data.db).into(),
            }))
        )
    }
}

impl std::ops::Index<usize> for TypeVarLikes {
    type Output = TypeVarLike;

    fn index(&self, index: usize) -> &TypeVarLike {
        &self.0[index]
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum TypeVarLike {
    TypeVar(Rc<TypeVar>),
    TypeVarTuple(Rc<TypeVarTuple>),
    ParamSpec(Rc<ParamSpec>),
}

impl TypeVarLike {
    pub fn name<'db>(&self, db: &'db Database) -> &'db str {
        match self {
            Self::TypeVar(t) => t.name(db),
            Self::TypeVarTuple(t) => t.name(db),
            Self::ParamSpec(s) => s.name(db),
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

    pub fn as_never_generic_item(&self) -> GenericItem {
        match self {
            TypeVarLike::TypeVar(_) => GenericItem::TypeArg(Type::Never),
            TypeVarLike::TypeVarTuple(_) => {
                GenericItem::TypeArgs(TypeArgs::new_arbitrary_length(Type::Never))
            }
            TypeVarLike::ParamSpec(_) => todo!(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeVarName {
    PointLink(PointLink),
    Self_,
}

#[derive(Debug, Clone)]
pub enum TypeVarKind {
    Unrestricted,
    Bound(Type),
    Constraints(Box<[Type]>),
}

#[derive(Debug, Clone)]
pub struct TypeVar {
    pub name_string: TypeVarName,
    pub kind: TypeVarKind,
    pub variance: Variance,
}

impl PartialEq for TypeVar {
    fn eq(&self, other: &Self) -> bool {
        self.name_string == other.name_string
    }
}

impl TypeVar {
    pub fn name<'db>(&self, db: &'db Database) -> &'db str {
        match self.name_string {
            TypeVarName::PointLink(link) => {
                NodeRef::from_link(db, link).maybe_str().unwrap().content()
            }
            TypeVarName::Self_ => "Self",
        }
    }

    pub fn qualified_name(&self, db: &Database) -> Box<str> {
        match self.name_string {
            TypeVarName::PointLink(link) => {
                let node_ref = NodeRef::from_link(db, link);
                format!(
                    "{}.{}",
                    node_ref.in_module().qualified_name(db),
                    node_ref.maybe_str().unwrap().content()
                )
                .into()
            }
            TypeVarName::Self_ => Box::from("Self"),
        }
    }
}

#[derive(Debug, Clone)]
pub struct TypeVarTuple {
    pub name_string: PointLink,
    pub default: Option<Type>,
}

impl TypeVarTuple {
    pub fn name<'db>(&self, db: &'db Database) -> &'db str {
        NodeRef::from_link(db, self.name_string)
            .maybe_str()
            .unwrap()
            .content()
    }
}

impl PartialEq for TypeVarTuple {
    fn eq(&self, other: &Self) -> bool {
        self.name_string == other.name_string
    }
}

#[derive(Debug, Clone)]
pub struct ParamSpec {
    pub name_string: PointLink,
}

impl ParamSpec {
    pub fn name<'db>(&self, db: &'db Database) -> &'db str {
        NodeRef::from_link(db, self.name_string)
            .maybe_str()
            .unwrap()
            .content()
    }
}

impl PartialEq for ParamSpec {
    fn eq(&self, other: &Self) -> bool {
        self.name_string == other.name_string
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct TypeVarUsage {
    pub type_var: Rc<TypeVar>,
    pub in_definition: PointLink,
    pub index: TypeVarIndex,
    // This should only ever be used for type matching. This is also only used for stuff like
    // foo(foo) where the callable is used twice with type vars and polymorphic matching is needed
    // to negotiate the type vars. This is reset after type matching and should always be 0.
    pub temporary_matcher_id: u32,
}

impl TypeVarUsage {
    pub fn new(type_var: Rc<TypeVar>, in_definition: PointLink, index: TypeVarIndex) -> Self {
        Self {
            type_var,
            in_definition,
            index,
            temporary_matcher_id: 0,
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct TypeVarTupleUsage {
    pub type_var_tuple: Rc<TypeVarTuple>,
    pub in_definition: PointLink,
    pub index: TypeVarIndex,
    pub temporary_matcher_id: u32,
}

impl TypeVarTupleUsage {
    pub fn new(
        type_var_tuple: Rc<TypeVarTuple>,
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

#[derive(Debug, PartialEq, Clone)]
pub struct ParamSpecUsage {
    pub param_spec: Rc<ParamSpec>,
    pub in_definition: PointLink,
    pub index: TypeVarIndex,
    pub temporary_matcher_id: u32,
}

impl ParamSpecUsage {
    pub fn new(param_spec: Rc<ParamSpec>, in_definition: PointLink, index: TypeVarIndex) -> Self {
        Self {
            param_spec,
            in_definition,
            index,
            temporary_matcher_id: 0,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct ParamSpecTypeVars {
    pub type_vars: TypeVarLikes,
    pub in_definition: PointLink,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ParamSpecArg {
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

    pub fn replace_type_var_likes_and_self(
        &self,
        db: &Database,
        callable: ReplaceTypeVarLike,
        replace_self: ReplaceSelf,
    ) -> Self {
        let mut type_vars = self.type_vars.as_ref().map(|t| t.type_vars.as_vec());
        Self::new(
            self.params
                .replace_type_var_likes_and_self(
                    db,
                    &mut type_vars,
                    self.type_vars.as_ref().map(|t| t.in_definition),
                    callable,
                    replace_self,
                )
                .0,
            type_vars.map(|t| ParamSpecTypeVars {
                type_vars: TypeVarLikes::from_vec(t),
                in_definition: self.type_vars.as_ref().unwrap().in_definition,
            }),
        )
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum TypeVarLikeUsage {
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

    pub fn into_generic_item(self) -> GenericItem {
        match self {
            TypeVarLikeUsage::TypeVar(usage) => GenericItem::TypeArg(Type::TypeVar(usage)),
            TypeVarLikeUsage::TypeVarTuple(usage) => GenericItem::TypeArgs(TypeArgs {
                args: TupleArgs::WithUnpack(WithUnpack {
                    before: Rc::from([]),
                    unpack: TupleUnpack::TypeVarTuple(usage),
                    after: Rc::from([]),
                }),
            }),
            TypeVarLikeUsage::ParamSpec(usage) => GenericItem::ParamSpecArg(ParamSpecArg::new(
                CallableParams::WithParamSpec(Rc::new([]), usage),
                None,
            )),
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
                todo!()
            }
            TypeVarLikeUsage::ParamSpec(mut usage) => {
                usage.index = index;
                GenericItem::ParamSpecArg(ParamSpecArg::new(
                    CallableParams::WithParamSpec(Rc::new([]), usage),
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

    pub fn format_without_matcher(&self, db: &Database, params_style: ParamsStyle) -> Box<str> {
        match self {
            Self::TypeVar(type_var_usage) => type_var_usage.type_var.name(db).into(),
            Self::TypeVarTuple(t) => t.type_var_tuple.name(db).into(),
            Self::ParamSpec(p) => {
                let name = p.param_spec.name(db);
                match params_style {
                    ParamsStyle::CallableParams => name.into(),
                    ParamsStyle::CallableParamsInner => format!("**{}", name).into(),
                    ParamsStyle::Unreachable => unreachable!(),
                }
            }
        }
    }
}
