use std::{borrow::Cow, ops::AddAssign, rc::Rc};

use super::{
    replace::ReplaceTypeVarLike, AnyCause, CallableParams, GenericItem, GenericsList, ReplaceSelf,
    TupleArgs, TupleUnpack, Type, TypeArgs, WithUnpack,
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
pub struct CallableWithParent {
    pub defined_at: PointLink,
    pub parent_callable: Option<PointLink>,
}

struct CallableAncestors<'a> {
    callables: &'a [CallableWithParent],
    next: Option<PointLink>,
}

impl Iterator for CallableAncestors<'_> {
    type Item = PointLink;

    fn next(&mut self) -> Option<Self::Item> {
        // This algorithm seems a bit weird in terms of Big O, but it shouldn't matter at all,
        // because this will have at most 3-5 callables (more typical is 0-1).
        if let Some(next) = self.next {
            let result = next;
            for callable_with_parent in self.callables {
                if callable_with_parent.defined_at == next {
                    self.next = callable_with_parent.parent_callable;
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
pub struct UnresolvedTypeVarLike {
    pub type_var_like: TypeVarLike,
    pub most_outer_callable: Option<PointLink>,
}

#[derive(Default, Debug)]
pub struct TypeVarManager {
    pub type_vars: Vec<UnresolvedTypeVarLike>,
    callables: Vec<CallableWithParent>,
}

impl TypeVarManager {
    pub fn position(&self, type_var: &TypeVarLike) -> Option<usize> {
        self.type_vars
            .iter()
            .position(|t| &t.type_var_like == type_var)
    }

    pub fn add(
        &mut self,
        type_var_like: TypeVarLike,
        in_callable: Option<PointLink>,
    ) -> TypeVarIndex {
        if let Some(index) = self.position(&type_var_like) {
            self.type_vars[index].most_outer_callable = self.calculate_most_outer_callable(
                self.type_vars[index].most_outer_callable,
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

    pub fn register_callable(&mut self, c: CallableWithParent) {
        self.callables.push(c)
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

    pub fn iter(&self) -> impl Iterator<Item = &UnresolvedTypeVarLike> {
        self.type_vars.iter()
    }
    pub fn len(&self) -> usize {
        self.type_vars.len()
    }

    fn calculate_most_outer_callable(
        &self,
        first: Option<PointLink>,
        second: Option<PointLink>,
    ) -> Option<PointLink> {
        for ancestor1 in (CallableAncestors {
            callables: &self.callables,
            next: first,
        }) {
            for ancestor2 in (CallableAncestors {
                callables: &self.callables,
                next: second,
            }) {
                if ancestor1 == ancestor2 {
                    return Some(ancestor1);
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
        let mut in_definition = None;
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
                if in_def == t.most_outer_callable {
                    index += 1;
                }
            } else if matched {
                in_definition = Some(t.most_outer_callable);
                index = 0;
            }
        }
        in_definition.map(|d| (index.into(), d))
    }

    pub fn remap_type_var(&self, usage: &TypeVarUsage) -> TypeVarUsage {
        if let Some((index, in_definition)) =
            self.remap_internal(&TypeVarLikeUsage::TypeVar(Cow::Borrowed(usage)))
        {
            TypeVarUsage {
                type_var: usage.type_var.clone(),
                in_definition: in_definition.unwrap_or(usage.in_definition),
                index,
            }
        } else {
            usage.clone()
        }
    }

    pub fn remap_type_var_tuple(&self, usage: &TypeVarTupleUsage) -> TypeVarTupleUsage {
        if let Some((index, in_definition)) =
            self.remap_internal(&TypeVarLikeUsage::TypeVarTuple(Cow::Borrowed(usage)))
        {
            TypeVarTupleUsage {
                type_var_tuple: usage.type_var_tuple.clone(),
                in_definition: in_definition.unwrap_or(usage.in_definition),
                index,
            }
        } else {
            usage.clone()
        }
    }

    pub fn remap_param_spec(&self, usage: &ParamSpecUsage) -> ParamSpecUsage {
        if let Some((index, in_definition)) =
            self.remap_internal(&TypeVarLikeUsage::ParamSpec(Cow::Borrowed(usage)))
        {
            ParamSpecUsage {
                param_spec: usage.param_spec.clone(),
                in_definition: in_definition.unwrap_or(usage.in_definition),
                index,
            }
        } else {
            usage.clone()
        }
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
    ) -> Option<TypeVarLikeUsage<'static>> {
        self.0
            .iter()
            .position(|t| t == &type_var_like)
            .map(|index| match type_var_like {
                TypeVarLike::TypeVar(type_var) => {
                    TypeVarLikeUsage::TypeVar(Cow::Owned(TypeVarUsage {
                        type_var,
                        index: index.into(),
                        in_definition,
                    }))
                }
                TypeVarLike::TypeVarTuple(type_var_tuple) => {
                    TypeVarLikeUsage::TypeVarTuple(Cow::Owned(TypeVarTupleUsage {
                        type_var_tuple,
                        index: index.into(),
                        in_definition,
                    }))
                }
                TypeVarLike::ParamSpec(param_spec) => {
                    TypeVarLikeUsage::ParamSpec(Cow::Owned(ParamSpecUsage {
                        param_spec,
                        index: index.into(),
                        in_definition,
                    }))
                }
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
    ) -> TypeVarLikeUsage<'static> {
        match self {
            Self::TypeVar(type_var) => TypeVarLikeUsage::TypeVar(Cow::Owned(TypeVarUsage {
                type_var: type_var.clone(),
                index,
                in_definition,
            })),
            Self::TypeVarTuple(t) => {
                TypeVarLikeUsage::TypeVarTuple(Cow::Owned(TypeVarTupleUsage {
                    type_var_tuple: t.clone(),
                    index,
                    in_definition,
                }))
            }
            Self::ParamSpec(p) => TypeVarLikeUsage::ParamSpec(Cow::Owned(ParamSpecUsage {
                param_spec: p.clone(),
                index,
                in_definition,
            })),
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
    pub index: TypeVarIndex,
    pub in_definition: PointLink,
}

#[derive(Debug, PartialEq, Clone)]
pub struct TypeVarTupleUsage {
    pub type_var_tuple: Rc<TypeVarTuple>,
    pub index: TypeVarIndex,
    pub in_definition: PointLink,
}

#[derive(Debug, PartialEq, Clone)]
pub struct ParamSpecUsage {
    pub param_spec: Rc<ParamSpec>,
    pub index: TypeVarIndex,
    pub in_definition: PointLink,
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
        let mut type_vars = self.type_vars.clone().map(|t| t.type_vars.as_vec());
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
pub enum TypeVarLikeUsage<'a> {
    TypeVar(Cow<'a, TypeVarUsage>),
    TypeVarTuple(Cow<'a, TypeVarTupleUsage>),
    ParamSpec(Cow<'a, ParamSpecUsage>),
}

impl<'a> TypeVarLikeUsage<'a> {
    pub fn in_definition(&self) -> PointLink {
        match self {
            Self::TypeVar(t) => t.in_definition,
            Self::TypeVarTuple(t) => t.in_definition,
            Self::ParamSpec(p) => p.in_definition,
        }
    }

    pub fn add_to_index(&mut self, amount: i32) {
        match self {
            Self::TypeVar(t) => t.to_mut().index += amount,
            Self::TypeVarTuple(t) => t.to_mut().index += amount,
            Self::ParamSpec(p) => p.to_mut().index += amount,
        }
    }

    pub fn index(&self) -> TypeVarIndex {
        match self {
            Self::TypeVar(t) => t.index,
            Self::TypeVarTuple(t) => t.index,
            Self::ParamSpec(p) => p.index,
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
            TypeVarLikeUsage::TypeVar(usage) => {
                GenericItem::TypeArg(Type::TypeVar(usage.into_owned()))
            }
            TypeVarLikeUsage::TypeVarTuple(usage) => GenericItem::TypeArgs(TypeArgs {
                args: TupleArgs::WithUnpack(WithUnpack {
                    before: Rc::from([]),
                    unpack: TupleUnpack::TypeVarTuple(usage.into_owned()),
                    after: Rc::from([]),
                }),
            }),
            TypeVarLikeUsage::ParamSpec(usage) => GenericItem::ParamSpecArg(ParamSpecArg::new(
                CallableParams::WithParamSpec(Rc::new([]), usage.into_owned()),
                None,
            )),
        }
    }

    pub fn into_generic_item_with_new_index(self, index: TypeVarIndex) -> GenericItem {
        match self {
            TypeVarLikeUsage::TypeVar(usage) => {
                let mut usage = usage.into_owned();
                usage.index = index;
                GenericItem::TypeArg(Type::TypeVar(usage))
            }
            TypeVarLikeUsage::TypeVarTuple(usage) => {
                let mut usage = usage.into_owned();
                usage.index = index;
                todo!()
            }
            TypeVarLikeUsage::ParamSpec(usage) => {
                let mut usage = usage.into_owned();
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
                let t = t.to_mut();
                t.index = index;
                t.in_definition = in_definition;
            }
            Self::TypeVarTuple(t) => {
                let t = t.to_mut();
                t.index = index;
                t.in_definition = in_definition;
            }
            Self::ParamSpec(p) => {
                let p = p.to_mut();
                p.index = index;
                p.in_definition = in_definition;
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
