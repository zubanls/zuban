use std::borrow::Cow;
use std::rc::Rc;

use parsa_python_ast::ParamKind;

use super::super::{Generic, Match, MismatchReason};
use super::bound::TypeVarBound;
use crate::database::{Database, PointLink};
use crate::inference_state::InferenceState;
use crate::matching::Param;
use crate::type_::{
    common_base_type_of_type_var_tuple_with_items, CallableParams, GenericItem, ParamSpecArgument,
    ParamSpecific, Type, TypeArguments, TypeOrTypeVarTuple, TypeVar, TypeVarKind, TypeVarLike,
    TypeVarLikeUsage, TypeVarLikes, TypeVarUsage, Variance,
};
use crate::type_helpers::{Callable, Class, Function};

#[derive(Debug, Clone, Copy)]
pub enum FunctionOrCallable<'a> {
    Function(Function<'a, 'a>),
    Callable(Callable<'a>),
}

impl<'db: 'a, 'a> FunctionOrCallable<'a> {
    pub fn result_type(&self, i_s: &InferenceState<'db, '_>) -> Cow<'a, Type> {
        match self {
            Self::Function(f) => f.result_type(i_s),
            Self::Callable(c) => Cow::Borrowed(&c.content.result_type),
        }
    }

    pub fn diagnostic_string(&self, db: &Database) -> Option<String> {
        match self {
            Self::Function(f) => Some(f.diagnostic_string()),
            Self::Callable(c) => c.diagnostic_string(db),
        }
    }

    pub fn defined_at(&self) -> PointLink {
        match self {
            Self::Function(function) => function.node_ref.as_link(),
            Self::Callable(callable) => callable.content.defined_at,
        }
    }

    pub fn type_vars(&self, i_s: &InferenceState<'db, '_>) -> &'a TypeVarLikes {
        match self {
            Self::Function(function) => function.type_vars(i_s),
            Self::Callable(c) => &c.content.type_vars,
        }
    }

    pub fn class(&self) -> Option<Class<'a>> {
        match self {
            Self::Function(function) => function.class,
            Self::Callable(c) => c.defined_in,
        }
    }

    pub fn has_keyword_param_with_name(&self, db: &Database, name: &str) -> bool {
        match self {
            Self::Function(function) => function.iter_params().any(|p| {
                p.name(db) == Some(name)
                    && matches!(
                        p.kind(db),
                        ParamKind::PositionalOrKeyword | ParamKind::KeywordOnly
                    )
            }),
            Self::Callable(c) => match &c.content.params {
                CallableParams::Simple(params) => params.iter().any(|p| {
                    p.name.is_some_and(|n| {
                        n.as_str(db) == name
                            && matches!(
                                p.param_specific,
                                ParamSpecific::PositionalOrKeyword(_)
                                    | ParamSpecific::KeywordOnly(_)
                            )
                    })
                }),
                _ => false,
            },
        }
    }
}

#[derive(Debug, Clone)]
pub enum BoundKind {
    TypeVar(TypeVarBound),
    TypeVarTuple(TypeArguments),
    ParamSpecArgument(ParamSpecArgument),
    Uncalculated { fallback: Option<Type> },
}

impl Default for BoundKind {
    fn default() -> Self {
        Self::Uncalculated { fallback: None }
    }
}

#[derive(Debug, Default, Clone)]
pub struct CalculatedTypeVarLike {
    pub(super) type_: BoundKind,
    pub(super) defined_by_result_context: bool,
}

impl CalculatedTypeVarLike {
    pub fn calculated(&self) -> bool {
        !matches!(self.type_, BoundKind::Uncalculated { .. })
    }

    pub fn merge_fixed_length_type_var_tuple<
        'x,
        I: ExactSizeIterator<Item = &'x TypeOrTypeVarTuple>,
    >(
        &mut self,
        i_s: &InferenceState,
        length: usize,
        items: I,
    ) {
        match &mut self.type_ {
            BoundKind::TypeVarTuple(ts) => {
                common_base_type_of_type_var_tuple_with_items(&mut ts.args, i_s, length, items)
            }
            _ => unreachable!(),
        }
    }

    pub fn into_generic_item(self, db: &Database, type_var_like: &TypeVarLike) -> GenericItem {
        match self.type_ {
            BoundKind::TypeVar(t) => GenericItem::TypeArgument(t.into_type(db)),
            BoundKind::TypeVarTuple(ts) => GenericItem::TypeArguments(ts),
            BoundKind::ParamSpecArgument(params) => GenericItem::ParamSpecArgument(params),
            BoundKind::Uncalculated { fallback } => {
                if let Some(fallback) = fallback {
                    GenericItem::TypeArgument(fallback)
                } else {
                    match type_var_like {
                        TypeVarLike::TypeVar(_) => GenericItem::TypeArgument(Type::Never),
                        // TODO TypeVarTuple: this feels wrong, should maybe be never?
                        TypeVarLike::TypeVarTuple(_) => {
                            GenericItem::TypeArguments(TypeArguments::new_fixed_length(Rc::new([])))
                        }
                        // TODO ParamSpec: this feels wrong, should maybe be never?
                        TypeVarLike::ParamSpec(_) => {
                            GenericItem::ParamSpecArgument(ParamSpecArgument::new_any())
                        }
                    }
                }
            }
        }
    }

    pub fn maybe_calculated_type(self, db: &Database) -> Option<Type> {
        let BoundKind::TypeVar(bound) = self.type_ else {
            return None
        };
        Some(bound.into_type(db))
    }

    pub fn update_uncalculated_with_generic_invariant(&mut self, db: &Database, g: Generic) {
        debug_assert!(matches!(self.type_, BoundKind::Uncalculated { .. }));
        self.type_ = match g {
            Generic::TypeArgument(t) => BoundKind::TypeVar(TypeVarBound::Invariant(t.into_owned())),
            Generic::TypeVarTuple(t) => todo!(),
            Generic::ParamSpecArgument(p) => todo!(),
        }
    }
}

#[derive(Debug)]
pub struct TypeVarMatcher {
    pub(super) calculated_type_vars: Vec<CalculatedTypeVarLike>,
    pub(super) match_in_definition: PointLink,
}

impl TypeVarMatcher {
    pub fn new(match_in_definition: PointLink, type_var_count: usize) -> Self {
        // We could allocate on stack as described here:
        // https://stackoverflow.com/questions/27859822/is-it-possible-to-have-stack-allocated-arrays-with-the-size-determined-at-runtim
        let mut calculated_type_vars = vec![];
        calculated_type_vars.resize_with(type_var_count, Default::default);
        Self {
            calculated_type_vars,
            match_in_definition,
        }
    }

    pub fn set_all_contained_type_vars_to_any(&mut self, i_s: &InferenceState, type_: &Type) {
        type_.search_type_vars(&mut |t| {
            if t.in_definition() == self.match_in_definition {
                let current = &mut self.calculated_type_vars[t.index().as_usize()];
                if !current.calculated() {
                    current.type_ = match t {
                        TypeVarLikeUsage::TypeVar(_) => {
                            BoundKind::TypeVar(TypeVarBound::Invariant(Type::Any))
                        }
                        TypeVarLikeUsage::TypeVarTuple(_) => {
                            BoundKind::TypeVarTuple(TypeArguments::new_arbitrary_length(Type::Any))
                        }
                        TypeVarLikeUsage::ParamSpec(_) => {
                            BoundKind::ParamSpecArgument(ParamSpecArgument::new_any())
                        }
                    }
                }
            }
        });
    }

    pub fn match_or_add_type_var(
        &mut self,
        i_s: &InferenceState,
        type_var_usage: &TypeVarUsage,
        type_var: &TypeVar,
        value_type: &Type,
        variance: Variance,
    ) -> Match {
        let current = &mut self.calculated_type_vars[type_var_usage.index.as_usize()];
        if let BoundKind::TypeVar(current_type) = &mut current.type_ {
            let m = current_type.merge_or_mismatch(i_s, value_type, variance);
            return m;
        }
        debug_assert!(!current.calculated(), "{current:?}");
        // Before setting the type var, we need to check if the constraints match.
        match check_constraints(i_s, &type_var_usage.type_var, value_type, variance) {
            Ok(bound) => {
                current.type_ = BoundKind::TypeVar(bound);
                if value_type.is_any() {
                    Match::True { with_any: true }
                } else {
                    Match::new_true()
                }
            }
            Err(m) => {
                current.type_ = BoundKind::Uncalculated {
                    fallback: Some(value_type.clone()),
                };
                m
            }
        }
    }
}

pub fn check_constraints(
    i_s: &InferenceState,
    type_var: &Rc<TypeVar>,
    value_type: &Type,
    variance: Variance,
) -> Result<TypeVarBound, Match> {
    let mut mismatch_constraints = false;
    match &type_var.kind {
        TypeVarKind::Unrestricted => (),
        TypeVarKind::Bound(bound) => {
            mismatch_constraints |= !bound.is_simple_super_type_of(i_s, value_type).bool();
        }
        TypeVarKind::Constraints(constraints) => {
            if let Type::TypeVar(t2) = value_type {
                if let TypeVarKind::Constraints(constraints2) = &t2.type_var.kind {
                    if constraints2.iter().all(|r2| {
                        constraints
                            .iter()
                            .any(|r1| r1.is_simple_super_type_of(i_s, r2).bool())
                    }) {
                        return Ok(TypeVarBound::Invariant(value_type.clone()));
                    } else {
                        mismatch_constraints = true;
                    }
                }
            }
            if !mismatch_constraints {
                let mut matched_constraint = None;
                for constraint in constraints.iter() {
                    let m = constraint.simple_matches(i_s, value_type, variance);
                    if m.bool() {
                        if matched_constraint.is_some() {
                            // This means that any is involved and multiple constraints
                            // are matching. Therefore just return Any.
                            return Ok(TypeVarBound::Invariant(Type::Any));
                        }
                        if value_type.has_any(i_s) {
                            matched_constraint = Some(constraint);
                        } else {
                            return Ok(TypeVarBound::Invariant(constraint.clone()));
                        }
                    }
                }
                mismatch_constraints = true;
            }
        }
    }
    if mismatch_constraints {
        Err(Match::False {
            reason: MismatchReason::ConstraintMismatch {
                expected: value_type.clone(),
                type_var: type_var.clone(),
            },
            similar: false,
        })
    } else {
        Ok(TypeVarBound::new(value_type.clone(), variance, type_var))
    }
}
