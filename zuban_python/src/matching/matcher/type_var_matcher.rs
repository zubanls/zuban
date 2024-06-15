use std::{borrow::Cow, rc::Rc};

use parsa_python_cst::ParamKind;

use super::{
    super::{Match, MismatchReason},
    bound::{Bound, BoundKind},
};
use crate::{
    database::{Database, PointLink},
    inference_state::InferenceState,
    matching::Param,
    type_::{
        AnyCause, CallableParams, GenericItem, GenericsList, NeverCause, ParamType, Type, TypeVar,
        TypeVarKind, TypeVarLike, TypeVarLikeUsage, TypeVarLikes, TypeVarUsage, Variance,
    },
    type_helpers::{Callable, Class, Function},
};

#[derive(Debug, Clone, Copy)]
pub enum FunctionOrCallable<'a> {
    Function(Function<'a, 'a>),
    Callable(Callable<'a>),
}

impl<'db: 'a, 'a> FunctionOrCallable<'a> {
    pub fn return_type(&self, i_s: &InferenceState<'db, '_>) -> Cow<'a, Type> {
        match self {
            Self::Function(f) => f.return_type(i_s),
            Self::Callable(c) => Cow::Borrowed(&c.content.return_type),
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

    pub fn first_self_or_class_annotation(
        &self,
        i_s: &InferenceState<'db, '_>,
    ) -> Option<Cow<Type>> {
        match self {
            Self::Function(function) => function.first_param_annotation_type(i_s),
            Self::Callable(c) => c
                .content
                .kind
                .had_first_self_or_class_annotation()
                .then(|| Cow::Owned(c.content.first_positional_type().unwrap())),
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
                    p.name.as_ref().is_some_and(|n| {
                        n.as_str(db) == name
                            && matches!(
                                p.type_,
                                ParamType::PositionalOrKeyword(_) | ParamType::KeywordOnly(_)
                            )
                    })
                }),
                _ => false,
            },
        }
    }
}

#[derive(Debug, Default, Clone)]
pub(super) struct CalculatingTypeArg {
    pub(super) type_: Bound,
    pub(super) unresolved_transitive_constraints: Vec<Bound>,
    pub(super) defined_by_result_context: bool,
}

impl CalculatingTypeArg {
    pub fn calculated(&self) -> bool {
        !matches!(self.type_, Bound::Uncalculated { .. })
    }

    pub fn merge_full(&mut self, db: &Database, other: Self) -> Match {
        self.defined_by_result_context |= other.defined_by_result_context;
        self.merge(db, other.type_)
    }

    pub fn merge(&mut self, db: &Database, other: Bound) -> Match {
        if self.type_ == other {
            return Match::new_true();
        }
        let i_s = InferenceState::new(db);
        let mut m = Match::new_true();
        if let Bound::Uncalculated { fallback } = &self.type_ {
            if !matches!(&other, Bound::Uncalculated { .. }) || fallback.is_none() {
                self.type_ = other;
            }
            return Match::new_true();
        }
        let (t, variance) = match other {
            Bound::Upper(t) => (t, Variance::Contravariant),
            Bound::Lower(t) => (t, Variance::Covariant),
            Bound::Invariant(t) => (t, Variance::Invariant),
            Bound::UpperAndLower(upper, t) => {
                m = self.merge_or_mismatch(&i_s, &upper, Variance::Contravariant);
                (t, Variance::Covariant)
            }
            Bound::Uncalculated { .. } => return Match::new_true(),
        };
        m & self.merge_or_mismatch(&i_s, &t, variance)
    }

    pub fn merge_or_mismatch(
        &mut self,
        i_s: &InferenceState,
        other: &BoundKind,
        variance: Variance,
    ) -> Match {
        // First check if the value is between the bounds.
        let matches = match &mut self.type_ {
            Bound::Invariant(t) => {
                let m = t.is_simple_same_type(i_s, other);
                if m.bool() {
                    return m; // In the false case we still have to check for the variance cases.
                }
                m
            }
            Bound::Upper(lower) => lower.is_simple_super_type_of(i_s, other),
            Bound::Lower(upper) => upper.is_simple_sub_type_of(i_s, other),
            Bound::UpperAndLower(lower, upper) => {
                lower.is_simple_super_type_of(i_s, other) & upper.is_simple_sub_type_of(i_s, other)
            }
            Bound::Uncalculated { .. } => unreachable!(),
        };
        if matches.bool() {
            // If we are between the bounds we might need to update lower/upper bounds
            match variance {
                Variance::Invariant => self.type_ = Bound::Invariant(other.clone()),
                Variance::Covariant => self.type_.update_lower_bound(i_s, other),
                Variance::Contravariant => self.type_.update_upper_bound(i_s, other),
            }
        } else {
            // If we are not between the lower and upper bound, but the value is co or
            // contravariant, it can still be valid.
            match variance {
                Variance::Invariant => (),
                Variance::Covariant => match &mut self.type_ {
                    Bound::Lower(t) => {
                        // TODO shouldn't this also do a limited common base type search in the
                        // case of LowerAndUpper?
                        let m = t.is_simple_super_type_of(i_s, other);
                        *t = t.common_base_type(i_s, other);
                        if !m.bool() {
                            return Match::new_true();
                        }
                        return m;
                    }
                    Bound::Invariant(t) | Bound::UpperAndLower(_, t) => {
                        return t.is_simple_super_type_of(i_s, other)
                    }
                    Bound::Upper(t) => {}
                    Bound::Uncalculated { .. } => unreachable!(),
                },
                Variance::Contravariant => match &mut self.type_ {
                    Bound::Upper(t) => {
                        // TODO shouldn't we also check LowerAndUpper like this?
                        let m = t.is_simple_sub_type_of(i_s, other);
                        if !m.bool() {
                            if let Some(new) = t.common_sub_type(i_s, other) {
                                *t = new;
                                return Match::new_true();
                            } else {
                                return Match::new_false();
                            }
                        }
                        return m;
                    }
                    Bound::Invariant(t) | Bound::UpperAndLower(t, _) => {
                        return t.is_simple_sub_type_of(i_s, other);
                    }
                    Bound::Lower(_) => {}
                    Bound::Uncalculated { .. } => unreachable!(),
                },
            };
        }
        matches
    }

    pub fn into_generic_item(self, db: &Database, type_var_like: &TypeVarLike) -> GenericItem {
        self.type_.into_generic_item(db, |fallback| {
            if let Some(fallback) = fallback {
                GenericItem::TypeArg(fallback)
            } else {
                type_var_like.as_never_generic_item(NeverCause::Inference)
            }
        })
    }
}

#[derive(Debug, Clone)]
pub struct TypeVarMatcher {
    pub(super) calculating_type_args: Vec<CalculatingTypeArg>,
    pub(super) type_var_likes: TypeVarLikes,
    pub(super) match_in_definition: PointLink,
}

impl TypeVarMatcher {
    pub fn new(match_in_definition: PointLink, type_var_likes: TypeVarLikes) -> Self {
        Self::new_internal(match_in_definition, type_var_likes)
    }

    fn new_internal(match_in_definition: PointLink, type_var_likes: TypeVarLikes) -> Self {
        // We could allocate on stack as described here:
        // https://stackoverflow.com/questions/27859822/is-it-possible-to-have-stack-allocated-arrays-with-the-size-determined-at-runtim
        let mut calculated_type_vars = vec![];
        calculated_type_vars.resize_with(type_var_likes.len(), Default::default);
        Self {
            calculating_type_args: calculated_type_vars,
            match_in_definition,
            type_var_likes,
        }
    }

    pub fn set_all_contained_type_vars_to_any(
        &mut self,
        i_s: &InferenceState,
        search_type_vars: impl FnOnce(&mut dyn FnMut(TypeVarLikeUsage)),
        matcher_index: u32,
        cause: AnyCause,
    ) {
        search_type_vars(&mut |usage: TypeVarLikeUsage| {
            if usage.in_definition() == self.match_in_definition {
                let temporary_matcher_id = usage.temporary_matcher_id();
                if temporary_matcher_id == 0 || temporary_matcher_id == matcher_index {
                    let current = &mut self.calculating_type_args[usage.index().as_usize()];
                    if !current.calculated() {
                        current.type_.set_to_any(&usage.as_type_var_like(), cause)
                    }
                }
            }
        });
    }

    pub fn match_or_add_type_var(
        &mut self,
        i_s: &InferenceState,
        type_var_usage: &TypeVarUsage,
        value_type: &Type,
        variance: Variance,
    ) -> Match {
        debug_assert_eq!(type_var_usage.in_definition, self.match_in_definition);
        let current = &mut self.calculating_type_args[type_var_usage.index.as_usize()];
        if current.calculated() {
            return current.merge_or_mismatch(
                i_s,
                &BoundKind::TypeVar(value_type.clone()),
                variance,
            );
        }
        // Before setting the type var, we need to check if the constraints match.
        match check_constraints(i_s, &type_var_usage.type_var, value_type, variance) {
            Ok(bound) => {
                current.type_ = bound;
                if value_type.is_any() {
                    Match::True { with_any: true }
                } else {
                    Match::new_true()
                }
            }
            Err(m) => {
                current.type_ = Bound::Uncalculated {
                    fallback: Some(value_type.clone()),
                };
                m
            }
        }
    }

    pub fn into_generics_list(self, db: &Database) -> GenericsList {
        GenericsList::new_generics(
            self.calculating_type_args
                .into_iter()
                .zip(self.type_var_likes.iter())
                .map(|(c, type_var_like)| c.into_generic_item(db, type_var_like))
                .collect(),
        )
    }

    pub fn has_unresolved_transitive_constraints(&self) -> bool {
        self.calculating_type_args
            .iter()
            .any(|calculated| !calculated.unresolved_transitive_constraints.is_empty())
    }
}

pub fn check_constraints(
    i_s: &InferenceState,
    type_var: &Rc<TypeVar>,
    value_type: &Type,
    variance: Variance,
) -> Result<Bound, Match> {
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
                        return Ok(Bound::Invariant(BoundKind::TypeVar(value_type.clone())));
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
                            return Ok(Bound::Invariant(BoundKind::TypeVar(Type::Any(
                                AnyCause::Todo,
                            ))));
                        }
                        if value_type.has_any(i_s) {
                            matched_constraint = Some(constraint);
                        } else {
                            return Ok(Bound::Invariant(BoundKind::TypeVar(constraint.clone())));
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
        Ok(Bound::new_type_arg(value_type.clone(), variance, type_var))
    }
}
