use std::{borrow::Cow, rc::Rc};

use parsa_python_ast::ParamKind;

use super::{
    super::{Match, MismatchReason},
    bound::TypeVarBound,
};
use crate::{
    database::{Database, PointLink},
    debug,
    inference_state::InferenceState,
    matching::Param,
    type_::{
        common_base_type_of_type_var_tuple_with_items, AnyCause, CallableParams, GenericItem,
        GenericsList, ParamSpecArg, ParamType, TupleArgs, Type, TypeArgs, TypeVar, TypeVarKind,
        TypeVarLike, TypeVarLikeUsage, TypeVarLikes, TypeVarUsage, Variance,
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

#[derive(Debug, Clone, PartialEq)]
pub enum BoundKind {
    TypeVar(TypeVarBound),
    TypeVarTuple(TupleArgs),
    ParamSpec(CallableParams),
    Uncalculated { fallback: Option<Type> },
}

impl Default for BoundKind {
    fn default() -> Self {
        Self::Uncalculated { fallback: None }
    }
}

impl BoundKind {
    pub fn merge(&mut self, db: &Database, other: Self) -> Match {
        if self == &other {
            return Match::new_true();
        }
        let i_s = InferenceState::new(db);
        match (self, other) {
            (Self::TypeVar(bound1), Self::TypeVar(bound2)) => {
                let mut m = Match::new_true();
                let (t, variance) = match bound2 {
                    TypeVarBound::Upper(t) => (t, Variance::Contravariant),
                    TypeVarBound::Lower(t) => (t, Variance::Covariant),
                    TypeVarBound::Invariant(t) => (t, Variance::Invariant),
                    TypeVarBound::UpperAndLower(upper, t) => {
                        m = bound1.merge_or_mismatch(&i_s, &upper, Variance::Contravariant);
                        (t, Variance::Covariant)
                    }
                };
                m & bound1.merge_or_mismatch(&i_s, &t, variance)
            }
            (Self::TypeVarTuple(tup1), Self::TypeVarTuple(tup2)) => {
                dbg!(tup1, tup2);
                //match_tuple_type_arguments(&i_s, &mut Matcher::default(), tup1, &tup2, Variance::Invariant);
                todo!()
            }
            (Self::ParamSpec(p1), Self::ParamSpec(p2)) => {
                dbg!(p1, p2);
                todo!()
            }
            (Self::Uncalculated { fallback: Some(_) }, Self::Uncalculated { .. }) => {
                Match::new_true()
            }
            (slf @ Self::Uncalculated { fallback: _ }, other) => {
                *slf = other;
                Match::new_true()
            }
            (_, Self::Uncalculated { fallback: _ }) => Match::new_true(),
            _ => unreachable!(),
        }
    }

    pub fn search_type_vars<C: FnMut(TypeVarLikeUsage) + ?Sized>(&self, found_type_var: &mut C) {
        match self {
            Self::TypeVar(tv) => {
                let t = match tv {
                    TypeVarBound::Invariant(t)
                    | TypeVarBound::Lower(t)
                    | TypeVarBound::Upper(t) => t,
                    TypeVarBound::UpperAndLower(upper, lower) => {
                        upper.search_type_vars(found_type_var);
                        lower
                    }
                };
                t.search_type_vars(found_type_var)
            }
            Self::TypeVarTuple(tup) => tup.search_type_vars(found_type_var),
            Self::ParamSpec(params) => params.search_type_vars(found_type_var),
            Self::Uncalculated { fallback: Some(t) } => t.search_type_vars(found_type_var),
            Self::Uncalculated { fallback: None } => (),
        }
    }
    pub fn replace_type_var_likes(
        &self,
        db: &Database,
        on_type_var_like: &mut impl FnMut(TypeVarLikeUsage) -> GenericItem,
    ) -> Self {
        match self {
            Self::TypeVar(tv) => Self::TypeVar(match tv {
                TypeVarBound::Invariant(t) => {
                    TypeVarBound::Invariant(t.replace_type_var_likes(db, on_type_var_like))
                }
                TypeVarBound::Upper(t) => {
                    TypeVarBound::Upper(t.replace_type_var_likes(db, on_type_var_like))
                }
                TypeVarBound::Lower(t) => {
                    TypeVarBound::Upper(t.replace_type_var_likes(db, on_type_var_like))
                }
                TypeVarBound::UpperAndLower(upper, lower) => TypeVarBound::UpperAndLower(
                    upper.replace_type_var_likes(db, on_type_var_like),
                    lower.replace_type_var_likes(db, on_type_var_like),
                ),
            }),
            Self::TypeVarTuple(tup) => BoundKind::TypeVarTuple(
                tup.replace_type_var_likes_and_self(db, on_type_var_like, &|| Type::Self_),
            ),
            Self::ParamSpec(params) => Self::ParamSpec(
                params
                    .replace_type_var_likes_and_self(db, &mut None, None, on_type_var_like, &|| {
                        Type::Self_
                    })
                    .0,
            ),
            Self::Uncalculated { fallback: Some(t) } => Self::Uncalculated {
                fallback: Some(t.replace_type_var_likes(db, on_type_var_like)),
            },
            Self::Uncalculated { fallback: None } => Self::Uncalculated { fallback: None },
        }
    }
}

#[derive(Debug, Default, Clone)]
pub(super) struct CalculatingTypeArg {
    pub(super) type_: BoundKind,
    pub(super) unresolved_transitive_constraints: Vec<BoundKind>,
    pub(super) defined_by_result_context: bool,
}

impl CalculatingTypeArg {
    pub fn calculated(&self) -> bool {
        !matches!(self.type_, BoundKind::Uncalculated { .. })
    }

    pub fn set_to_any(&mut self, tv: &TypeVarLike, cause: AnyCause) {
        self.type_ = match tv {
            TypeVarLike::TypeVar(_) => {
                BoundKind::TypeVar(TypeVarBound::Invariant(Type::Any(cause)))
            }
            TypeVarLike::TypeVarTuple(_) => {
                BoundKind::TypeVarTuple(TupleArgs::ArbitraryLen(Box::new(Type::Any(cause))))
            }
            TypeVarLike::ParamSpec(_) => BoundKind::ParamSpec(CallableParams::Any(cause)),
        }
    }

    pub fn match_or_add_type_var_tuple(&mut self, i_s: &InferenceState, args2: TupleArgs) -> Match {
        match &mut self.type_ {
            BoundKind::TypeVarTuple(current) => match args2 {
                TupleArgs::FixedLen(ts) => {
                    common_base_type_of_type_var_tuple_with_items(current, i_s, ts.iter())
                }
                TupleArgs::ArbitraryLen(t2) => match current {
                    TupleArgs::ArbitraryLen(t1) => *t1 = Box::new(t1.common_base_type(i_s, &t2)),
                    TupleArgs::FixedLen(_) => todo!(),
                    TupleArgs::WithUnpack(_) => todo!(),
                },
                TupleArgs::WithUnpack(ts) => {
                    debug!("TODO implement withunpack merging {current:?} {ts:?}");
                }
            },
            BoundKind::Uncalculated { .. } => {
                self.type_ = BoundKind::TypeVarTuple(args2);
            }
            _ => unreachable!(),
        }
        Match::new_true()
    }

    pub fn into_generic_item(self, db: &Database, type_var_like: &TypeVarLike) -> GenericItem {
        match self.type_ {
            BoundKind::TypeVar(t) => GenericItem::TypeArg(t.into_type(db)),
            BoundKind::TypeVarTuple(ts) => GenericItem::TypeArgs(TypeArgs::new(ts)),
            BoundKind::ParamSpec(params) => GenericItem::ParamSpecArg(ParamSpecArg {
                params,
                type_vars: None,
            }),
            BoundKind::Uncalculated { fallback } => {
                if let Some(fallback) = fallback {
                    GenericItem::TypeArg(fallback)
                } else {
                    match type_var_like {
                        TypeVarLike::TypeVar(_) => GenericItem::TypeArg(Type::Never),
                        // TODO TypeVarTuple: this feels wrong, should maybe be never?
                        TypeVarLike::TypeVarTuple(_) => {
                            GenericItem::TypeArgs(TypeArgs::new_fixed_length(Rc::new([])))
                        }
                        // TODO ParamSpec: this feels wrong, should maybe be never?
                        TypeVarLike::ParamSpec(_) => {
                            GenericItem::ParamSpecArg(ParamSpecArg::new_any(AnyCause::Todo))
                        }
                    }
                }
            }
        }
    }

    pub fn maybe_calculated_type(self, db: &Database) -> Option<Type> {
        // Expects only TypeVars, no TypeVarTuples or ParamSpecs
        match self.type_ {
            BoundKind::TypeVar(bound) => Some(bound.into_type(db)),
            BoundKind::Uncalculated { .. } => None,
            _ => unreachable!(),
        }
    }

    pub fn avoid_type_vars_from_class_self_arguments(&mut self, class: Class) {
        let is_self_type_var = match &self.type_ {
            BoundKind::TypeVar(
                TypeVarBound::Invariant(t) | TypeVarBound::Lower(t) | TypeVarBound::Upper(t),
            ) => match t {
                Type::TypeVar(tv) if class.node_ref.as_link() == tv.in_definition => true,
                _ => false,
            },
            BoundKind::TypeVar(TypeVarBound::UpperAndLower(_, _)) => unreachable!(),
            BoundKind::TypeVarTuple(tvt) => todo!(),
            BoundKind::ParamSpec(p) => match p {
                CallableParams::WithParamSpec(pre, p2)
                    if pre.is_empty() && class.node_ref.as_link() == p2.in_definition =>
                {
                    true
                }
                _ => false,
            },
            BoundKind::Uncalculated { .. } => false,
        };
        if is_self_type_var {
            self.type_ = BoundKind::Uncalculated { fallback: None };
        }
    }
}

#[derive(Debug, Clone)]
pub struct TypeVarMatcher {
    pub(super) calculating_type_args: Vec<CalculatingTypeArg>,
    pub(super) type_var_likes: TypeVarLikes,
    pub(super) match_in_definition: PointLink,
    pub match_reverse: bool,
    pub enabled: bool,
}

impl TypeVarMatcher {
    pub fn new(match_in_definition: PointLink, type_var_likes: TypeVarLikes) -> Self {
        Self::new_internal(match_in_definition, type_var_likes, false)
    }

    pub fn new_reverse(match_in_definition: PointLink, type_var_likes: TypeVarLikes) -> Self {
        Self::new_internal(match_in_definition, type_var_likes, true)
    }

    fn new_internal(
        match_in_definition: PointLink,
        type_var_likes: TypeVarLikes,
        match_reverse: bool,
    ) -> Self {
        // We could allocate on stack as described here:
        // https://stackoverflow.com/questions/27859822/is-it-possible-to-have-stack-allocated-arrays-with-the-size-determined-at-runtim
        let mut calculated_type_vars = vec![];
        calculated_type_vars.resize_with(type_var_likes.len(), Default::default);
        Self {
            calculating_type_args: calculated_type_vars,
            match_in_definition,
            type_var_likes,
            match_reverse,
            enabled: true,
        }
    }

    pub fn set_all_contained_type_vars_to_any(
        &mut self,
        i_s: &InferenceState,
        type_: &Type,
        cause: AnyCause,
    ) {
        type_.search_type_vars(&mut |t| {
            if t.in_definition() == self.match_in_definition {
                let current = &mut self.calculating_type_args[t.index().as_usize()];
                if !current.calculated() {
                    current.set_to_any(&t.as_type_var_like(), cause)
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
        debug_assert_eq!(type_var_usage.in_definition, self.match_in_definition);
        let current = &mut self.calculating_type_args[type_var_usage.index.as_usize()];
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
                            return Ok(TypeVarBound::Invariant(Type::Any(AnyCause::Todo)));
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
