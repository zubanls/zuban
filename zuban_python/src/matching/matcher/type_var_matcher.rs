use std::borrow::Cow;

use super::super::{Match, MismatchReason, Type};
use super::bound::TypeVarBound;
use crate::database::{
    CallableContent, Database, DbType, GenericItem, ParamSpecArgument, PointLink,
    TupleTypeArguments, TypeArguments, TypeOrTypeVarTuple, TypeVar, TypeVarLike, TypeVarLikeUsage,
    TypeVarUsage, Variance,
};
use crate::inference_state::InferenceState;
use crate::value::Function;

#[derive(Debug, Clone, Copy)]
pub enum FunctionOrCallable<'a> {
    Function(Function<'a, 'a>),
    Callable(&'a CallableContent),
}

#[derive(Debug, Clone)]
pub enum BoundKind {
    TypeVar(TypeVarBound),
    TypeVarTuple(TypeArguments),
    ParamSpecArgument(ParamSpecArgument),
    Uncalculated,
}

impl Default for BoundKind {
    fn default() -> Self {
        Self::Uncalculated
    }
}

#[derive(Debug, Default, Clone)]
pub struct CalculatedTypeVarLike {
    pub(super) type_: BoundKind,
    pub(super) defined_by_result_context: bool,
}

fn common_base_class<'x, I: Iterator<Item = &'x TypeOrTypeVarTuple>>(
    i_s: &mut InferenceState,
    mut ts: I,
) -> DbType {
    if let Some(first) = ts.next() {
        let mut result = match first {
            TypeOrTypeVarTuple::Type(t) => Cow::Borrowed(t),
            TypeOrTypeVarTuple::TypeVarTuple(_) => return i_s.db.python_state.object_db_type(),
        };
        for t in ts {
            let t = match t {
                TypeOrTypeVarTuple::Type(t) => t,
                TypeOrTypeVarTuple::TypeVarTuple(_) => return i_s.db.python_state.object_db_type(),
            };
            result = Cow::Owned(Type::Type(result).common_base_class(i_s, &Type::new(t)));
        }
        result.into_owned()
    } else {
        todo!("should probably return never")
    }
}

impl CalculatedTypeVarLike {
    pub fn calculated(&self) -> bool {
        !matches!(self.type_, BoundKind::Uncalculated)
    }

    pub fn merge_fixed_length_type_var_tuple<'x, I: Iterator<Item = &'x TypeOrTypeVarTuple>>(
        &mut self,
        i_s: &mut InferenceState,
        fetch: usize,
        items: I,
    ) {
        match &mut self.type_ {
            BoundKind::TypeVarTuple(ts) => match &mut ts.args {
                TupleTypeArguments::FixedLength(calc_ts) => {
                    if fetch == calc_ts.len() {
                        for (t1, t2) in calc_ts.iter_mut().zip(items) {
                            match (t1, t2) {
                                (TypeOrTypeVarTuple::Type(t1), TypeOrTypeVarTuple::Type(t2)) => {
                                    *t1 = Type::new(t1).common_base_class(i_s, &Type::new(t2));
                                }
                                _ => todo!(),
                            }
                        }
                    } else {
                        // We use map to make an iterator with covariant lifetimes.
                        #[allow(clippy::map_identity)]
                        let t = common_base_class(i_s, calc_ts.iter().chain(items.map(|x| x)));
                        ts.args = TupleTypeArguments::ArbitraryLength(Box::new(t));
                    }
                }
                TupleTypeArguments::ArbitraryLength(calc_t) => {
                    let base = common_base_class(i_s, items);
                    //self.merge_arbitrary_length_type_var_tuple(i_s, &base)
                }
            },
            _ => unreachable!(),
        }
    }

    pub fn merge_arbitrary_length_type_var_tuple(
        &mut self,
        i_s: &mut InferenceState,
        item: &DbType,
    ) {
        todo!()
    }

    pub fn into_generic_item(self, db: &Database, type_var_like: &TypeVarLike) -> GenericItem {
        match self.type_ {
            BoundKind::TypeVar(t) => GenericItem::TypeArgument(t.into_db_type(db)),
            BoundKind::TypeVarTuple(ts) => GenericItem::TypeArguments(ts),
            BoundKind::ParamSpecArgument(params) => GenericItem::ParamSpecArgument(params),
            BoundKind::Uncalculated => match type_var_like {
                TypeVarLike::TypeVar(_) => GenericItem::TypeArgument(DbType::Never),
                // TODO TypeVarTuple: this feels wrong, should maybe be never?
                TypeVarLike::TypeVarTuple(_) => {
                    GenericItem::TypeArguments(TypeArguments::new_fixed_length(Box::new([])))
                }
                // TODO ParamSpec: this feels wrong, should maybe be never?
                TypeVarLike::ParamSpec(_) => {
                    GenericItem::ParamSpecArgument(ParamSpecArgument::new_any())
                }
            },
        }
    }
}

#[derive(Debug)]
pub struct TypeVarMatcher {
    pub(super) calculated_type_vars: Vec<CalculatedTypeVarLike>,
    pub(super) match_in_definition: PointLink,
    pub match_reverse: bool, // For contravariance subtypes
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
            match_reverse: false,
        }
    }

    pub fn set_all_contained_type_vars_to_any(&mut self, i_s: &mut InferenceState, type_: &DbType) {
        type_.search_type_vars(&mut |t| {
            if t.in_definition() == self.match_in_definition {
                let current = &mut self.calculated_type_vars[t.index().as_usize()];
                if !current.calculated() {
                    current.type_ = match t {
                        TypeVarLikeUsage::TypeVar(_) => {
                            BoundKind::TypeVar(TypeVarBound::Invariant(DbType::Any))
                        }
                        TypeVarLikeUsage::TypeVarTuple(_) => BoundKind::TypeVarTuple(
                            TypeArguments::new_arbitrary_length(DbType::Any),
                        ),
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
        i_s: &mut InferenceState,
        type_var_usage: &TypeVarUsage,
        type_var: &TypeVar,
        value_type: &Type,
        variance: Variance,
    ) -> Match {
        let type_var_like = &type_var_usage.type_var;
        let current = &mut self.calculated_type_vars[type_var_usage.index.as_usize()];
        if let BoundKind::TypeVar(current_type) = &mut current.type_ {
            let m = current_type.merge_or_mismatch(i_s, value_type, variance);
            return match m.bool() || !type_var.restrictions.is_empty() {
                true => m,
                false => match current.defined_by_result_context {
                    true => Match::new_false(),
                    false => Match::False {
                        reason: MismatchReason::CannotInferTypeArgument(type_var_usage.index),
                        similar: false,
                    },
                },
            };
        } else {
            debug_assert!(!current.calculated(), "{current:?}");
        }
        // Before setting the type var, we need to check if the constraints match.
        let mut mismatch_constraints = false;
        if !type_var.restrictions.is_empty() {
            if let Some(DbType::TypeVar(t2)) = value_type.maybe_db_type() {
                if !t2.type_var.restrictions.is_empty() {
                    if current.calculated() {
                        todo!()
                    } else if t2.type_var.restrictions.iter().all(|r2| {
                        type_var.restrictions.iter().any(|r1| {
                            Type::new(r1)
                                .is_simple_super_type_of(i_s, &Type::new(r2))
                                .bool()
                        })
                    }) {
                        current.type_ =
                            BoundKind::TypeVar(TypeVarBound::Invariant(value_type.as_db_type(i_s)));
                        return Match::new_true();
                    } else {
                        mismatch_constraints = true;
                    }
                }
            }
            if !mismatch_constraints {
                for restriction in type_var.restrictions.iter() {
                    let m = Type::new(restriction).simple_matches(i_s, value_type, variance);
                    if m.bool() {
                        if current.calculated() {
                            // This means that any is involved and multiple restrictions
                            // are matching. Therefore just return Any.
                            current.type_ =
                                BoundKind::TypeVar(TypeVarBound::Invariant(DbType::Any));
                            return m;
                        }
                        current.type_ =
                            BoundKind::TypeVar(TypeVarBound::Invariant(restriction.clone()));
                        if !value_type.has_any(i_s) {
                            return m;
                        }
                    }
                }
                mismatch_constraints = true;
            }
        }
        if let Some(bound) = &type_var.bound {
            mismatch_constraints |= !Type::new(bound)
                .is_simple_super_type_of(i_s, value_type)
                .bool();
        }
        if mismatch_constraints {
            return Match::False {
                reason: MismatchReason::ConstraintMismatch {
                    expected: value_type.as_db_type(i_s),
                    type_var: type_var_usage.type_var.clone(),
                },
                similar: false,
            };
        }
        current.type_ = BoundKind::TypeVar(TypeVarBound::new(value_type.as_db_type(i_s), variance));
        if matches!(value_type.maybe_db_type(), Some(DbType::Any)) {
            Match::True { with_any: true }
        } else {
            Match::new_true()
        }
    }
}
