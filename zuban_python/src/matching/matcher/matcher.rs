use super::super::{FormatData, Match, MismatchReason, Type};
use super::bound::TypeVarBound;
use super::type_var_matcher::{CalculatedTypeVar, FunctionOrCallable, TypeVarMatcher};

use crate::database::{
    CallableContent, Database, DbType, FormatStyle, RecursiveAlias, TypeVarUsage, TypeVars,
    Variance,
};
use crate::inference_state::InferenceState;
use crate::value::Function;

struct CheckedTypeRecursion {}

#[derive(Default)]
pub struct Matcher<'a> {
    type_var_matcher: Option<TypeVarMatcher<'a>>,
    checked_type_recursions: Vec<CheckedTypeRecursion>,
}

impl<'a> Matcher<'a> {
    pub fn new(type_var_matcher: Option<TypeVarMatcher<'a>>) -> Self {
        Self {
            type_var_matcher,
            ..Self::default()
        }
    }

    pub fn new_reverse_callable_matcher(
        callable: &'a CallableContent,
        calculated_type_vars: &'a mut [CalculatedTypeVar],
    ) -> Self {
        let mut m = TypeVarMatcher::new(
            None,
            FunctionOrCallable::Callable(callable),
            callable.defined_at,
            calculated_type_vars,
        );
        m.match_reverse = true;
        Self {
            type_var_matcher: Some(m),
            ..Self::default()
        }
    }

    pub fn new_reverse_function_matcher(
        function: Function<'a>,
        type_vars: Option<&TypeVars>,
        calculated_type_vars: &'a mut Vec<CalculatedTypeVar>,
    ) -> Self {
        if let Some(type_vars) = type_vars {
            calculated_type_vars.resize_with(type_vars.len(), Default::default);
            let mut m = TypeVarMatcher::new(
                None,
                FunctionOrCallable::Function(function),
                function.node_ref.as_link(),
                calculated_type_vars,
            );
            m.match_reverse = true;
            Self {
                type_var_matcher: Some(m),
                ..Self::default()
            }
        } else {
            Matcher::default()
        }
    }

    #[inline]
    pub fn has_type_var_matcher(&self) -> bool {
        self.type_var_matcher.is_some()
    }

    pub fn is_matching_reverse(&self) -> bool {
        self.type_var_matcher
            .as_ref()
            .map(|m| m.match_reverse)
            .unwrap_or(false)
    }

    pub fn match_reverse(&mut self) {
        if let Some(matcher) = self.type_var_matcher.as_mut() {
            matcher.match_reverse = !matcher.match_reverse;
        }
    }

    pub fn match_or_add_type_var(
        &mut self,
        i_s: &mut InferenceState,
        t1: &TypeVarUsage,
        value_type: &Type,
        variance: Variance,
    ) -> Match {
        match self.type_var_matcher.as_mut() {
            Some(matcher) => {
                self.match_or_add_type_var_in_type_var_matcher(i_s, t1, value_type, variance)
            }
            None => match value_type.maybe_db_type() {
                Some(DbType::TypeVar(t2)) => {
                    (t1.index == t2.index && t1.in_definition == t2.in_definition).into()
                }
                _ => Match::new_false(),
            },
        }
    }

    fn match_or_add_type_var_in_type_var_matcher(
        &mut self,
        i_s: &mut InferenceState,
        type_var_usage: &TypeVarUsage,
        value_type: &Type,
        variance: Variance,
    ) -> Match {
        let type_var_matcher = self.type_var_matcher.as_mut().unwrap();
        let type_var = &type_var_usage.type_var;
        if type_var_matcher.match_in_definition == type_var_usage.in_definition {
            let current =
                &mut type_var_matcher.calculated_type_vars[type_var_usage.index.as_usize()];
            if let Some(current_type) = &mut current.type_ {
                let m = current_type.merge_or_mismatch(i_s, value_type, variance);
                return match m.bool() || !type_var_usage.type_var.restrictions.is_empty() {
                    true => m,
                    false => match current.defined_by_result_context {
                        true => Match::new_false(),
                        false => Match::False(MismatchReason::CannotInferTypeArgument(
                            type_var_usage.index,
                        )),
                    },
                };
            }
            // Before setting the type var, we need to check if the constraints match.
            let mut mismatch_constraints = false;
            if !type_var.restrictions.is_empty() {
                match value_type.maybe_db_type() {
                    Some(DbType::TypeVar(t2)) if !t2.type_var.restrictions.is_empty() => {
                        if let Some(type_) = &current.type_ {
                            todo!()
                        } else if t2.type_var.restrictions.iter().all(|r2| {
                            type_var.restrictions.iter().any(|r1| {
                                Type::new(r1)
                                    .is_simple_super_type_of(i_s, &Type::new(r2))
                                    .bool()
                            })
                        }) {
                            current.type_ =
                                Some(TypeVarBound::Invariant(value_type.as_db_type(i_s)));
                            return Match::True;
                        }
                    }
                    _ => {
                        for restriction in type_var.restrictions.iter() {
                            let m =
                                Type::new(restriction).simple_matches(i_s, value_type, variance);
                            if m.bool() {
                                if current.type_.is_some() {
                                    // This means that any is involved and multiple restrictions
                                    // are matching. Therefore just return Any.
                                    current.type_ = Some(TypeVarBound::Invariant(DbType::Any));
                                    return m;
                                }
                                current.type_ = Some(TypeVarBound::Invariant(restriction.clone()));
                                if !value_type.has_any(i_s) {
                                    return m;
                                }
                            }
                        }
                    }
                }
                mismatch_constraints = true;
            }
            if let Some(bound) = &type_var.bound {
                mismatch_constraints |= !Type::new(bound)
                    .is_simple_super_type_of(i_s, value_type)
                    .bool();
            }
            if mismatch_constraints {
                return Match::False(MismatchReason::ConstraintMismatch {
                    expected: value_type.as_db_type(i_s),
                    type_var: type_var_usage.type_var.clone(),
                });
            }
            current.type_ = Some(TypeVarBound::new(value_type.as_db_type(i_s), variance));
            if matches!(value_type.maybe_db_type(), Some(DbType::Any)) {
                Match::TrueWithAny
            } else {
                Match::True
            }
        } else {
            if let Some(parent_matcher) = type_var_matcher.parent_matcher.as_mut() {
                todo!()
            }
            if let Some(class) = type_var_matcher.class {
                if class.node_ref.as_link() == type_var_usage.in_definition {
                    let g = class.generics.nth(i_s, type_var_usage.index);
                    return g.simple_matches(i_s, value_type, type_var.variance);
                }
            }
            match type_var_matcher.func_or_callable {
                FunctionOrCallable::Function(f) => {
                    // If we're in a class context, we must also be in a method.
                    if let Some(func_class) = f.class {
                        if type_var_usage.in_definition == func_class.node_ref.as_link() {
                            // By definition, because the class did not match there will never be a
                            // type_var_remap that is not defined.
                            let type_var_remap = func_class.type_var_remap.unwrap();
                            let g = Type::new(&type_var_remap[type_var_usage.index]);
                            // The remapping of type vars needs to be checked now. In a lot of
                            // cases this is T -> T and S -> S, but it could also be T -> S and S
                            // -> List[T] or something completely arbitrary.
                            g.matches(i_s, self, value_type, type_var.variance)
                        } else {
                            // Happens e.g. for testInvalidNumberOfTypeArgs
                            // class C:  # Forgot to add type params here
                            //     def __init__(self, t: T) -> None: pass
                            if let Some(DbType::TypeVar(v)) = value_type.maybe_db_type() {
                                if v == type_var_usage {
                                    return Match::True;
                                }
                            }
                            todo!(
                                "TODO free type param annotations; searched ({:?}), found {:?}",
                                type_var_matcher.match_in_definition,
                                type_var_usage.in_definition,
                            )
                        }
                    } else {
                        todo!(
                            "Probably nested generic functions??? {:?} {:?}",
                            type_var_usage.in_definition,
                            type_var_matcher.match_in_definition
                        )
                    }
                }
                FunctionOrCallable::Callable(c) => todo!(),
            }
        }
    }

    pub fn format_in_type_var_matcher(
        &self,
        db: &Database,
        type_var_usage: &TypeVarUsage,
        style: FormatStyle,
    ) -> Box<str> {
        let type_var_matcher = self.type_var_matcher.as_ref().unwrap();
        let i_s = &mut InferenceState::new(db);
        // In general this whole function should look very similar to the matches function, since
        // on mismatches this can be run.
        if type_var_matcher.match_in_definition == type_var_usage.in_definition {
            let current = &type_var_matcher.calculated_type_vars[type_var_usage.index.as_usize()];
            if let Some(bound) = current.type_.as_ref() {
                bound.format(i_s, style)
            } else {
                DbType::Never.format(&FormatData::with_style(db, style))
            }
        } else {
            match type_var_matcher.func_or_callable {
                FunctionOrCallable::Function(f) => {
                    if let Some(class) = type_var_matcher.class {
                        if class.node_ref.as_link() == type_var_usage.in_definition {
                            return class
                                .generics
                                .nth(i_s, type_var_usage.index)
                                .format(&FormatData::with_style(db, style));
                        }
                        let func_class = f.class.unwrap();
                        if type_var_usage.in_definition == func_class.node_ref.as_link() {
                            let type_var_remap = func_class.type_var_remap.unwrap();
                            type_var_remap[type_var_usage.index]
                                .format(&FormatData::with_matcher_and_style(db, self, style))
                        } else {
                            type_var_usage.type_var.name(db).into()
                        }
                    } else {
                        todo!("Probably nested generic functions???")
                    }
                }
                FunctionOrCallable::Callable(c) => todo!(),
            }
        }
    }

    pub fn iter_calculated_type_vars(&mut self) -> std::slice::IterMut<CalculatedTypeVar> {
        if let Some(type_var_matcher) = self.type_var_matcher.as_mut() {
            type_var_matcher.calculated_type_vars.iter_mut()
        } else {
            unreachable!()
        }
    }

    pub fn replace_type_vars_for_nested_context(
        &self,
        i_s: &mut InferenceState,
        t: &DbType,
    ) -> DbType {
        if let Some(type_var_matcher) = self.type_var_matcher.as_ref() {
            type_var_matcher.replace_type_vars_for_nested_context(i_s, t)
        } else {
            unreachable!()
        }
    }

    pub fn set_all_contained_type_vars_to_any(&mut self, i_s: &mut InferenceState, type_: &DbType) {
        if let Some(matcher) = self.type_var_matcher.as_mut() {
            matcher.set_all_contained_type_vars_to_any(i_s, type_)
        }
    }

    pub fn has_already_matched_recursive_alias(
        &self,
        rec1: &RecursiveAlias,
        rec2: &RecursiveAlias,
    ) -> bool {
        false
    }
}
