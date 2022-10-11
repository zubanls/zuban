use super::type_var_matcher::{CalculatedTypeVar, FunctionOrCallable, TypeVarMatcher};
use super::{Match, Type};

use crate::database::{
    CallableContent, Database, DbType, FormatStyle, TypeVarUsage, TypeVars, Variance,
};
use crate::inference_state::InferenceState;
use crate::value::Function;

#[derive(Default)]
pub struct Matcher<'a> {
    type_var_matcher: Option<TypeVarMatcher<'a>>,
}

impl<'a> Matcher<'a> {
    pub fn new(type_var_matcher: Option<TypeVarMatcher<'a>>) -> Self {
        Self { type_var_matcher }
    }

    pub fn new_reverse_callable_matcher(
        callable: &'a CallableContent,
        calculated_type_vars: &'a mut [CalculatedTypeVar],
    ) -> Self {
        let m = TypeVarMatcher::new(
            None,
            FunctionOrCallable::Callable(callable),
            callable.defined_at,
            calculated_type_vars,
        );
        m.match_reverse = true;
        Self {
            type_var_matcher: Some(m),
        }
    }

    pub fn new_reverse_function_matcher(
        function: Function<'a>,
        type_vars: Option<&TypeVars>,
        calculated_type_vars: &'a mut Vec<CalculatedTypeVar>,
    ) -> Self {
        if let Some(type_vars) = type_vars {
            calculated_type_vars.resize_with(type_vars.len(), Default::default);
            let m = TypeVarMatcher::new(
                None,
                FunctionOrCallable::Function(function),
                function.node_ref.as_link(),
                calculated_type_vars,
            );
            m.match_reverse = true;
            Self {
                type_var_matcher: Some(m),
            }
        } else {
            Matcher::default()
        }
    }

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
            Some(matcher) => matcher.match_or_add_type_var(i_s, t1, value_type, variance),
            None => match value_type.maybe_db_type() {
                Some(DbType::TypeVar(t2)) => {
                    (t1.index == t2.index && t1.in_definition == t2.in_definition).into()
                }
                _ => Match::new_false(),
            },
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
        if let Some(type_var_matcher) = self.type_var_matcher.as_mut() {
            type_var_matcher.replace_type_vars_for_nested_context(i_s, t)
        } else {
            unreachable!()
        }
    }

    pub fn set_all_contained_type_vars_to_any(&mut self, i_s: &mut InferenceState, type_: &DbType) {
        if let Some(matcher) = self.type_var_matcher {
            matcher.set_all_contained_type_vars_to_any(i_s, type_)
        }
    }

    pub fn format(
        &self,
        db: &Database,
        type_var_usage: &TypeVarUsage,
        style: FormatStyle,
    ) -> Box<str> {
        if let Some(matcher) = self.type_var_matcher {
            return matcher.format(db, type_var_usage, style);
        } else {
            Box::from(type_var_usage.type_var.name(db))
        }
    }
}
