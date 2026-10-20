mod generics;

pub(crate) use crate::matcher::{
    CalculatedTypeArgs, CheckedTypeRecursion, Matcher, MatcherFormatResult, ReplaceSelfInMatcher,
    calc_callable_dunder_init_type_vars, calc_callable_type_vars, calc_class_dunder_init_type_vars,
    calc_func_type_vars, calc_untyped_func_type_vars, invalidate_matching_cache,
};
pub(crate) use generics::Generics;
