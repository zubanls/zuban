mod format_data;
mod generics;
mod match_;
mod matcher;
pub mod params;
mod result_context;
mod type_;
mod type_var_matcher;

pub use format_data::FormatData;
pub use generics::Generics;
pub use match_::{ArgumentIndexWithParam, Match, MismatchReason, SignatureMatch};
pub use matcher::Matcher;
pub use params::{matches_params, overload_has_overlapping_params};
pub use result_context::ResultContext;
pub use type_::Type;
pub use type_var_matcher::{
    calculate_callable_type_vars_and_return, calculate_class_init_type_vars_and_return,
    calculate_function_type_vars_and_return, CalculatedTypeArguments,
};
