mod format_data;
mod generic;
mod generics;
mod match_;
mod matcher;
pub mod params;
mod result_context;
mod special;
mod type_;
mod utils;

pub use format_data::{FormatData, ParamsStyle};
pub use generic::Generic;
pub use generics::{Generics, GenericsIterator};
pub use match_::{ArgumentIndexWithParam, Match, MismatchReason, SignatureMatch};
pub use matcher::{
    calculate_callable_type_vars_and_return, calculate_class_init_type_vars_and_return,
    calculate_function_type_vars_and_return, create_signature_without_self,
    CalculatedTypeArguments, Matcher,
};
pub use params::{matches_params, matches_simple_params, overload_has_overlapping_params, Param};
pub use result_context::ResultContext;
pub use special::NamedTuple;
pub use type_::{common_base_type, match_tuple_type_arguments, Type};
pub use utils::replace_class_type_vars;
