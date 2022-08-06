mod class_like;
mod generics;
mod match_;
mod matcher;
pub mod params;
mod result_context;
mod type_;

pub use class_like::ClassLike;
pub use generics::Generics;
pub use match_::{Match, MismatchReason, SignatureMatch};
pub use matcher::{
    calculate_callable_type_vars_and_return, calculate_function_type_vars_and_return,
    TypeVarMatcher,
};
pub use params::{matches_params, overload_has_overlapping_params};
pub use result_context::ResultContext;
pub use type_::Type;
