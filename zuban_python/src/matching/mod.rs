mod class_like;
mod generics;
mod match_;
mod matcher;
pub mod params;
mod type_;

pub use class_like::ClassLike;
pub use generics::Generics;
pub use match_::{Match, SignatureMatch};
pub(self) use matcher::FunctionOrCallable;
pub use matcher::TypeVarMatcher;
pub use params::{matches_params, overload_has_overlapping_params};
pub use type_::Type;
