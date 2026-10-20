use std::borrow::Cow;

use crate::{prelude::*, type_::ReplaceSelf};

pub fn maybe_replace_class_type_vars(
    db: &Database,
    t: &Type,
    attribute_class: &Class,
    self_instance: ReplaceSelf,
) -> Option<Type> {
    t.maybe_replace_type_var_likes_and_self(
        db,
        &mut |usage| usage.maybe_class_generic(db, attribute_class),
        self_instance,
    )
}

pub fn replace_class_type_vars<'x>(
    db: &Database,
    t: &'x Type,
    attribute_class: &Class,
    self_instance: ReplaceSelf,
) -> Cow<'x, Type> {
    maybe_replace_class_type_vars(db, t, attribute_class, self_instance)
        .map(Cow::Owned)
        .unwrap_or_else(|| Cow::Borrowed(t))
}
