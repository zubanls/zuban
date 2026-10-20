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
        &mut |usage| maybe_class_usage(db, attribute_class, &usage),
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

pub fn replace_class_type_vars_in_callable(
    db: &Database,
    callable: &CallableContent,
    func_class: Option<&Class>,
    as_self_instance: ReplaceSelf,
) -> Option<CallableContent> {
    callable.replace_type_var_likes_and_self(
        db,
        &mut |usage| func_class.and_then(|c| maybe_class_usage(db, c, &usage)),
        as_self_instance,
    )
}

pub fn maybe_class_usage(
    db: &Database,
    attribute_class: &Class,
    usage: &TypeVarLikeUsage,
) -> Option<Generic> {
    (attribute_class.node_ref.as_link() == usage.in_definition())
        .then(|| attribute_class.generics().nth_usage(db, usage).into_owned())
}
