use std::borrow::Cow;

use super::Matcher;
use crate::{
    database::Database,
    debug,
    format_data::FormatData,
    inference_state::InferenceState,
    type_::{CallableContent, GenericItem, ReplaceSelf, Type, TypeVarLikeUsage},
    type_helpers::Class,
};

pub fn replace_class_type_vars<'x>(
    db: &Database,
    t: &'x Type,
    attribute_class: &Class,
    self_instance: ReplaceSelf,
) -> Cow<'x, Type> {
    t.replace_type_var_likes_and_self(
        db,
        &mut |usage| maybe_class_usage(db, attribute_class, &usage),
        self_instance,
    )
    .map(Cow::Owned)
    .unwrap_or_else(|| Cow::Borrowed(t))
}

pub fn replace_class_type_vars_in_callable(
    db: &Database,
    callable: &CallableContent,
    func_class: Option<&Class>,
    as_self_instance: ReplaceSelf,
) -> CallableContent {
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
) -> Option<GenericItem> {
    (attribute_class.node_ref.as_link() == usage.in_definition()).then(|| {
        attribute_class
            .generics()
            .nth_usage(db, usage)
            .into_generic_item(db)
    })
}

pub fn create_signature_without_self_for_callable(
    i_s: &InferenceState,
    callable: &CallableContent,
    instance: &Type,
    func_class: &Class,
    first_type: &Type,
) -> Option<CallableContent> {
    let mut matcher = Matcher::new_callable_matcher(callable);
    if !match_self_type(i_s, &mut matcher, instance, func_class, first_type) {
        debug!(
            "Couldn't create signature without self for callable {} with instance {}",
            callable.format(&FormatData::new_short(i_s.db)),
            instance.format_short(i_s.db)
        );
        return None;
    }
    let c = callable
        .remove_first_positional_param()
        .expect("Signatures without any params should have been filtered before");
    let c = replace_class_type_vars_in_callable(i_s.db, &c, Some(func_class), &|| {
        Some(instance.clone())
    });
    Some(matcher.remove_self_from_callable(i_s, c))
}

pub fn match_self_type(
    i_s: &InferenceState,
    matcher: &mut Matcher,
    instance: &Type,
    func_class: &Class,
    first_type: &Type,
) -> bool {
    let expected =
        replace_class_type_vars(i_s.db, first_type, func_class, &|| Some(instance.clone()));
    expected.is_super_type_of(i_s, matcher, instance).bool()
}

pub fn calculate_property_return(
    i_s: &InferenceState,
    instance: &Type,
    func_class: &Class,
    callable: &CallableContent,
) -> Option<Type> {
    let first_type = callable.first_positional_type().unwrap();
    let mut matcher = Matcher::new_callable_matcher(callable);
    if callable.kind.had_first_self_or_class_annotation()
        && !match_self_type(i_s, &mut matcher, instance, func_class, &first_type)
    {
        return None;
    }

    let t = replace_class_type_vars(i_s.db, &callable.return_type, func_class, &|| {
        Some(instance.clone())
    });

    Some(if callable.type_vars.is_empty() {
        t.into_owned()
    } else {
        matcher
            .replace_type_var_likes_for_unknown_type_vars(i_s.db, &t)
            .into_owned()
    })
}
