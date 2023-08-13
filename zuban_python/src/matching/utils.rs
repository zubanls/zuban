use crate::database::{
    CallableContent, Database, DbType, GenericItem, TypeVarLikeUsage, TypeVarLikes,
};
use crate::inference_state::InferenceState;
use crate::type_helpers::Class;

use super::type_::ReplaceSelf;
use super::{Matcher, Type};

pub fn replace_class_type_vars(
    db: &Database,
    t: &DbType,
    attribute_class: &Class,
    self_instance: ReplaceSelf,
) -> DbType {
    Type::new(t).replace_type_var_likes_and_self(
        db,
        &mut |usage| {
            maybe_class_usage(db, attribute_class, &usage)
                .unwrap_or_else(|| usage.into_generic_item())
        },
        self_instance,
    )
}

pub fn replace_class_type_vars_in_callable(
    db: &Database,
    callable: &CallableContent,
    func_class: Option<&Class>,
    as_self_instance: ReplaceSelf,
) -> CallableContent {
    Type::replace_type_var_likes_and_self_for_callable(
        callable,
        db,
        &mut |usage| {
            func_class
                .and_then(|c| maybe_class_usage(db, c, &usage))
                .unwrap_or_else(|| usage.into_generic_item())
        },
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
    instance: &DbType,
    func_class: &Class,
    first_type: &DbType,
) -> Option<CallableContent> {
    let matcher = Matcher::new_callable_matcher(callable);
    create_signature_without_self(
        i_s,
        matcher,
        || {
            let c = callable
                .remove_first_param()
                .expect("Signatures without any params should have been filtered before");
            replace_class_type_vars_in_callable(i_s.db, &c, Some(func_class), &|| instance.clone())
        },
        instance,
        func_class,
        first_type,
    )
}

fn match_self_type(
    i_s: &InferenceState,
    matcher: &mut Matcher,
    instance: &DbType,
    func_class: &Class,
    first_type: &DbType,
) -> Option<()> {
    let expected = replace_class_type_vars(i_s.db, first_type, func_class, &|| {
        func_class.as_db_type(i_s.db)
    });
    if !Type::owned(expected)
        .is_super_type_of(i_s, matcher, &Type::new(instance))
        .bool()
    {
        return None;
    }
    Some(())
}

pub fn create_signature_without_self(
    i_s: &InferenceState,
    mut matcher: Matcher,
    get_callable: impl FnOnce() -> CallableContent,
    instance: &DbType,
    func_class: &Class,
    first_type: &DbType,
) -> Option<CallableContent> {
    match_self_type(i_s, &mut matcher, instance, func_class, first_type)?;
    let mut callable = get_callable();
    if let Some(type_vars) = &callable.type_vars {
        let calculated = matcher.unwrap_calculated_type_args();
        callable = Type::replace_type_var_likes_and_self_for_callable(
            &callable,
            i_s.db,
            &mut |usage| {
                let index = usage.index().as_usize();
                if usage.in_definition() == callable.defined_at {
                    let c = &calculated[index];
                    if c.calculated() {
                        return (*c).clone().into_generic_item(i_s.db, &type_vars[index]);
                    }
                }
                let new_index = calculated
                    .iter()
                    .take(index)
                    .filter(|c| !c.calculated())
                    .count();
                usage.into_generic_item_with_new_index(new_index.into())
            },
            &|| unreachable!("Self should have been remapped already"),
        );
        let mut old_type_vars = callable.type_vars.take().unwrap().as_vec();
        for (i, c) in calculated.iter().enumerate().rev() {
            if c.calculated() {
                old_type_vars.remove(i);
            }
        }
        if !old_type_vars.is_empty() {
            callable.type_vars = Some(TypeVarLikes::from_vec(old_type_vars));
        }
    }
    Some(callable)
}

pub fn calculate_property_return(
    i_s: &InferenceState,
    instance: &DbType,
    func_class: &Class,
    callable: &CallableContent,
) -> Option<DbType> {
    let first_type = callable.first_positional_type().unwrap();
    let mut matcher = Matcher::new_callable_matcher(callable);
    match_self_type(i_s, &mut matcher, instance, func_class, first_type)?;

    let t = replace_class_type_vars(i_s.db, &callable.result_type, &func_class, &|| {
        instance.clone()
    });

    if let Some(type_vars) = &callable.type_vars {
        let calculated = matcher.unwrap_calculated_type_args();
        Some(Type::owned(t).replace_type_var_likes(i_s.db, &mut |usage| {
            let index = usage.index().as_usize();
            if usage.in_definition() == callable.defined_at {
                let c = &calculated[index];
                if c.calculated() {
                    return (*c).clone().into_generic_item(i_s.db, &type_vars[index]);
                }
            }
            usage.into_generic_item()
        }))
    } else {
        Some(t)
    }
}
