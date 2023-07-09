use std::rc::Rc;

use crate::database::{
    CallableContent, Database, DbType, GenericItem, TypeVarLikeUsage, TypeVarLikes,
};
use crate::inference_state::InferenceState;
use crate::type_helpers::{Class, Instance};

use super::{Matcher, Type};

pub fn replace_class_type_vars(
    db: &Database,
    t: &DbType,
    instance_class: &Class,
    attribute_class: &Class,
) -> DbType {
    Type::new(t).replace_type_var_likes_and_self(
        db,
        &mut |usage| {
            maybe_class_usage(db, attribute_class, &usage)
                .unwrap_or_else(|| usage.into_generic_item())
        },
        &mut || instance_class.as_db_type(db),
    )
}

pub fn replace_class_type_vars_in_callable(
    db: &Database,
    callable: &CallableContent,
    instance_class: &Class,
    func_class: Option<&Class>,
) -> CallableContent {
    Type::replace_type_var_likes_and_self_for_callable(
        &callable,
        db,
        &mut |usage| {
            func_class
                .and_then(|c| maybe_class_usage(db, c, &usage))
                .unwrap_or_else(|| usage.into_generic_item())
        },
        &mut || instance_class.as_db_type(db),
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
            .nth_usage(db, &usage)
            .into_generic_item(db)
    })
}

pub fn create_signature_without_self(
    i_s: &InferenceState,
    callable: &CallableContent,
    instance: &Instance,
    func_class: &Class,
    expected_type: &Type,
) -> Option<DbType> {
    let type_vars = &callable.type_vars;
    let mut matcher = Matcher::new_callable_matcher(callable);
    let expected = replace_class_type_vars(i_s.db, expected_type.as_ref(), func_class, func_class);
    if !Type::owned(expected)
        .is_super_type_of(
            i_s,
            &mut matcher,
            &Type::owned(instance.class.as_db_type(i_s.db)),
        )
        .bool()
    {
        return None;
    }
    let Some(mut callable) = callable.remove_first_param() else {
        unreachable!()
    };
    if let Some(type_vars) = type_vars {
        let mut old_type_vars = callable.type_vars.take().unwrap().into_vec();
        let calculated = matcher.unwrap_calculated_type_args();
        for (i, c) in calculated.iter().enumerate().rev() {
            if c.calculated() {
                old_type_vars.remove(i);
            }
        }
        if !old_type_vars.is_empty() {
            callable.type_vars = Some(TypeVarLikes::from_vec(old_type_vars));
        }
        let new = Type::replace_type_var_likes_and_self_for_callable(
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
                if let Some(g) = maybe_class_usage(i_s.db, func_class, &usage) {
                    return g;
                }
                let new_index = calculated
                    .iter()
                    .take(index)
                    .filter(|c| !c.calculated())
                    .count();
                usage.into_generic_item_with_new_index(new_index.into())
            },
            &mut || todo!(), //instance.class.as_db_type(i_s.db),
        );
        Some(DbType::Callable(Rc::new(new)))
    } else {
        // TODO this should not be run separately, we do two replacements here.
        Some(replace_class_type_vars(
            i_s.db,
            &DbType::Callable(Rc::new(callable)),
            &instance.class,
            func_class,
        ))
    }
}
