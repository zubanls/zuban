use crate::database::{CallableContent, Database, DbType, GenericItem, TypeVarLikeUsage};
use crate::type_helpers::Class;

use super::Type;

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
