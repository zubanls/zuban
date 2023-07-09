use crate::database::{CallableContent, Database, DbType};
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
            if attribute_class.node_ref.as_link() == usage.in_definition() {
                return attribute_class
                    .generics()
                    .nth_usage(db, &usage)
                    .into_generic_item(db);
            }
            usage.into_generic_item()
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
            let in_definition = usage.in_definition();
            if let Some(defined_in) = func_class {
                if in_definition == defined_in.node_ref.as_link() {
                    return defined_in
                        .generics()
                        .nth_usage(db, &usage)
                        .into_generic_item(db);
                }
            }
            // This can happen for example if the return value is a Callable with its
            // own type vars.
            usage.into_generic_item()
        },
        &mut || instance_class.as_db_type(db),
    )
}
