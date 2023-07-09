use crate::database::{Database, DbType};
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
