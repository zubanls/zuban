use crate::database::DbType;
use crate::inference_state::InferenceState;
use crate::type_helpers::Class;

use super::Type;

pub fn replace_class_type_vars(i_s: &InferenceState, t: &DbType, class: &Class) -> DbType {
    let db = i_s.db;
    Type::new(t).replace_type_var_likes_and_self(
        db,
        &mut |usage| {
            if let Some(class) = i_s.current_class() {
                if class.node_ref.as_link() == usage.in_definition() {
                    return class.generics().nth_usage(db, &usage).into_generic_item(db);
                }
            }
            usage.into_generic_item()
        },
        &mut || class.as_db_type(db),
    )
}
