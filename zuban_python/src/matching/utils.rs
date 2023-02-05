use crate::database::DbType;
use crate::inference_state::InferenceState;
use crate::value::Class;

pub fn replace_class_type_vars(i_s: &mut InferenceState, t: &DbType, class: &Class) -> DbType {
    let db = i_s.db;
    t.replace_type_var_likes_and_self(
        i_s.db,
        &mut |t| {
            if let Some(class) = i_s.current_class() {
                if class.node_ref.as_link() == t.in_definition() {
                    return class.generics().nth_usage(i_s, &t).into_generic_item(i_s);
                }
            }
            t.into_generic_item()
        },
        &mut || class.as_db_type(db),
    )
}
