mod bound;
mod matcher;
mod type_var_matcher;

pub use matcher::Matcher;
pub use type_var_matcher::{
    calculate_callable_type_vars_and_return, calculate_class_init_type_vars_and_return,
    calculate_function_type_vars_and_return, CalculatedTypeArguments,
};

use super::{replace_class_type_vars, Type};
use crate::database::{DbType, TypeVarLikes};
use crate::inference_state::InferenceState;
use crate::value::{Function, Instance, Value};

pub fn create_signature_without_self(
    i_s: &mut InferenceState,
    func: Function,
    instance: Instance,
    expected_type: &Type,
) -> Option<DbType> {
    let type_vars = func.type_vars(i_s);
    let type_vars_len = type_vars.map(|t| t.len()).unwrap_or(0);
    let mut matcher = Matcher::new_reverse_function_matcher(Some(&instance.class), func, type_vars);
    let instance_t = instance.as_type(i_s);
    let match_ = matcher.match_reverse(|m| expected_type.is_super_type_of(i_s, m, &instance_t));
    if !match_.bool() {
        return None;
    }
    let mut t = func.as_db_type(i_s, true);
    if let Some(type_vars) = type_vars {
        let DbType::Callable(callable_content) = &mut t else {
            unreachable!();
        };
        let mut old_type_vars = std::mem::replace(&mut callable_content.type_vars, None)
            .unwrap()
            .into_vec();
        let calculated = matcher.unwrap_calculated_type_args();
        for (i, c) in calculated.iter().enumerate().rev() {
            if c.calculated() {
                old_type_vars.remove(i);
            }
        }
        if !old_type_vars.is_empty() {
            callable_content.type_vars = Some(TypeVarLikes::from_vec(old_type_vars));
        }
        t = t.replace_type_var_likes_and_self(
            i_s.db,
            &mut |usage| {
                let index = usage.index().as_usize();
                if usage.in_definition() == func.node_ref.as_link() {
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
            &mut || DbType::Self_,
        );
    }
    // TODO this should not be run separately, we do two replacements here.
    Some(replace_class_type_vars(i_s, &t, &instance.class))
}
