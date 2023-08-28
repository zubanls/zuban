use std::rc::Rc;

use crate::{
    arguments::Arguments,
    database::{Dataclass, DbType},
    inference_state::InferenceState,
    inferred::Inferred,
    matching::{OnTypeError, ResultContext},
};

pub fn execute_dataclass<'db>(
    i_s: &InferenceState<'db, '_>,
    args: &dyn Arguments<'db>,
    on_type_error: OnTypeError,
) -> Inferred {
    let mut iterator = args.iter();
    let first = iterator.next();
    if let Some(x) = iterator.next() {
        todo!()
    } else if let Some(first) = first {
        if let Some(cls) = first
            .infer(i_s, &mut ResultContext::Unknown)
            .as_type(i_s)
            .maybe_type_of_class(i_s.db)
        {
            Inferred::from_type(DbType::Type(Rc::new(DbType::Dataclass(Rc::new(
                Dataclass {
                    class: cls.node_ref.as_link(),
                    options: Default::default(),
                    // TODO this is quite obviously wrong.
                    __init__: i_s.db.python_state.any_callable.as_ref().clone(),
                },
            )))))
        } else {
            todo!()
        }
    } else {
        todo!()
    }
}
