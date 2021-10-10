use crate::inference_state::InferenceState;
use crate::inferred::Inferred;

pub trait TypeVarFinder<'db, 'a> {
    fn lookup(&mut self, i_s: &mut InferenceState<'db, '_>, name: &str) -> Option<Inferred<'db>>;
}
