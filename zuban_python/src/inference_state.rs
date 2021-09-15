use crate::database::{Database, PointLink};

pub struct InferenceState<'a> {
    pub database: &'a Database,
    execution_stack: Vec<PointLink>,
}

impl<'a> InferenceState<'a> {
    pub fn new(database: &'a Database) -> Self {
        Self {
            database,
            execution_stack: vec![],
        }
    }
}
