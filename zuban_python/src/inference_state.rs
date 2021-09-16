use crate::arguments::Arguments;
use crate::database::Database;
use crate::value::Function;

pub struct InferenceState<'a, 'b> {
    pub database: &'a Database,
    pub current_execution: Option<(&'b Function<'a, 'b>, &'b Arguments<'a>)>,
}

impl<'a, 'b> InferenceState<'a, 'b> {
    pub fn new(database: &'a Database) -> Self {
        Self {
            database,
            current_execution: None,
        }
    }

    pub fn with_execution(&self, func: &'b Function<'a, 'b>, args: &'b Arguments<'a>) -> Self {
        Self {
            database: self.database,
            current_execution: Some((func, args)),
        }
    }
}
