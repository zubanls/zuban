use crate::arguments::Arguments;
use crate::database::Database;
use crate::value::Function;

pub struct InferenceState<'db, 'a> {
    pub database: &'db Database,
    pub current_execution: Option<(&'a Function<'db, 'a>, &'a Arguments<'db>)>,
}

impl<'db, 'a> InferenceState<'db, 'a> {
    pub fn new(database: &'db Database) -> Self {
        Self {
            database,
            current_execution: None,
        }
    }

    pub fn with_execution(&self, func: &'a Function<'db, 'a>, args: &'a Arguments<'db>) -> Self {
        Self {
            database: self.database,
            current_execution: Some((func, args)),
        }
    }
}
