use crate::arguments::Arguments;
use crate::database::Database;
use crate::value::Function;

pub struct InferenceState<'db, 'b> {
    pub database: &'db Database,
    pub current_execution: Option<(&'b Function<'db, 'b>, &'b Arguments<'db>)>,
}

impl<'db, 'b> InferenceState<'db, 'b> {
    pub fn new(database: &'db Database) -> Self {
        Self {
            database,
            current_execution: None,
        }
    }

    pub fn with_execution(&self, func: &'b Function<'db, 'b>, args: &'b Arguments<'db>) -> Self {
        Self {
            database: self.database,
            current_execution: Some((func, args)),
        }
    }
}
