use super::Matcher;
use crate::database::{Database, FormatStyle};

pub struct FormatData<'db, 'a, 'b> {
    pub db: &'db Database,
    pub matcher: &'b Matcher<'a>,
    pub style: FormatStyle,
    pub verbose: bool,
}

impl<'db, 'a, 'b> FormatData<'db, 'a, 'b> {
    pub fn new_short(db: &'db Database) -> Self {
        Self {
            db,
            matcher: &Matcher::default(),
            style: FormatStyle::Short,
            verbose: false,
        }
    }

    pub fn with_style(db: &'db Database, style: FormatStyle) -> Self {
        Self {
            db,
            matcher: &Matcher::default(),
            style,
            verbose: false,
        }
    }

    pub fn with_matcher(db: &'db Database, matcher: &'b Matcher<'a>) -> Self {
        Self {
            db,
            matcher,
            style: FormatStyle::Short,
            verbose: false,
        }
    }

    pub fn enable_verbose(&mut self) {
        self.verbose = true;
    }
}
