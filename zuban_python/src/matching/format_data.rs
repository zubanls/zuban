use super::Matcher;
use crate::database::{Database, FormatStyle, TypeVarUsage};

pub struct FormatData<'db, 'a, 'b> {
    pub db: &'db Database,
    matcher: Option<&'b Matcher<'a>>,
    pub style: FormatStyle,
    pub verbose: bool,
}

impl<'db, 'a, 'b> FormatData<'db, 'a, 'b> {
    pub fn new_short(db: &'db Database) -> Self {
        Self {
            db,
            matcher: None,
            style: FormatStyle::Short,
            verbose: false,
        }
    }

    pub fn with_style(db: &'db Database, style: FormatStyle) -> Self {
        Self {
            db,
            matcher: None,
            style,
            verbose: false,
        }
    }

    pub fn with_matcher(db: &'db Database, matcher: &'b Matcher<'a>) -> Self {
        Self {
            db,
            matcher: Some(matcher),
            style: FormatStyle::Short,
            verbose: false,
        }
    }

    pub fn with_matcher_and_style(
        db: &'db Database,
        matcher: &'b Matcher<'a>,
        style: FormatStyle,
    ) -> Self {
        Self {
            db,
            matcher: Some(matcher),
            style,
            verbose: false,
        }
    }

    pub fn enable_verbose(&mut self) {
        self.verbose = true;
    }

    pub fn format_type_var(&self, type_var_usage: &TypeVarUsage) -> Box<str> {
        if let Some(matcher) = self.matcher {
            if matcher.has_type_var_matcher() {
                return matcher.format_in_type_var_matcher(self.db, type_var_usage, self.style);
            }
        }
        Box::from(type_var_usage.type_var.name(self.db))
    }
}
