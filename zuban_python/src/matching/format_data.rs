use super::TypeVarMatcher;
use crate::database::{Database, FormatStyle};

pub struct FormatData<'db, 'a, 'b> {
    pub db: &'db Database,
    pub matcher: Option<&'b TypeVarMatcher<'db, 'a>>,
    pub style: FormatStyle,
}

impl<'db, 'a, 'b> FormatData<'db, 'a, 'b> {
    pub fn new_short(db: &'db Database) -> Self {
        Self {
            db,
            matcher: None,
            style: FormatStyle::Short,
        }
    }

    pub fn with_style(db: &'db Database, style: FormatStyle) -> Self {
        Self {
            db,
            matcher: None,
            style,
        }
    }

    pub fn with_matcher(db: &'db Database, matcher: Option<&'b TypeVarMatcher<'db, 'a>>) -> Self {
        Self {
            db,
            matcher,
            style: FormatStyle::Short,
        }
    }
}
