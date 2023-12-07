use super::Matcher;
use crate::{
    database::{Database, PointLink},
    type_::{FormatStyle, RecursiveType, TypeVarLikeUsage},
};

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum AvoidRecursionFor<'a> {
    RecursiveType(&'a RecursiveType),
    TypedDict(PointLink),
}

#[derive(Clone, Copy, Debug)]
struct DisplayedRecursive<'a> {
    current: AvoidRecursionFor<'a>,
    parent: Option<&'a DisplayedRecursive<'a>>,
}

impl DisplayedRecursive<'_> {
    fn has_already_seen_recursive_type(&self, rec: AvoidRecursionFor) -> bool {
        self.current == rec
            || self
                .parent
                .is_some_and(|d| d.has_already_seen_recursive_type(rec))
    }
}

#[derive(Clone, Copy)]
pub enum ParamsStyle {
    CallableParamsInner,
    CallableParams,
    Unreachable,
}

#[derive(Debug)]
pub struct FormatData<'db, 'a, 'b, 'c> {
    pub db: &'db Database,
    matcher: Option<&'b Matcher<'a>>,
    pub style: FormatStyle,
    pub verbose: bool,
    pub hide_implicit_literals: bool,
    displayed_recursive: Option<DisplayedRecursive<'c>>,
}

impl<'db, 'a, 'b, 'c> FormatData<'db, 'a, 'b, 'c> {
    pub fn new_short(db: &'db Database) -> Self {
        Self {
            db,
            matcher: None,
            style: FormatStyle::Short,
            verbose: false,
            hide_implicit_literals: true,
            displayed_recursive: None,
        }
    }

    pub fn with_style(db: &'db Database, style: FormatStyle) -> Self {
        Self {
            db,
            matcher: None,
            style,
            verbose: false,
            hide_implicit_literals: true,
            displayed_recursive: None,
        }
    }

    pub fn with_matcher(db: &'db Database, matcher: &'b Matcher<'a>) -> Self {
        Self {
            db,
            matcher: Some(matcher),
            style: FormatStyle::Short,
            verbose: false,
            hide_implicit_literals: true,
            displayed_recursive: None,
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
            hide_implicit_literals: true,
            displayed_recursive: None,
        }
    }

    pub fn with_seen_recursive_type<'x: 'c>(
        &'x self,
        rec: AvoidRecursionFor<'x>,
    ) -> FormatData<'db, 'a, 'b, 'x> {
        Self {
            db: self.db,
            matcher: self.matcher,
            style: self.style,
            verbose: self.verbose,
            hide_implicit_literals: self.hide_implicit_literals,
            displayed_recursive: Some(DisplayedRecursive {
                current: rec,
                parent: self.displayed_recursive.as_ref(),
            }),
        }
    }

    pub fn remove_matcher<'x: 'c>(&'x self) -> Self {
        Self {
            db: self.db,
            matcher: None,
            style: self.style,
            verbose: self.verbose,
            hide_implicit_literals: self.hide_implicit_literals,
            displayed_recursive: self.displayed_recursive,
        }
    }

    pub fn has_already_seen_recursive_type(&self, rec: AvoidRecursionFor) -> bool {
        if let Some(displayed_recursive) = &self.displayed_recursive {
            displayed_recursive.has_already_seen_recursive_type(rec)
        } else {
            false
        }
    }

    pub fn enable_verbose(&mut self) {
        self.verbose = true;
    }

    pub fn format_type_var_like(
        &self,
        type_var_usage: &TypeVarLikeUsage,
        params_style: ParamsStyle,
    ) -> Box<str> {
        if let Some(matcher) = self.matcher {
            return matcher.format(type_var_usage, self, params_style);
        }
        type_var_usage.format_without_matcher(self.db, params_style)
    }
}
