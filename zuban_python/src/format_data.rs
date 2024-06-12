use crate::{
    database::{Database, PointLink},
    matching::{Matcher, MatcherFormatResult},
    type_::{
        FormatStyle, ParamSpecUsage, RecursiveType, TypeVarLikeUsage, TypeVarTupleUsage,
        TypeVarUsage,
    },
    utils::AlreadySeen,
};

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum AvoidRecursionFor<'a> {
    RecursiveType(&'a RecursiveType),
    TypedDict(PointLink),
    NamedTuple(PointLink),
}

type DisplayedRecursive<'a> = AlreadySeen<'a, AvoidRecursionFor<'a>>;

#[derive(Clone, Copy)]
pub enum ParamsStyle {
    CallableParamsInner,
    CallableParams,
    Unreachable,
}

#[derive(Debug)]
pub struct FormatData<'db, 'a, 'b, 'c> {
    pub db: &'db Database,
    pub matcher: Option<&'b Matcher<'a>>,
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
    ) -> Result<FormatData<'db, 'a, 'b, 'x>, ()> {
        let displayed_recursive = DisplayedRecursive {
            current: rec,
            previous: self.displayed_recursive.as_ref(),
        };
        if displayed_recursive.is_cycle() {
            Err(())
        } else {
            Ok(Self {
                db: self.db,
                matcher: self.matcher,
                style: self.style,
                verbose: self.verbose,
                hide_implicit_literals: self.hide_implicit_literals,
                displayed_recursive: Some(displayed_recursive),
            })
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

    pub fn enable_verbose(&mut self) {
        self.verbose = true;
    }

    pub fn format_type_var(&self, usage: &TypeVarUsage) -> Box<str> {
        match self.format_internal(
            &TypeVarLikeUsage::TypeVar(usage.clone()),
            ParamsStyle::Unreachable,
        ) {
            MatcherFormatResult::Str(s) => s,
            MatcherFormatResult::TypeVarTupleUnknown => unreachable!(),
        }
    }

    pub fn format_type_var_tuple(&self, usage: &TypeVarTupleUsage) -> Option<Box<str>> {
        match self.format_internal(
            &TypeVarLikeUsage::TypeVarTuple(usage.clone()),
            ParamsStyle::Unreachable,
        ) {
            MatcherFormatResult::Str(s) => Some(s),
            MatcherFormatResult::TypeVarTupleUnknown => None,
        }
    }

    pub fn format_param_spec(&self, usage: &ParamSpecUsage, style: ParamsStyle) -> Box<str> {
        match self.format_internal(&TypeVarLikeUsage::ParamSpec(usage.clone()), style) {
            MatcherFormatResult::Str(s) => s,
            MatcherFormatResult::TypeVarTupleUnknown => unreachable!(),
        }
    }

    fn format_internal(
        &self,
        type_var_usage: &TypeVarLikeUsage,
        params_style: ParamsStyle,
    ) -> MatcherFormatResult {
        if let Some(matcher) = self.matcher {
            return matcher.format(type_var_usage, self, params_style);
        }
        MatcherFormatResult::Str(type_var_usage.format_without_matcher(self.db, params_style))
    }
}
