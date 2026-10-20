use std::borrow::Cow;

use crate::{
    arguments::Arg, format_data::find_similar_types, match_::MismatchReason, prelude::*,
    type_helpers::FuncLike,
};

type OnOverloadMismatch<'a> = Option<&'a dyn Fn()>;
type GenerateDiagnosticString<'a> = &'a dyn Fn(&dyn FuncLike, &Database) -> Option<String>;

#[derive(Clone, Copy)]
pub(crate) struct OnTypeError<'a> {
    pub callback: OnTypeErrorCallback<'a>,
    pub on_overload_mismatch: OnOverloadMismatch<'a>,
    pub generate_diagnostic_string: GenerateDiagnosticString<'a>,
}

impl<'a> OnTypeError<'a> {
    pub fn new(callback: OnTypeErrorCallback<'a>) -> Self {
        Self {
            callback,
            on_overload_mismatch: None,
            generate_diagnostic_string: &func_like_diagnostic_string,
        }
    }

    pub fn with_overload_mismatch(
        callback: OnTypeErrorCallback<'a>,
        on_overload_mismatch: OnOverloadMismatch<'a>,
    ) -> Self {
        Self {
            callback,
            on_overload_mismatch,
            generate_diagnostic_string: &func_like_diagnostic_string,
        }
    }

    pub fn with_custom_generate_diagnostic_string<'c>(
        &self,
        generate_diagnostic_string: GenerateDiagnosticString<'c>,
    ) -> OnTypeError<'c>
    where
        'a: 'c,
    {
        OnTypeError {
            generate_diagnostic_string,
            callback: self.callback,
            on_overload_mismatch: self.on_overload_mismatch,
        }
    }
}

// For whatever reason we cannot just pass FunctionOrCallable::diagnostic_string, even though it
// results in the exactly same behavior. Probably a Rust bug.
fn func_like_diagnostic_string(f: &dyn FuncLike, db: &Database) -> Option<String> {
    f.diagnostic_string(db)
}

#[derive(Debug)]
pub(crate) enum GotType<'t> {
    Type(&'t Type),
    Starred(Type),
    DoubleStarred(Type),
}

impl<'t> GotType<'t> {
    pub fn from_arg(i_s: &InferenceState, arg: &Arg, value_t: &'t Type) -> Self {
        if let Some(star_t) = arg.maybe_star_type(i_s) {
            Self::Starred(star_t)
        } else if let Some(double_star_t) = arg.maybe_star_star_type(i_s) {
            Self::DoubleStarred(double_star_t)
        } else {
            Self::Type(value_t)
        }
    }

    pub fn format(&self, format_data: &FormatData) -> String {
        match self {
            GotType::Type(t) => t.format(format_data).into(),
            GotType::Starred(t) => format!("*{}", t.format(format_data)),
            GotType::DoubleStarred(t) => format!("**{}", t.format(format_data)),
        }
    }

    fn contained_type(&self) -> &Type {
        match self {
            GotType::Type(t) => t,
            GotType::Starred(t) | GotType::DoubleStarred(t) => t,
        }
    }
}

pub(crate) struct ErrorTypes<'a> {
    pub matcher: Option<&'a Matcher<'a>>,
    pub got: GotType<'a>,
    pub expected: &'a Type,
    pub reason: &'a MismatchReason,
}

pub fn format_got_expected(db: &Database, got: &Type, expected: &Type) -> ErrorStrs {
    ErrorTypes {
        matcher: None,
        got: GotType::Type(got),
        expected,
        reason: &MismatchReason::None,
    }
    .as_boxed_strs(db)
}

pub(crate) struct ErrorStrs {
    pub got: Box<str>,
    pub expected: Box<str>,
}

impl ErrorTypes<'_> {
    pub fn as_boxed_strs(&self, db: &Database) -> ErrorStrs {
        // This is our own very limited implementation of formatting different types as small as
        // possible, but still different if they are different. e.g. a.Foo is not b.Foo and should
        // therefore not be formatted both as Foo. Mypy does a lot more here like subtype matching,
        // but for now this should suffice.
        let expected_t = self
            .matcher
            .map(|m| m.replace_type_var_likes_for_unknown_type_vars(db, self.expected))
            .unwrap_or_else(|| Cow::Borrowed(self.expected));
        let similar_types = find_similar_types(db, &[self.got.contained_type(), &expected_t]);
        let mut fmt_got = FormatData::with_types_that_need_qualified_names(db, &similar_types);
        let mut fmt_expected = if let Some(matcher) = self.matcher {
            FormatData::with_matcher(db, matcher, &similar_types)
        } else {
            fmt_got
        };
        if self.expected.is_literal_or_literal_in_tuple() {
            fmt_got.hide_implicit_literals = false;
            fmt_expected.hide_implicit_literals = false;
        }
        let mut got = self.got.format(&fmt_got);
        let mut expected = self.expected.format(&fmt_expected);
        if got.as_str() == expected.as_ref() {
            fmt_got.enable_verbose();
            fmt_expected.enable_verbose();
            got = self.got.format(&fmt_got);
            expected = self.expected.format(&fmt_expected);
        }
        ErrorStrs {
            got: got.into(),
            expected,
        }
    }

    pub(crate) fn add_mismatch_notes(&self, add_issue: impl Fn(IssueKind)) {
        match self.reason {
            MismatchReason::SequenceInsteadOfListNeeded => {
                add_issue(IssueKind::InvariantNote {
                    actual: "List",
                    maybe: "Sequence",
                });
            }
            MismatchReason::MappingInsteadOfDictNeeded => {
                add_issue(IssueKind::InvariantNote {
                    actual: "Dict",
                    maybe: "Mapping",
                });
            }
            MismatchReason::ProtocolMismatches { notes } => {
                for note in notes.iter() {
                    add_issue(IssueKind::Note(note.clone()));
                }
            }
            MismatchReason::TypedDictAgainstDictMatching { from } => {
                add_issue(IssueKind::Note(
                    format!(
                        "TypedDicts cannot be assigned to {from}, callers could \
                             delete or change keys to violate their type contract. \
                             Use Mapping[...] for read-only access or make all \
                             TypedDict keys NotRequired, with identical types, \
                             combined with a compatible `extra_items` class parameter."
                    )
                    .into(),
                ));
            }
            _ => (),
        }
    }
}

pub type OnTypeErrorCallback<'a> = &'a dyn Fn(
    &InferenceState,
    &dyn Fn(&str) -> Option<Box<str>>, // error_text; argument is a prefix
    &Arg,
    ErrorTypes,
);
pub type OnLookupError<'a> = &'a dyn Fn(&Type);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum LookupKind {
    Normal,
    // In CPython there is PyTypeObject (for documentation see CPython's `Doc/c-api/typeobj.rst`).
    // This type object is used to access __and__, when a user types `int & int`. Note that int
    // defines __and__ as well, but the type of int does not, hence it should lead to an error.
    OnlyType,
}
