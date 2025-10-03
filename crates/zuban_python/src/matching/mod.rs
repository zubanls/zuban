mod generic;
mod generics;
mod match_;
mod matcher;
mod result_context;
mod utils;

use std::{borrow::Cow, cell::RefCell, collections::HashMap, sync::Arc};

pub(crate) use generic::Generic;
pub(crate) use generics::Generics;
pub(crate) use match_::{ArgumentIndexWithParam, Match, MismatchReason, SignatureMatch};
pub(crate) use matcher::{
    CalculatedTypeArgs, CheckedTypeRecursion, Matcher, MatcherFormatResult, ReplaceSelfInMatcher,
    calc_callable_dunder_init_type_vars, calc_callable_type_vars, calc_class_dunder_init_type_vars,
    calc_func_type_vars, calc_untyped_func_type_vars,
};
pub(crate) use result_context::{CouldBeALiteral, ResultContext};
pub(crate) use utils::{
    calculate_property_return, create_signature_without_self_for_callable, match_self_type,
    maybe_class_usage, maybe_replace_class_type_vars, replace_class_type_vars,
    replace_class_type_vars_in_callable,
};

use crate::{
    arguments::Arg,
    database::Database,
    debug,
    diagnostics::IssueKind,
    format_data::{FormatData, find_similar_types},
    inference_state::InferenceState,
    inferred::Inferred,
    recoverable_error,
    type_::{AnyCause, NeverCause, ReplaceTypeVarLikes, Tuple, TupleUnpack, Type, WithUnpack},
    type_helpers::FuncLike,
    utils::debug_indent,
};

thread_local! {
    static PROTOCOL_CACHE: ProtocolCache = ProtocolCache::default();
}

#[derive(Default)]
struct ProtocolCache {
    avoid_recursions: RefCell<Vec<(Type, Type)>>,
    cached: RefCell<HashMap<(Type, Type), Match>>,
}

pub fn invalidate_protocol_cache() {
    PROTOCOL_CACHE.with(|cache| {
        debug_assert!(cache.avoid_recursions.borrow().is_empty());
        cache.cached.borrow_mut().clear()
    })
}

pub fn avoid_protocol_mismatch(
    db: &Database,
    t1: &Type,
    t2: &Type,
    had_type_var_matcher: bool,
    callable: impl FnOnce() -> Match,
) -> Match {
    PROTOCOL_CACHE.with(|cache| {
        let mut current = cache.avoid_recursions.borrow_mut();
        if current.iter().any(|(x1, x2)| x1 == t1 && x2 == t2) {
            Match::new_true()
        } else {
            if !current.is_empty() {
                let mut had_temporary_matcher_id = false;
                t1.search_type_vars(&mut |usage| {
                    if usage.temporary_matcher_id() > 0 {
                        had_temporary_matcher_id = true;
                    }
                });
                if had_temporary_matcher_id {
                    let new_t1 = t1
                        .replace_type_var_likes(db, &mut |mut usage| {
                            usage.update_temporary_matcher_index(0);
                            Some(usage.into_generic_item())
                        })
                        .map(Cow::Owned)
                        .unwrap_or_else(|| Cow::Borrowed(t1));
                    // This case arose in
                    // testTwoUncomfortablyIncompatibleProtocolsWithoutRunningInIssue9771
                    // where it replace function type vars repeatedly with new generated type vars.
                    // I'm not 100% sure this holds for all cases, but it feels like this is fine.
                    drop(current);
                    return avoid_protocol_mismatch(
                        db,
                        &new_t1,
                        t2,
                        had_type_var_matcher,
                        callable,
                    );
                }
            }
            let new_t = (t1.clone(), t2.clone());
            if !had_type_var_matcher && let Some(already_known) = cache.cached.borrow().get(&new_t)
            {
                debug!(
                    r#"Used protocol cache "{}" against "{}": {:?}"#,
                    t1.format_short(db),
                    t2.format_short(db),
                    already_known,
                );
                return already_known.clone();
            }
            current.push(new_t);
            drop(current);
            debug!(
                r#"Match protocol "{}" against "{}" (TypeVarMatcher: {:?})"#,
                t1.format_short(db),
                t2.format_short(db),
                had_type_var_matcher,
            );
            let _indent = debug_indent();
            let result = callable();
            if !had_type_var_matcher {
                cache
                    .cached
                    .borrow_mut()
                    .insert((t1.clone(), t2.clone()), result.clone());
            }
            cache.avoid_recursions.borrow_mut().pop();
            result
        }
    })
}

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

#[derive(Debug, Clone)]
pub(crate) enum IteratorContent {
    Inferred(Inferred),
    // The code before makes sure that no type var tuples are passed.
    FixedLenTupleGenerics {
        entries: Arc<[Type]>,
        current_index: usize,
    },
    WithUnpack {
        unpack: WithUnpack,
        before_index: usize,
        after_index: usize,
    },
    Union(Vec<IteratorContent>),
    Any(AnyCause),
}

impl IteratorContent {
    pub fn new_tuple(entries: Arc<[Type]>) -> IteratorContent {
        Self::FixedLenTupleGenerics {
            entries,
            current_index: 0,
        }
    }

    pub fn infer_all(self, i_s: &InferenceState) -> Inferred {
        match self {
            Self::Inferred(inferred) => inferred,
            Self::FixedLenTupleGenerics {
                entries,
                current_index,
            } => Inferred::gather_simplified_union(i_s, |add| {
                for entry in entries.iter().skip(current_index) {
                    add(Inferred::from_type(entry.clone()))
                }
            }),
            Self::Union(iterators) => Inferred::gather_simplified_union(i_s, |add| {
                for iterator in iterators {
                    add(iterator.infer_all(i_s))
                }
            }),
            Self::WithUnpack {
                unpack,
                before_index,
                after_index,
            } => Inferred::gather_simplified_union(i_s, |add| match unpack.unpack {
                TupleUnpack::TypeVarTuple(_) => add(Inferred::new_object(i_s.db)),
                TupleUnpack::ArbitraryLen(t) => {
                    for entry in unpack.before.iter().skip(before_index) {
                        add(Inferred::from_type(entry.clone()))
                    }
                    add(Inferred::from_type(t));
                    for entry in unpack.before.iter().skip(after_index) {
                        add(Inferred::from_type(entry.clone()))
                    }
                }
            }),
            Self::Any(cause) => Inferred::new_any(cause),
        }
    }

    pub fn next_as_argument(&mut self, i_s: &InferenceState) -> Option<UnpackedArgument> {
        match self {
            Self::Inferred(inferred) => Some(UnpackedArgument::Normal {
                inferred: inferred.clone(),
                arbitrary_len: true,
            }),
            Self::FixedLenTupleGenerics {
                entries,
                current_index,
            } => next_fixed_length(entries, current_index).map(|inf| UnpackedArgument::Normal {
                inferred: inf,
                arbitrary_len: false,
            }),
            Self::Union(iterators) => iterators
                .iter_mut()
                .map(|i| i.next_as_argument(i_s))
                .reduce(|x, y| match (x?, y?) {
                    (
                        UnpackedArgument::Normal {
                            inferred: inf1,
                            arbitrary_len: a1,
                        },
                        UnpackedArgument::Normal {
                            inferred: inf2,
                            arbitrary_len: a2,
                        },
                    ) => Some(UnpackedArgument::Normal {
                        inferred: inf1.simplified_union(i_s, inf2),
                        arbitrary_len: a1 & a2,
                    }),
                    _ => {
                        debug!("Unpacking a union with incompatible results");
                        None
                    }
                })?,
            Self::WithUnpack {
                unpack,
                before_index,
                after_index,
            } => {
                debug_assert_eq!(*after_index, 0);
                let new_unpack = if *before_index == 0 {
                    unpack.clone()
                } else {
                    WithUnpack {
                        before: unpack.before.iter().skip(*before_index).cloned().collect(),
                        unpack: unpack.unpack.clone(),
                        after: unpack.after.clone(),
                    }
                };
                Some(UnpackedArgument::WithUnpack(new_unpack))
            }
            Self::Any(cause) => Some(UnpackedArgument::Normal {
                inferred: Inferred::new_any(*cause),
                arbitrary_len: true,
            }),
        }
    }

    pub fn unpack_starred(
        &mut self,
        i_s: &InferenceState,
        after: usize,
        tuple_target: bool,
        use_joins: bool,
    ) -> (bool, Inferred) {
        (
            false,
            match self {
                Self::Inferred(inf) => Inferred::new_list_of(i_s.db, inf.as_type(i_s)),
                Self::Any(cause) => Inferred::new_list_of(i_s.db, Type::Any(*cause)),
                Self::FixedLenTupleGenerics {
                    entries,
                    current_index,
                } => {
                    let end = entries.len() - after;
                    let fetch = end - *current_index;
                    let relevant_entries = &entries[*current_index..end];
                    let inf = if tuple_target {
                        let mut tuple_entries = vec![];
                        for t in relevant_entries {
                            tuple_entries.push(t.clone());
                        }
                        Inferred::from_type(Type::Tuple(Tuple::new_fixed_length(
                            tuple_entries.into(),
                        )))
                    } else {
                        let union = if use_joins {
                            Inferred::gather_base_types(i_s, |callable| {
                                for t in relevant_entries {
                                    callable(Inferred::from_type(t.clone()));
                                }
                            })
                        } else {
                            Inferred::gather_simplified_union(i_s, |callable| {
                                for t in relevant_entries {
                                    callable(Inferred::from_type(t.clone()));
                                }
                            })
                        };
                        let generic = union.as_type(i_s);
                        Inferred::new_list_of(i_s.db, generic)
                    };
                    *current_index += fetch;
                    if fetch == 0 {
                        return (true, inf);
                    }
                    inf
                }
                Self::WithUnpack {
                    unpack,
                    before_index,
                    after_index,
                } => {
                    let result = Inferred::new_list_of(
                        i_s.db,
                        match &unpack.unpack {
                            TupleUnpack::TypeVarTuple(_) => i_s.db.python_state.object_type(),
                            TupleUnpack::ArbitraryLen(t) => {
                                let mut result = Type::Never(NeverCause::Other);
                                for entry in unpack.before.iter().skip(*before_index) {
                                    result = result
                                        .gather_types_maybe_with_joins(i_s, &entry, use_joins);
                                }
                                result = result.gather_types_maybe_with_joins(i_s, &t, use_joins);
                                for entry in unpack.after.iter().rev().skip(after).rev() {
                                    result = result
                                        .gather_types_maybe_with_joins(i_s, &entry, use_joins);
                                }
                                result
                            }
                        },
                    );
                    // Change the indexes, to account for what has been fetched.
                    *before_index = unpack.before.len();
                    let after_len = unpack.after.len();
                    *after_index = after_len.checked_sub(after).unwrap_or(0);
                    result
                }
                Self::Union(_) => unreachable!(),
            },
        )
    }

    pub fn unpack_next(&mut self) -> Inferred {
        self.unpack_next_with_customized_after(|_| None)
    }

    pub fn unpack_next_with_customized_after(
        &mut self,
        on_after: impl FnOnce(&WithUnpack) -> Option<Type>,
    ) -> Inferred {
        // It is important to note that the lengths have been checked before and it is at this
        // point clear that we can unpack the iterator. This should only ever be used for
        // assignment calculation and assigning patterns, e.g. foo, *bar = ...
        match self {
            Self::Inferred(inf) => inf.clone(),
            Self::Any(cause) => Inferred::new_any(*cause),
            Self::FixedLenTupleGenerics {
                entries,
                current_index,
            } => next_fixed_length(entries, current_index).unwrap(),
            Self::WithUnpack {
                unpack,
                before_index,
                after_index,
            } => Inferred::from_type(if let Some(result) = unpack.before.get(*before_index) {
                *before_index += 1;
                result.clone()
            } else if let Some(custom) = on_after(unpack) {
                custom
            } else if let Some(result) = unpack.after.get(*after_index) {
                *after_index += 1;
                result.clone()
            } else {
                recoverable_error!("Next on exhausted after should never happen");
                Type::ERROR
            }),
            Self::Union(_) => unreachable!(),
        }
    }

    pub fn len_infos(&self) -> Option<TupleLenInfos> {
        match self {
            Self::Inferred(_) | Self::Any(_) => None,
            Self::FixedLenTupleGenerics {
                entries,
                current_index,
            } => Some(TupleLenInfos::FixedLen(
                entries.as_ref().len() - current_index,
            )),
            Self::Union(_) => unreachable!(),
            Self::WithUnpack { unpack, .. } => Some(TupleLenInfos::WithStar {
                before: unpack.before.len(),
                after: unpack.after.len(),
            }),
        }
    }
}

pub(crate) enum UnpackedArgument {
    Normal {
        inferred: Inferred,
        arbitrary_len: bool,
    },
    WithUnpack(WithUnpack),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum LookupKind {
    Normal,
    // In CPython there is PyTypeObject (for documentation see CPython's `Doc/c-api/typeobj.rst`).
    // This type object is used to access __and__, when a user types `int & int`. Note that int
    // defines __and__ as well, but the type of int does not, hence it should lead to an error.
    OnlyType,
}

#[derive(Copy, Clone)]
pub(crate) enum TupleLenInfos {
    FixedLen(usize),
    WithStar { before: usize, after: usize },
}

fn next_fixed_length(entries: &[Type], current_index: &mut usize) -> Option<Inferred> {
    let result = entries.get(*current_index)?;
    *current_index += 1;
    Some(Inferred::from_type(result.clone()))
}
