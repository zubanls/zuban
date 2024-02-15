mod format_data;
mod generic;
mod generics;
mod lookup_result;
mod match_;
mod matcher;
pub mod params;
mod result_context;
mod utils;

use std::{cell::RefCell, rc::Rc};

pub use format_data::{AvoidRecursionFor, FormatData, ParamsStyle};
pub use generic::Generic;
pub use generics::{Generics, GenericsIterator};
pub use lookup_result::LookupResult;
pub use match_::{ArgumentIndexWithParam, Match, MismatchReason, SignatureMatch};
pub(crate) use matcher::{
    calculate_callable_init_type_vars_and_return, calculate_callable_type_vars_and_return,
    calculate_class_init_type_vars_and_return, calculate_function_type_vars_and_return,
    CalculatedTypeArgs, FunctionOrCallable, Matcher, MatcherFormatResult,
};
pub use params::{matches_params, matches_simple_params, Param};
pub use result_context::{CouldBeALiteral, ResultContext};
pub use utils::{
    calculate_property_return, create_signature_without_self_for_callable, match_self_type,
    maybe_class_usage, replace_class_type_vars, replace_class_type_vars_in_callable,
};

use crate::{
    arguments::Arg,
    database::Database,
    diagnostics::IssueType,
    inference_state::InferenceState,
    inferred::Inferred,
    type_::{AnyCause, Tuple, TupleUnpack, Type, WithUnpack},
    utils::debug_indent,
};

thread_local! {
    static PROTOCOL_RECURSION_AVOIDANCE: RefCell<Vec<(Type, Type)>> = const { RefCell::new(vec![]) };
}

pub fn avoid_protocol_mismatch(t1: &Type, t2: &Type, callable: impl FnOnce() -> Match) -> Match {
    PROTOCOL_RECURSION_AVOIDANCE.with(|vec| {
        let mut current = vec.borrow_mut();
        if current.iter().any(|(x1, x2)| x1 == t1 && x2 == t2) {
            Match::new_true()
        } else {
            current.push((t1.clone(), t2.clone()));
            drop(current);
            let result = debug_indent(|| callable());
            vec.borrow_mut().pop();
            result
        }
    })
}

type OnOverloadMismatch<'db, 'a> = Option<&'a dyn Fn()>;
type GenerateDiagnosticString<'a> = &'a dyn Fn(&FunctionOrCallable, &Database) -> Option<String>;

#[derive(Clone, Copy)]
pub struct OnTypeError<'db, 'a> {
    pub callback: OnTypeErrorCallback<'db, 'a>,
    pub on_overload_mismatch: OnOverloadMismatch<'db, 'a>,
    pub generate_diagnostic_string: GenerateDiagnosticString<'a>,
}

impl<'db, 'a> OnTypeError<'db, 'a> {
    pub fn new(callback: OnTypeErrorCallback<'db, 'a>) -> Self {
        Self {
            callback,
            on_overload_mismatch: None,
            generate_diagnostic_string: &func_or_callable_diagnostic_string,
        }
    }

    pub fn with_overload_mismatch(
        callback: OnTypeErrorCallback<'db, 'a>,
        on_overload_mismatch: OnOverloadMismatch<'db, 'a>,
    ) -> Self {
        Self {
            callback,
            on_overload_mismatch,
            generate_diagnostic_string: &func_or_callable_diagnostic_string,
        }
    }

    pub fn with_custom_generate_diagnostic_string<'c>(
        &self,
        generate_diagnostic_string: GenerateDiagnosticString<'c>,
    ) -> OnTypeError<'db, 'c>
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
fn func_or_callable_diagnostic_string(f: &FunctionOrCallable, db: &Database) -> Option<String> {
    f.diagnostic_string(db)
}

pub enum GotType<'a> {
    Type(&'a Type),
    Starred(Type),
    DoubleStarred(Type),
}

impl GotType<'_> {
    pub fn as_string(&self, db: &Database) -> String {
        self.format(&FormatData::new_short(db))
    }

    pub fn format(&self, format_data: &FormatData) -> String {
        match self {
            GotType::Type(t) => t.format(format_data).into(),
            GotType::Starred(t) => format!("*{}", t.format(format_data)),
            GotType::DoubleStarred(t) => format!("**{}", t.format(format_data)),
        }
    }
}

pub struct ErrorTypes<'a> {
    pub matcher: &'a Matcher<'a>,
    pub got: GotType<'a>,
    pub expected: &'a Type,
    pub reason: &'a MismatchReason,
}

pub struct ErrorStrs {
    pub got: Box<str>,
    pub expected: Box<str>,
}

impl ErrorTypes<'_> {
    pub fn as_boxed_strs(&self, i_s: &InferenceState) -> ErrorStrs {
        let mut fmt_got = FormatData::new_short(i_s.db);
        let mut fmt_expected = FormatData::with_matcher(i_s.db, self.matcher);
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

    pub(crate) fn add_mismatch_notes(&self, add_issue: impl Fn(IssueType)) {
        match self.reason {
            MismatchReason::SequenceInsteadOfListNeeded => {
                add_issue(IssueType::InvariantNote {
                    actual: "List",
                    maybe: "Sequence",
                });
            }
            MismatchReason::MappingInsteadOfDictNeeded => {
                add_issue(IssueType::InvariantNote {
                    actual: "Dict",
                    maybe: "Mapping",
                });
            }
            MismatchReason::ProtocolMismatches { notes } => {
                for note in notes.iter() {
                    add_issue(IssueType::Note(note.clone()));
                }
            }
            _ => (),
        }
    }
}

pub type OnTypeErrorCallback<'db, 'a> = &'a dyn Fn(
    &InferenceState<'db, '_>,
    &dyn Fn(&str) -> Option<Box<str>>, // error_text; argument is a prefix
    &Arg,
    ErrorTypes,
);
pub type OnLookupError<'a> = &'a dyn Fn(&Type);

#[derive(Debug, Clone)]
pub enum IteratorContent {
    Inferred(Inferred),
    // The code before makes sure that no type var tuples are passed.
    FixedLenTupleGenerics {
        entries: Rc<[Type]>,
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
    pub fn new_tuple(entries: Rc<[Type]>) -> IteratorContent {
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
            } => Inferred::gather_base_types(i_s, |add| match unpack.unpack {
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
            Self::Union(iterators) => todo!(),
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
                        let union = Inferred::gather_base_types(i_s, |callable| {
                            for t in relevant_entries {
                                callable(Inferred::from_type(t.clone()));
                            }
                        });
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
                                let inner = Inferred::gather_base_types(i_s, |add| {
                                    for entry in unpack.before.iter().skip(*before_index) {
                                        add(Inferred::from_type(entry.clone()));
                                    }
                                    add(Inferred::from_type(t.clone()));
                                    for entry in unpack.after.iter().rev().skip(after).rev() {
                                        add(Inferred::from_type(entry.clone()));
                                    }
                                });
                                inner.as_type(i_s)
                            }
                        },
                    );
                    // Change the indexes, to account for what has been fetched.
                    *before_index = unpack.before.len();
                    *after_index = unpack.after.len() - after;
                    result
                }
                Self::Union(_) => unreachable!(),
            },
        )
    }

    pub fn unpack_next(&mut self) -> Inferred {
        // It is important to note that the lengths have been checked before and it is at this
        // point clear that we can unpack the iterator. This should only ever be used for
        // assignment calculation, e.g. foo, *bar = ...
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
            } => {
                if *before_index == unpack.before.len() {
                    let result = unpack.after.get(*after_index).unwrap();
                    *after_index += 1;
                    Inferred::from_type(result.clone())
                } else {
                    let result = unpack.before.get(*before_index).unwrap();
                    *before_index += 1;
                    Inferred::from_type(result.clone())
                }
            }
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
            Self::Union(iterators) => unreachable!(),
            Self::WithUnpack { unpack, .. } => Some(TupleLenInfos::WithStar {
                before: unpack.before.len(),
                after: unpack.after.len(),
            }),
        }
    }
}

pub enum UnpackedArgument {
    Normal {
        inferred: Inferred,
        arbitrary_len: bool,
    },
    WithUnpack(WithUnpack),
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum LookupKind {
    Normal,
    // In CPython there is PyTypeObject (for documentation see CPython's `Doc/c-api/typeobj.rst`).
    // This type object is used to access __and__, when a user types `int & int`. Note that int
    // defines __and__ as well, but the type of int does not, hence it should lead to an error.
    OnlyType,
}

#[derive(Copy, Clone)]
pub enum TupleLenInfos {
    FixedLen(usize),
    WithStar { before: usize, after: usize },
}

fn next_fixed_length(entries: &[Type], current_index: &mut usize) -> Option<Inferred> {
    let result = entries.get(*current_index)?;
    *current_index += 1;
    Some(Inferred::from_type(result.clone()))
}
