use std::rc::Rc;

use super::{Callable, Class};
use crate::{
    arguments::{Arg, ArgIterator, ArgKind, Args, InferredArg},
    database::Database,
    debug,
    diagnostics::IssueKind,
    file::FLOW_ANALYSIS,
    format_data::FormatData,
    inference_state::InferenceState,
    inferred::Inferred,
    matching::{
        calculate_callable_dunder_init_type_vars_and_return,
        calculate_callable_type_vars_and_return, replace_class_type_vars_in_callable,
        ArgumentIndexWithParam, CalculatedTypeArgs, FunctionOrCallable, Generics, OnTypeError,
        ResultContext, SignatureMatch,
    },
    type_::{AnyCause, FunctionOverload, NeverCause, ReplaceSelf, Type},
    utils::debug_indent,
};

#[derive(Debug)]
pub struct OverloadedFunction<'a> {
    overload: &'a Rc<FunctionOverload>,
    class: Option<Class<'a>>,
}

pub enum OverloadResult<'a> {
    Single(Callable<'a>),
    Union(Type),
    NotFound,
}

#[derive(Debug)]
pub enum UnionMathResult {
    FirstSimilarIndex(usize),
    Match {
        first_similar_index: usize,
        result: Type,
    },
    NoMatch,
}

impl<'db: 'a, 'a> OverloadedFunction<'a> {
    pub fn new(overload: &'a Rc<FunctionOverload>, class: Option<Class<'a>>) -> Self {
        Self { overload, class }
    }

    pub(super) fn find_matching_function(
        &self,
        i_s: &InferenceState<'db, '_>,
        args: &dyn Args<'db>,
        skip_first_argument: bool,
        class: Option<&Class>,
        search_init: bool, // TODO this feels weird, maybe use a callback?
        result_context: &mut ResultContext,
        on_type_error: OnTypeError,
        as_union_math_type: &impl Fn(&Callable, CalculatedTypeArgs) -> Type,
    ) -> OverloadResult<'a> {
        let match_signature = |i_s: &InferenceState<'db, '_>,
                               result_context: &mut ResultContext,
                               callable: Callable| {
            if search_init {
                calculate_callable_dunder_init_type_vars_and_return(
                    i_s,
                    class.unwrap(),
                    callable,
                    args.iter(i_s.mode),
                    |issue| args.add_issue(i_s, issue),
                    true,
                    result_context,
                    None,
                )
            } else {
                calculate_callable_type_vars_and_return(
                    i_s,
                    callable,
                    args.iter(i_s.mode),
                    |issue| args.add_issue(i_s, issue),
                    skip_first_argument,
                    result_context,
                    None,
                )
            }
        };
        let mut first_arbitrary_length_not_handled = None;
        let mut first_similar = None;
        let mut multi_any_match: Option<(_, Box<_>)> = None;
        let mut had_error_in_func = None;
        let points_backup = args.points_backup();
        for (i, callable) in self.overload.iter_functions().enumerate() {
            debug!("Checking overload item #{i}");
            let callable = Callable::new(callable, self.class);
            let (calculated_type_args, had_error) =
                i_s.avoid_errors_within(|i_s| match_signature(i_s, result_context, callable));
            if had_error && had_error_in_func.is_none() {
                had_error_in_func = Some(callable);
            }
            match calculated_type_args.matches {
                SignatureMatch::True {
                    arbitrary_length_handled,
                } if !had_error => {
                    if multi_any_match.is_some() {
                        // This means that there was an explicit any in a param.
                        debug!(
                            "Decided overload as not found, because of Any, \
                                which match multiple overload versions"
                        );
                        return OverloadResult::NotFound;
                    } else if !arbitrary_length_handled {
                        debug!("Overload #{i} matches, but arbitrary length not handled");
                        if first_arbitrary_length_not_handled.is_none() {
                            first_arbitrary_length_not_handled = Some(callable);
                        }
                    } else {
                        debug!(
                            "Decided overload for {} (called on #{}): {:?}",
                            self.name(i_s.db),
                            args.starting_line(),
                            callable.content.format(&FormatData::new_short(i_s.db))
                        );
                        args.reset_points_from_backup(&points_backup);
                        return OverloadResult::Single(callable);
                    }
                }
                SignatureMatch::TrueWithAny { argument_indices } if !had_error => {
                    // TODO there could be three matches or more?
                    // TODO maybe merge list[any] and list[int]
                    if let Some((_, ref old_indices)) = multi_any_match {
                        // If multiple signatures match because of Any, we should just return
                        // without an error message, there is no clear choice, i.e. it's ambiguous,
                        // but there should also not be an error.
                        if are_any_arguments_ambiguous_in_overload(
                            i_s.db,
                            old_indices,
                            &argument_indices,
                        ) {
                            if had_error {
                                args.reset_points_from_backup(&points_backup);
                                // Need to run the whole thing again to generate errors, because
                                // the function is not going to be checked.
                                match_signature(i_s, result_context, callable);
                                todo!("Add a test")
                            }
                            debug!(
                                "Decided overload with any for {} (called on #{}): {:?}",
                                self.name(i_s.db),
                                args.starting_line(),
                                callable.content.format(&FormatData::new_short(i_s.db)),
                            );
                            args.reset_points_from_backup(&points_backup);
                            return OverloadResult::NotFound;
                        }
                        debug!("Overload #{i} is a follow-up any match, and therefore not used");
                    } else {
                        debug!("Overload #{i} matches as a first any match");
                        multi_any_match = Some((callable, argument_indices))
                    }
                }
                SignatureMatch::False { similar: true }
                | SignatureMatch::TrueWithAny { .. }
                | SignatureMatch::True { .. } => {
                    debug!("Overload #{i} mismatch, is similar.");
                    if first_similar.is_none() {
                        first_similar = Some(callable)
                    }
                }
                SignatureMatch::False { similar: false } => {
                    debug!("Overload #{i} mismatch, is not similar.");
                }
            }
            args.reset_points_from_backup(&points_backup);
        }
        if let Some((callable, _)) = multi_any_match {
            debug!(
                "Decided overload with any fallback for {} (called on #{}): {:?}",
                self.name(i_s.db),
                args.starting_line(),
                callable.content.format(&FormatData::new_short(i_s.db))
            );
            return OverloadResult::Single(callable);
        }
        if let Some(callable) = first_arbitrary_length_not_handled {
            debug!(
                "Decided overload with arbitrary length not handled for {} (called on #{}): {:?}",
                self.name(i_s.db),
                args.starting_line(),
                callable.content.format(&FormatData::new_short(i_s.db))
            );
            return OverloadResult::Single(callable);
        }
        if first_similar.is_none() && args.has_a_union_argument(i_s) {
            let mut non_union_args = vec![];
            match self.check_union_math(
                i_s,
                result_context,
                args.iter(i_s.mode),
                skip_first_argument,
                &mut non_union_args,
                &|issue| args.add_issue(i_s, issue),
                search_init,
                class,
                as_union_math_type,
            ) {
                UnionMathResult::Match { result, .. } => {
                    debug!(
                        "Decided overload as union math result {} (called on #{}): {:?}",
                        self.name(i_s.db),
                        args.starting_line(),
                        result.format(&FormatData::new_short(i_s.db))
                    );
                    return OverloadResult::Union(result);
                }
                UnionMathResult::FirstSimilarIndex(index) => {
                    first_similar = Some(Callable::new(
                        self.overload.iter_functions().nth(index).unwrap(),
                        self.class,
                    ))
                }
                UnionMathResult::NoMatch => (),
            }
        }
        if result_context.has_explicit_type() {
            // In case the context causes issues where an overload cannot be resolved, we just try
            // to run it without it. Note that we know at this point that the overload failed, it's
            // just a matter of what to display in case of failure. It's also a bit weird that we
            // run everything again, but in normal code overloads almost always do not fail, so
            // it shouldn't impact performance, really.
            debug!("Rerun overload without context");
            return debug_indent(|| {
                self.find_matching_function(
                    i_s,
                    args,
                    skip_first_argument,
                    class,
                    search_init,
                    &mut ResultContext::Unknown,
                    on_type_error,
                    as_union_math_type,
                )
            });
        }
        if let Some(callable) = first_similar {
            // In case of similar params, we simply use the first similar overload and calculate
            // its diagnostics and return its types.
            // This is also how mypy does it. See `check_overload_call` (9943444c7)
            debug!(
                "Decided overload as first similar: {} (called on #{}): {:?}",
                self.name(i_s.db),
                args.starting_line(),
                callable.content.format(&FormatData::new_short(i_s.db))
            );
            return OverloadResult::Single(callable);
        }
        if let Some(on_overload_mismatch) = on_type_error.on_overload_mismatch {
            on_overload_mismatch()
        } else {
            let f_or_c = FunctionOrCallable::Callable(Callable::new(
                self.overload.iter_functions().next().unwrap(),
                self.class,
            ));
            let t = IssueKind::OverloadMismatch {
                name: (on_type_error.generate_diagnostic_string)(&f_or_c, i_s.db)
                    .unwrap_or_else(|| todo!())
                    .into(),
                args: args.iter(i_s.mode).into_argument_types(i_s),
                variants: self.variants(i_s, class.filter(|_| search_init)),
            };
            args.add_issue(i_s, t);
        }
        debug!("Decided overload as not found");
        if let Some(callable) = had_error_in_func {
            // Need to run the whole thing again to generate errors, because the function is not
            // going to be checked.
            match_signature(i_s, result_context, callable);
        }
        OverloadResult::NotFound
    }

    fn check_union_math<'x>(
        &self,
        i_s: &InferenceState<'db, '_>,
        result_context: &mut ResultContext,
        mut args: ArgIterator<'db, 'x>,
        skip_first_argument: bool,
        non_union_args: &mut Vec<Arg<'db, 'x>>,
        add_issue: &impl Fn(IssueKind),
        search_init: bool,
        class: Option<&Class>,
        as_union_math_type: &impl Fn(&Callable, CalculatedTypeArgs) -> Type,
    ) -> UnionMathResult {
        if let Some(next_arg) = args.next() {
            let InferredArg::Inferred(inf) = next_arg.infer(result_context) else {
                non_union_args.push(next_arg);
                return self.check_union_math(
                    i_s,
                    result_context,
                    args,
                    skip_first_argument,
                    non_union_args,
                    add_issue,
                    search_init,
                    class,
                    as_union_math_type,
                );
            };
            if let Some(u) = inf.as_cow_type(i_s).maybe_union_like(i_s.db) {
                // This unsafe feels very bad, but it seems to be fine, because we don't reuse the
                // argument we add here outside of this function. It is only ever used in recursive
                // function calls of this function.
                let nxt_arg: &'x Arg<'db, 'x> = unsafe { std::mem::transmute(&next_arg) };
                non_union_args.push(Arg {
                    index: next_arg.index,
                    kind: ArgKind::Overridden {
                        original: nxt_arg,
                        inferred: Inferred::new_any(AnyCause::Todo),
                    },
                });
                let mut unioned = Type::Never(NeverCause::Other);
                let mut first_similar = None;
                let mut mismatch = false;
                for entry in u.into_owned().entries.into_vec().into_iter() {
                    let non_union_args_len = non_union_args.len();
                    non_union_args.last_mut().unwrap().kind = ArgKind::Overridden {
                        original: nxt_arg,
                        inferred: Inferred::from_type(entry.type_),
                    };
                    let r = self.check_union_math(
                        i_s,
                        result_context,
                        args.clone(),
                        skip_first_argument,
                        non_union_args,
                        add_issue,
                        search_init,
                        class,
                        as_union_math_type,
                    );
                    if let UnionMathResult::Match {
                        first_similar_index,
                        ..
                    }
                    | UnionMathResult::FirstSimilarIndex(first_similar_index) = r
                    {
                        if first_similar
                            .map(|f| f > first_similar_index)
                            .unwrap_or(true)
                        {
                            first_similar = Some(first_similar_index);
                        }
                    }
                    match r {
                        UnionMathResult::Match { result, .. } if !mismatch => {
                            unioned = unioned.simplified_union(i_s, &result);
                        }
                        _ => mismatch = true,
                    };
                    non_union_args.truncate(non_union_args_len);
                }
                if mismatch {
                    if let Some(first_similar_index) = first_similar {
                        UnionMathResult::FirstSimilarIndex(first_similar_index)
                    } else {
                        UnionMathResult::NoMatch
                    }
                } else {
                    UnionMathResult::Match {
                        result: unioned,
                        first_similar_index: first_similar.unwrap(),
                    }
                }
            } else {
                non_union_args.push(next_arg);
                self.check_union_math(
                    i_s,
                    result_context,
                    args,
                    skip_first_argument,
                    non_union_args,
                    add_issue,
                    search_init,
                    class,
                    as_union_math_type,
                )
            }
        } else {
            let mut first_similar = None;
            for (i, callable) in self.overload.iter_functions().enumerate() {
                let callable = Callable::new(callable, self.class);
                let (calculated_type_args, had_error) = i_s.avoid_errors_within(|i_s| {
                    if search_init {
                        calculate_callable_dunder_init_type_vars_and_return(
                            i_s,
                            class.unwrap(),
                            callable,
                            non_union_args.clone().into_iter(),
                            add_issue,
                            true,
                            result_context,
                            None,
                        )
                    } else {
                        calculate_callable_type_vars_and_return(
                            i_s,
                            callable,
                            non_union_args.clone().into_iter(),
                            add_issue,
                            skip_first_argument,
                            result_context,
                            None,
                        )
                    }
                });
                if had_error {
                    todo!()
                }
                match calculated_type_args.matches {
                    SignatureMatch::TrueWithAny { .. } | SignatureMatch::True { .. } => {
                        return UnionMathResult::Match {
                            result: as_union_math_type(&callable, calculated_type_args),
                            first_similar_index: i,
                        };
                    }
                    SignatureMatch::False { similar: true } if first_similar.is_none() => {
                        first_similar = Some(i);
                    }
                    SignatureMatch::False { .. } => (),
                }
            }
            if let Some(first_similar) = first_similar {
                UnionMathResult::FirstSimilarIndex(first_similar)
            } else {
                UnionMathResult::NoMatch
            }
        }
    }

    fn variants(&self, i_s: &InferenceState<'db, '_>, init_cls: Option<&Class>) -> Box<[Box<str>]> {
        let format_data = &FormatData::new_short(i_s.db);
        self.overload
            .iter_functions()
            .map(|callable| {
                if let Some(class) = self.class {
                    let mut c;
                    if matches!(class.generics, Generics::NotDefinedYet) {
                        c = callable.as_ref().clone();
                        if let Some(init_cls) = init_cls {
                            c.return_type = Class::with_self_generics(i_s.db, init_cls.node_ref)
                                .as_type(i_s.db);
                        }
                        c.type_vars = class.type_vars(i_s).clone();
                    } else {
                        c = replace_class_type_vars_in_callable(
                            i_s.db,
                            callable,
                            Some(&class),
                            &|| None,
                        );
                        if let Some(init_cls) = init_cls {
                            c.return_type = init_cls.as_type(i_s.db)
                        }
                    };
                    c.format_pretty(format_data)
                } else {
                    callable.format_pretty(format_data)
                }
            })
            .collect()
    }

    fn fallback_type(&self, i_s: &InferenceState<'db, '_>) -> Inferred {
        let mut t: Option<Type> = None;
        for callable in self.overload.iter_functions() {
            let f_t = &callable.return_type;
            if let Some(old_t) = t.take() {
                t = Some(old_t.merge_matching_parts(i_s.db, f_t))
            } else {
                t = Some(f_t.clone());
            }
        }
        Inferred::from_type(t.unwrap())
    }

    pub fn as_type(
        &self,
        i_s: &InferenceState<'db, '_>,
        replace_self_type: Option<&dyn Fn() -> Type>,
    ) -> Type {
        if let Some(replace_self_type) = replace_self_type {
            Type::FunctionOverload(FunctionOverload::new(
                self.overload
                    .iter_functions()
                    .map(|callable| {
                        let mut callable = replace_class_type_vars_in_callable(
                            i_s.db,
                            &callable.remove_first_positional_param().unwrap(),
                            self.class.as_ref(),
                            &|| Some(replace_self_type()),
                        );
                        callable
                            .kind
                            .update_had_first_self_or_class_annotation(true);
                        Rc::new(callable)
                    })
                    .collect(),
            ))
        } else {
            Type::FunctionOverload(self.overload.clone())
        }
    }

    pub(crate) fn execute(
        &self,
        i_s: &InferenceState<'db, '_>,
        args: &dyn Args<'db>,
        result_context: &mut ResultContext,
        on_type_error: OnTypeError,
    ) -> Inferred {
        self.execute_internal(i_s, args, false, result_context, on_type_error, &|| None)
    }

    pub(super) fn execute_internal(
        &self,
        i_s: &InferenceState<'db, '_>,
        args: &dyn Args<'db>,
        skip_first_argument: bool,
        result_context: &mut ResultContext,
        on_type_error: OnTypeError,
        replace_self_type: ReplaceSelf,
    ) -> Inferred {
        debug!("Execute overloaded function {}", self.name(i_s.db));
        debug_indent(|| {
            match self.find_matching_function(
                i_s,
                args,
                skip_first_argument,
                None,
                false,
                result_context,
                on_type_error,
                &|callable, calculated_type_args| {
                    calculated_type_args
                        .into_return_type(
                            i_s,
                            &callable.content.return_type,
                            self.class.as_ref(),
                            replace_self_type,
                        )
                        .as_type(i_s)
                },
            ) {
                OverloadResult::Single(callable) => {
                    let result = callable.execute_internal(
                        i_s,
                        args,
                        skip_first_argument,
                        on_type_error,
                        result_context,
                        Some(replace_self_type),
                    );
                    if callable.content.return_type.is_never() {
                        FLOW_ANALYSIS.with(|fa| fa.mark_current_frame_unreachable())
                    }
                    result
                }
                OverloadResult::Union(t) => Inferred::from_type(t),
                OverloadResult::NotFound => self.fallback_type(i_s),
            }
        })
    }

    pub fn name(&self, db: &'a Database) -> &'a str {
        self.overload
            .iter_functions()
            .next()
            .unwrap()
            .name
            .as_ref()
            .unwrap_or_else(|| todo!())
            .as_str(db)
    }
}

fn are_any_arguments_ambiguous_in_overload(
    db: &Database,
    a: &[ArgumentIndexWithParam],
    b: &[ArgumentIndexWithParam],
) -> bool {
    // This function checks if an argument with an Any (like List[Any]) makes it unclear which
    // overload would need to be chosen. Please have a look at the test
    // `testOverloadWithOverlappingItemsAndAnyArgument4` for more information.
    for p1 in a {
        for p2 in b {
            if p1.argument_index == p2.argument_index && p1.type_ != p2.type_ {
                return true;
            }
        }
    }
    false
}
