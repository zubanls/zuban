use std::rc::Rc;

use super::{Callable, Class};
use crate::{
    arguments::{Argument, ArgumentIterator, ArgumentKind, Arguments},
    database::Database,
    debug,
    diagnostics::IssueType,
    inference_state::InferenceState,
    inferred::Inferred,
    matching::{
        calculate_callable_init_type_vars_and_return, calculate_callable_type_vars_and_return,
        replace_class_type_vars_in_callable, ArgumentIndexWithParam, FormatData,
        FunctionOrCallable, OnTypeError, ResultContext, SignatureMatch,
    },
    node_ref::NodeRef,
    type_::{AnyCause, FunctionOverload, ReplaceSelf, Type},
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
        args: &dyn Arguments<'db>,
        skip_first_argument: bool,
        class: Option<&Class>,
        search_init: bool, // TODO this feels weird, maybe use a callback?
        result_context: &mut ResultContext,
        on_type_error: OnTypeError<'db, '_>,
    ) -> OverloadResult<'a> {
        let match_signature = |i_s: &InferenceState<'db, '_>,
                               result_context: &mut ResultContext,
                               callable: Callable| {
            if search_init {
                calculate_callable_init_type_vars_and_return(
                    i_s,
                    class.unwrap(),
                    callable,
                    args.iter(),
                    args.as_node_ref(),
                    result_context,
                    None,
                )
            } else {
                calculate_callable_type_vars_and_return(
                    i_s,
                    callable,
                    args.iter(),
                    args.as_node_ref(),
                    skip_first_argument,
                    result_context,
                    None,
                )
            }
        };
        let mut first_arbitrary_length_not_handled = None;
        let mut first_similar = None;
        let mut multi_any_match: Option<(_, _, Box<_>)> = None;
        let mut had_error_in_func = None;
        let points_backup = args.points_backup();
        for (i, callable) in self.overload.iter_functions().enumerate() {
            let callable = Callable::new(callable, self.class);
            let (calculated_type_args, had_error) =
                i_s.do_overload_check(|i_s| match_signature(i_s, result_context, callable));
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
                        if first_arbitrary_length_not_handled.is_none() {
                            first_arbitrary_length_not_handled =
                                Some((calculated_type_args.type_arguments, callable));
                        }
                    } else {
                        debug!(
                            "Decided overload for {} (called on #{}): {:?}",
                            self.name(i_s.db),
                            args.as_node_ref().line(),
                            callable.content.format(&FormatData::new_short(i_s.db))
                        );
                        args.reset_points_from_backup(&points_backup);
                        return OverloadResult::Single(callable);
                    }
                }
                SignatureMatch::TrueWithAny { argument_indices } if !had_error => {
                    // TODO there could be three matches or more?
                    // TODO maybe merge list[any] and list[int]
                    if let Some((_, _, ref old_indices)) = multi_any_match {
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
                                args.as_node_ref().line(),
                                callable.content.format(&FormatData::new_short(i_s.db)),
                            );
                            args.reset_points_from_backup(&points_backup);
                            return OverloadResult::NotFound;
                        }
                    } else {
                        multi_any_match = Some((
                            calculated_type_args.type_arguments,
                            callable,
                            argument_indices,
                        ))
                    }
                }
                SignatureMatch::False { similar: true }
                | SignatureMatch::TrueWithAny { .. }
                | SignatureMatch::True { .. } => {
                    if first_similar.is_none() {
                        first_similar = Some(callable)
                    }
                }
                SignatureMatch::False { similar: false } => (),
            }
            args.reset_points_from_backup(&points_backup);
        }
        if let Some((type_arguments, callable, _)) = multi_any_match {
            debug!(
                "Decided overload with any fallback for {} (called on #{}): {:?}",
                self.name(i_s.db),
                args.as_node_ref().line(),
                callable.content.format(&FormatData::new_short(i_s.db))
            );
            return OverloadResult::Single(callable);
        }
        if let Some((type_arguments, callable)) = first_arbitrary_length_not_handled {
            debug!(
                "Decided overload with arbitrary length not handled for {} (called on #{}): {:?}",
                self.name(i_s.db),
                args.as_node_ref().line(),
                callable.content.format(&FormatData::new_short(i_s.db))
            );
            return OverloadResult::Single(callable);
        }
        if first_similar.is_none() && args.has_a_union_argument(i_s) {
            let mut non_union_args = vec![];
            match self.check_union_math(
                i_s,
                result_context,
                args.iter(),
                skip_first_argument,
                &mut non_union_args,
                args.as_node_ref(),
                search_init,
                class,
            ) {
                UnionMathResult::Match { result, .. } => {
                    debug!(
                        "Decided overload as union math result {} (called on #{}): {:?}",
                        self.name(i_s.db),
                        args.as_node_ref().line(),
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
            return self.find_matching_function(
                i_s,
                args,
                skip_first_argument,
                class,
                search_init,
                &mut ResultContext::Unknown,
                on_type_error,
            );
        }
        if let Some(callable) = first_similar {
            // In case of similar params, we simply use the first similar overload and calculate
            // its diagnostics and return its types.
            // This is also how mypy does it. See `check_overload_call` (9943444c7)
            let calculated_type_args = match_signature(i_s, result_context, callable);
            debug!(
                "Decided overload as first similar: {} (called on #{}): {:?}",
                self.name(i_s.db),
                args.as_node_ref().line(),
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
            let t = IssueType::OverloadMismatch {
                name: (on_type_error.generate_diagnostic_string)(&f_or_c, i_s.db)
                    .unwrap_or_else(|| todo!())
                    .into(),
                args: args.iter().into_argument_types(i_s),
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
        mut args: ArgumentIterator<'db, 'x>,
        skip_first_argument: bool,
        non_union_args: &mut Vec<Argument<'db, 'x>>,
        args_node_ref: NodeRef,
        search_init: bool,
        class: Option<&Class>,
    ) -> UnionMathResult {
        if let Some(next_arg) = args.next() {
            let inf = next_arg.infer(i_s, result_context);
            if inf.is_union(i_s) {
                // TODO this is shit
                let nxt_arg: &'x Argument<'db, 'x> = unsafe { std::mem::transmute(&next_arg) };
                non_union_args.push(Argument {
                    index: next_arg.index,
                    kind: ArgumentKind::Overridden {
                        original: nxt_arg,
                        inferred: Inferred::new_any(AnyCause::Todo),
                    },
                });
                let Type::Union(u) = inf.as_type(i_s) else {
                    unreachable!()
                };
                let mut unioned = Type::Never;
                let mut first_similar = None;
                let mut mismatch = false;
                for entry in u.entries.into_vec().into_iter() {
                    let non_union_args_len = non_union_args.len();
                    non_union_args.last_mut().unwrap().kind = ArgumentKind::Overridden {
                        original: nxt_arg,
                        inferred: Inferred::from_type(entry.type_),
                    };
                    let r = self.check_union_math(
                        i_s,
                        result_context,
                        args.clone(),
                        skip_first_argument,
                        non_union_args,
                        args_node_ref,
                        search_init,
                        class,
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
                    args_node_ref,
                    search_init,
                    class,
                )
            }
        } else {
            let mut first_similar = None;
            for (i, callable) in self.overload.iter_functions().enumerate() {
                let callable = Callable::new(callable, self.class);
                let (calculated_type_args, had_error) = i_s.do_overload_check(|i_s| {
                    if search_init {
                        calculate_callable_init_type_vars_and_return(
                            i_s,
                            class.unwrap(),
                            callable,
                            non_union_args.clone().into_iter(),
                            args_node_ref,
                            result_context,
                            None,
                        )
                    } else {
                        calculate_callable_type_vars_and_return(
                            i_s,
                            callable,
                            non_union_args.clone().into_iter(),
                            args_node_ref,
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
                    SignatureMatch::True { .. } => {
                        if search_init {
                            todo!()
                        } else {
                            return UnionMathResult::Match {
                                result: callable
                                    .content
                                    .return_type
                                    .execute_and_resolve_type_vars(
                                        i_s,
                                        &calculated_type_args,
                                        self.class.as_ref(),
                                        &|| class.map(|c| c.as_type(i_s.db)).unwrap_or(Type::Self_),
                                    )
                                    .as_type(i_s),
                                first_similar_index: i,
                            };
                        }
                    }
                    SignatureMatch::TrueWithAny { argument_indices } => todo!(),
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
                    let mut callable = replace_class_type_vars_in_callable(
                        i_s.db,
                        callable,
                        Some(&class),
                        &|| Type::Self_,
                    );
                    if let Some(init_cls) = init_cls {
                        callable.return_type = init_cls.as_type(i_s.db)
                    }
                    callable.format_pretty(format_data)
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
        replace_self_type: Option<ReplaceSelf>,
    ) -> Type {
        if let Some(replace_self_type) = replace_self_type {
            Type::FunctionOverload(FunctionOverload::new(
                self.overload
                    .iter_functions()
                    .map(|callable| {
                        replace_class_type_vars_in_callable(
                            i_s.db,
                            &callable.remove_first_param().unwrap(),
                            self.class.as_ref(),
                            replace_self_type,
                        )
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
        args: &dyn Arguments<'db>,
        result_context: &mut ResultContext,
        on_type_error: OnTypeError<'db, '_>,
    ) -> Inferred {
        self.execute_internal(i_s, args, false, result_context, on_type_error)
    }

    pub(super) fn execute_internal(
        &self,
        i_s: &InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
        skip_first_argument: bool,
        result_context: &mut ResultContext,
        on_type_error: OnTypeError<'db, '_>,
    ) -> Inferred {
        debug!("Execute overloaded function {}", self.name(i_s.db));
        match self.find_matching_function(
            i_s,
            args,
            skip_first_argument,
            None,
            false,
            result_context,
            on_type_error,
        ) {
            OverloadResult::Single(callable) => callable.execute_internal(
                i_s,
                args,
                skip_first_argument,
                on_type_error,
                result_context,
            ),
            OverloadResult::Union(t) => Inferred::from_type(t),
            OverloadResult::NotFound => self.fallback_type(i_s),
        }
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
