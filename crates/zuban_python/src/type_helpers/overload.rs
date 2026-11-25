use std::{
    borrow::Cow,
    cell::{Cell, RefCell},
    sync::Arc,
};

use utils::FastHashMap;

use super::Callable;
use crate::{
    arguments::{Arg, ArgIterator, ArgKind, InferredArg},
    file::FLOW_ANALYSIS,
    match_::{ArgumentIndexWithParam, SignatureMatch},
    matcher::{CalculatedTypeArgs, calc_callable_dunder_init_type_vars, calc_callable_type_vars},
    prelude::*,
    type_::{
        ComplexTypeGatherer, FunctionOverload, OnTypeError, PrettyCallableOptions, ReplaceSelf,
    },
    type_helpers::Generics,
};

#[derive(Debug)]
pub(crate) struct OverloadedFunction<'a> {
    overload: &'a FunctionOverload,
    class: Option<Class<'a>>,
}

pub(crate) enum OverloadResult<'a> {
    Single(Callable<'a>),
    Union(Type),
    MultiAnyMatch,
    NotFound {
        had_error_in_callable: Option<Callable<'a>>,
    },
    TooManyUnions,
}

#[derive(Debug)]
pub(crate) enum UnionMathResult {
    FirstSimilarIndex(usize),
    Match {
        first_similar_index: usize,
        result: Type,
    },
    NoMatch,
    TooManyUnions,
}

impl<'db: 'a, 'a> OverloadedFunction<'a> {
    pub fn new(overload: &'a FunctionOverload, class: Option<Class<'a>>) -> Self {
        Self { overload, class }
    }

    pub(crate) fn find_matching_function(
        &self,
        i_s: &InferenceState<'db, '_>,
        args: &dyn Args<'db>,
        skip_first_argument: bool,
        class: Option<&Class>,
        search_init: bool, // TODO this feels weird, maybe use a callback?
        replace_self: Option<ReplaceSelf>,
        on_type_error: OnTypeError,
        as_union_math_type: &impl Fn(&Callable, CalculatedTypeArgs) -> Type,
    ) -> OverloadResult<'a> {
        let match_signature =
            |i_s: &InferenceState<'db, '_>,
             callable: Callable<'a>,
             args_iter: &mut dyn Iterator<Item = Arg<'db, '_>>| {
                if search_init {
                    calc_callable_dunder_init_type_vars(
                        i_s,
                        class.unwrap(),
                        callable,
                        // Variance rules in traits suck and hit us again
                        args_iter.map(|arg| arg),
                        |issue| args.add_issue(i_s, issue),
                        true,
                        &mut ResultContext::Unknown,
                        None,
                    )
                } else {
                    calc_callable_type_vars(
                        i_s,
                        callable,
                        args_iter.map(|arg| arg),
                        |issue| args.add_issue(i_s, issue),
                        skip_first_argument,
                        &mut ResultContext::Unknown,
                        replace_self,
                        None,
                    )
                }
            };
        let counter = nested_counter();
        // Since the overloads infer arguments multiple times (e.g. [1] might be inferred as
        // list[int] or list[object], depending on the overload. In multiple nested overloads this
        // can blow up exponentially.
        let result = counter
            .maybe_reuse_previous_solution(i_s.db, self.overload, args, &self.class)
            .unwrap_or_else(|| {
                let solution = self.find_matching_function_part2(
                    i_s,
                    args,
                    &match_signature,
                    as_union_math_type,
                );
                counter.register_solution(i_s.db, self.overload, args, &self.class, &solution);
                solution
            });
        match &result {
            OverloadResult::Single(callable) => {
                if i_s.db.project.flags.disallow_deprecated
                    && let Some(deprecated) = &callable.content.deprecated_reason
                {
                    let fmt = callable.content.format_pretty_detailed(
                        &FormatData::new_reveal_type(i_s.db),
                        PrettyCallableOptions {
                            avoid_classmethod_param: true,
                            ..Default::default()
                        },
                    );
                    args.add_issue(
                        i_s,
                        IssueKind::Deprecated {
                            identifier: format!(
                                "overload def {} of function {}",
                                &fmt[fmt.find('(').unwrap()..],
                                callable.content.qualified_name(i_s.db)
                            )
                            .into(),
                            reason: deprecated.clone(),
                        },
                    );
                }
            }
            OverloadResult::Union(_) | OverloadResult::MultiAnyMatch => (),
            OverloadResult::TooManyUnions => {
                args.add_issue(i_s, IssueKind::OverloadTooManyUnions);
            }
            OverloadResult::NotFound {
                had_error_in_callable,
            } => {
                if let Some(on_overload_mismatch) = on_type_error.on_overload_mismatch {
                    on_overload_mismatch()
                } else {
                    debug!(
                        "Overload fallback: Infer arguments and add errors since no match was found"
                    );
                    let _indent = debug_indent();
                    let c =
                        Callable::new(self.overload.iter_functions().next().unwrap(), self.class);
                    let t = IssueKind::OverloadMismatch {
                        name: (on_type_error.generate_diagnostic_string)(&c, i_s.db)
                            .expect(
                                "The diagnostic string should always be set for overloads, \
                             because the name is always defined",
                            )
                            .into(),
                        args: args.iter(i_s.mode).into_argument_types(i_s),
                        variants: self.variants(i_s, class.filter(|_| search_init)),
                    };
                    args.add_issue(i_s, t);
                }
                if let Some(callable) = had_error_in_callable {
                    // Need to run the whole thing again to generate errors, because the function is not
                    // going to be checked.
                    match_signature(i_s, *callable, &mut args.iter(i_s.mode));
                }
            }
        }
        result
    }

    pub(crate) fn find_matching_function_part2(
        &self,
        i_s: &InferenceState<'db, '_>,
        args: &dyn Args<'db>,
        match_signature: &impl Fn(
            &InferenceState<'db, '_>,
            Callable<'a>,
            &mut dyn Iterator<Item = Arg<'db, '_>>,
        ) -> CalculatedTypeArgs,
        as_union_math_type: &impl Fn(&Callable, CalculatedTypeArgs) -> Type,
    ) -> OverloadResult<'a> {
        let mut first_arbitrary_length_not_handled = None;
        let mut first_similar = None;
        let mut multi_any_match: Option<(Callable, Box<_>)> = None;
        let mut had_error_in_callable = None;
        let points_backup = args.points_backup();
        for (i, callable) in self.overload.iter_functions().enumerate() {
            debug!("Checking overload item #{i}");
            let _indent = debug_indent();
            let callable = Callable::new(callable, self.class);
            let (calculated_type_args, had_error) = i_s.avoid_errors_within(|i_s| {
                match_signature(i_s, callable, &mut args.iter(i_s.mode))
            });
            if had_error && had_error_in_callable.is_none() {
                had_error_in_callable = Some(callable);
            }
            match calculated_type_args.matches {
                SignatureMatch::True {
                    arbitrary_length_handled,
                } if !had_error => {
                    if multi_any_match.is_some() {
                        // This means that there was an explicit any in a param.
                        debug!(
                            "Decided overload #{i} as not found, because of Any and non-any match"
                        );
                        return OverloadResult::MultiAnyMatch;
                    } else if !arbitrary_length_handled {
                        debug!("Overload #{i} matches, but arbitrary length not handled");
                        if first_arbitrary_length_not_handled.is_none() {
                            first_arbitrary_length_not_handled = Some(callable);
                        }
                    } else {
                        debug!(
                            "Decided to use overload #{i} for {} (called on #{}): {:?}",
                            self.name(i_s.db),
                            args.starting_line(i_s.db),
                            callable.content.format(&FormatData::new_short(i_s.db))
                        );
                        args.reset_points_from_backup(&points_backup);
                        return OverloadResult::Single(callable);
                    }
                }
                SignatureMatch::TrueWithAny { argument_indices } if !had_error => {
                    // TODO there could be three matches or more?
                    // TODO maybe merge list[any] and list[int]
                    if let Some((other_callable, ref old_indices)) = multi_any_match {
                        // If multiple signatures match because of Any, we should just return
                        // without an error message, there is no clear choice, i.e. it's ambiguous,
                        // but there should also not be an error.
                        if are_any_arguments_ambiguous_in_overload(old_indices, &argument_indices)
                            // If return type is the same, we don't have to return.
                            && !(other_callable
                                .content
                                .return_type
                                .is_equal_type(i_s.db, &callable.content.return_type)
                                && callable.content.guard.is_none()
                                && other_callable.content.guard.is_none())
                        {
                            debug!("Decided overload #{i} as not found, because of 2+ Any matches");
                            args.reset_points_from_backup(&points_backup);
                            return OverloadResult::MultiAnyMatch;
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
            // Not doing this is a bad thing, but otherwise nested overloads can explode
            // exponentially.
            args.reset_points_from_backup(&points_backup);
        }
        if let Some((callable, _)) = multi_any_match {
            debug!(
                "Decided overload with any fallback for {} (called on #{}): {:?}",
                self.name(i_s.db),
                args.starting_line(i_s.db),
                callable.content.format(&FormatData::new_short(i_s.db))
            );
            return OverloadResult::Single(callable);
        }
        if let Some(callable) = first_arbitrary_length_not_handled {
            debug!(
                "Decided overload with arbitrary length not handled for {} (called on #{}): {:?}",
                self.name(i_s.db),
                args.starting_line(i_s.db),
                callable.content.format(&FormatData::new_short(i_s.db))
            );
            return OverloadResult::Single(callable);
        }
        // Mypy has a bit of a different way of working than the conformance tests
        if first_similar.is_none() || !i_s.db.mypy_compatible() {
            debug!("Find out if we want to check union math");
            let _indent = debug_indent();
            if args.should_do_union_math_for_overloads(i_s) {
                debug!("Checking overload union math");
                let _indent = debug_indent();
                let mut non_union_args = vec![];
                match self.check_union_math(
                    i_s,
                    args.iter(i_s.mode),
                    &mut non_union_args,
                    match_signature,
                    as_union_math_type,
                    0,
                ) {
                    UnionMathResult::Match { result, .. } => {
                        debug!(
                            "Decided overload as union math result {} (called on #{}): {:?}",
                            self.name(i_s.db),
                            args.starting_line(i_s.db),
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
                    UnionMathResult::TooManyUnions => return OverloadResult::TooManyUnions,
                }
            }
        }
        if let Some(callable) = first_similar {
            // In case of similar params, we simply use the first similar overload and calculate
            // its diagnostics and return its types.
            // This is also how mypy does it. See `check_overload_call` (9943444c7)
            debug!(
                "Decided overload as first similar: {} (called on #{}): {:?}",
                self.name(i_s.db),
                args.starting_line(i_s.db),
                callable.content.format(&FormatData::new_short(i_s.db))
            );
            return OverloadResult::Single(callable);
        }
        debug!("Decided overload as not found");
        OverloadResult::NotFound {
            had_error_in_callable,
        }
    }

    fn check_union_math<'x>(
        &self,
        i_s: &InferenceState<'db, '_>,
        mut args: ArgIterator<'db, 'x>,
        non_union_args: &mut Vec<Arg<'db, 'x>>,
        match_signature: &impl Fn(
            &InferenceState<'db, '_>,
            Callable<'a>,
            &mut dyn Iterator<Item = Arg<'db, '_>>,
        ) -> CalculatedTypeArgs,
        as_union_math_type: &impl Fn(&Callable, CalculatedTypeArgs) -> Type,
        recursion_depth: usize,
    ) -> UnionMathResult {
        // Uses the same name as the Mypy one, look it up for an explanation
        const MAX_UNIONS: usize = 5;
        if recursion_depth >= MAX_UNIONS {
            return UnionMathResult::TooManyUnions;
        }

        if let Some(next_arg) = args.next() {
            let InferredArg::Inferred(inf) = next_arg.infer(&mut ResultContext::Unknown) else {
                non_union_args.push(next_arg);
                return self.check_union_math(
                    i_s,
                    args,
                    non_union_args,
                    match_signature,
                    as_union_math_type,
                    recursion_depth,
                );
            };
            let t = inf.as_cow_type(i_s);
            if let Some(u) = t.maybe_union_like_with_materializations(i_s.db) {
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
                let mut unioned = ComplexTypeGatherer::default();
                let mut first_similar = None;
                let mut mismatch = false;
                for entry in u.entries.iter() {
                    debug!(
                        "Split union math, use {:?} of {:?}",
                        entry.format_short(i_s.db),
                        t.format_short(i_s.db)
                    );
                    let _indent = debug_indent();
                    let non_union_args_len = non_union_args.len();
                    non_union_args.last_mut().unwrap().kind = ArgKind::Overridden {
                        original: nxt_arg,
                        inferred: Inferred::from_type(entry.clone()),
                    };
                    let r = self.check_union_math(
                        i_s,
                        args.clone(),
                        non_union_args,
                        match_signature,
                        as_union_math_type,
                        recursion_depth + 1,
                    );
                    if let UnionMathResult::Match {
                        first_similar_index,
                        ..
                    }
                    | UnionMathResult::FirstSimilarIndex(first_similar_index) = r
                        && first_similar
                            .map(|f| f > first_similar_index)
                            .unwrap_or(true)
                    {
                        first_similar = Some(first_similar_index);
                    }
                    match r {
                        UnionMathResult::Match { result, .. } if !mismatch => {
                            unioned.add(result);
                        }
                        UnionMathResult::TooManyUnions => return UnionMathResult::TooManyUnions,
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
                        result: unioned.into_simplified_type(i_s),
                        first_similar_index: first_similar.unwrap(),
                    }
                }
            } else {
                non_union_args.push(next_arg);
                self.check_union_math(
                    i_s,
                    args,
                    non_union_args,
                    match_signature,
                    as_union_math_type,
                    recursion_depth,
                )
            }
        } else {
            let mut first_similar = None;
            for (i, callable) in self.overload.iter_functions().enumerate() {
                let callable = Callable::new(callable, self.class);
                let calculated_type_args =
                    match_signature(i_s, callable, &mut non_union_args.clone().into_iter());
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
                    if matches!(class.generics, Generics::NotDefinedYet { .. }) {
                        c = callable.as_ref().clone();
                        if let Some(init_cls) = init_cls {
                            c.return_type = Class::with_self_generics(i_s.db, init_cls.node_ref)
                                .as_type(i_s.db);
                        }
                        c.type_vars = class.type_vars(i_s).clone();
                    } else {
                        c = callable
                            .replace_class_type_vars(i_s.db, Some(&class), &|| None)
                            .unwrap_or_else(|| (**callable).clone());
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
                        let without_first_param = callable
                            .remove_first_positional_param()
                            // The callable did not have a first positional param. This
                            // should be flagged when generating diagnostics. here we just
                            // try to not crash.
                            .unwrap_or_else(|| (**callable).clone());
                        let mut callable = without_first_param
                            .replace_class_type_vars(i_s.db, self.class.as_ref(), &|| {
                                Some(replace_self_type())
                            })
                            .unwrap_or(without_first_param);
                        callable
                            .kind
                            .update_had_first_self_or_class_annotation(true);
                        Arc::new(callable)
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
        replace_self: ReplaceSelf,
    ) -> Inferred {
        debug!("Execute overloaded function {}", self.name(i_s.db));
        let _indent = debug_indent();
        match self.find_matching_function(
            i_s,
            args,
            skip_first_argument,
            None,
            false,
            Some(replace_self),
            on_type_error,
            &|callable, calculated_type_args| {
                calculated_type_args
                    .into_return_type(
                        i_s,
                        &callable.content.return_type,
                        self.class.as_ref(),
                        replace_self,
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
                    Some(replace_self),
                );
                if callable.content.return_type.is_never() {
                    FLOW_ANALYSIS.with(|fa| fa.mark_current_frame_unreachable())
                }
                result
            }
            OverloadResult::Union(t) => Inferred::from_type(t),
            OverloadResult::NotFound { .. }
            | OverloadResult::MultiAnyMatch
            | OverloadResult::TooManyUnions => {
                let to_type = |c: &'a CallableContent| -> Cow<'a, Type> {
                    if let Some(cls) = self.class {
                        return c.return_type.replace_type_var_likes(i_s.db, &mut |usage| {
                            usage.maybe_class_generic(i_s.db, &cls)
                        });
                    }
                    Cow::Borrowed(&c.return_type)
                };
                let mut t: Option<Type> = None;
                for callable in self.overload.iter_functions() {
                    let f_t = to_type(callable);
                    if let Some(old_t) = t.take() {
                        t = Some(old_t.merge_matching_parts(i_s.db, &f_t))
                    } else {
                        t = Some(f_t.into_owned());
                    }
                }

                let t = t.unwrap();
                Inferred::from_type(t.maybe_replace_self(i_s.db, replace_self).unwrap_or(t))
            }
        }
    }

    pub fn name(&self, db: &'a Database) -> &'a str {
        self.overload
            .iter_functions()
            .next()
            .unwrap()
            .name
            .as_ref()
            .expect("The name for an overload should always be set")
            .as_str(db)
    }
}

fn are_any_arguments_ambiguous_in_overload(
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

#[derive(PartialEq, Eq, Hash)]
struct CachedOverloadSolutionKey {
    overload: FunctionOverload,
    arguments_node: PointLink,
    class: Option<Type>,
}

#[derive(Debug)]
enum CachedOverloadSolution {
    Single(PointLink),
    Union(Type),
    MultiAnyMatch,
    NotFound {
        had_error_in_callable: Option<PointLink>,
    },
    TooManyUnions,
}

#[derive(Default)]
struct NestedOverloadDetails {
    count: Cell<usize>,
    previous_solution_cache:
        RefCell<FastHashMap<CachedOverloadSolutionKey, CachedOverloadSolution>>,
}

thread_local!(static NESTED_OVERLOAD_COUNTER: NestedOverloadDetails = const { NestedOverloadDetails {
    count: Cell::new(0),
    previous_solution_cache: RefCell::new(FastHashMap::with_hasher(std::hash::BuildHasherDefault::new())),
} });

struct NestedOverloadCounter();

impl NestedOverloadCounter {
    fn maybe_reuse_previous_solution<'a>(
        &self,
        db: &Database,
        overload: &'a FunctionOverload,
        args: &dyn Args,
        class: &Option<Class<'a>>,
    ) -> Option<OverloadResult<'a>> {
        NESTED_OVERLOAD_COUNTER.with(|details| {
            let key = Self::to_key(db, details, overload, args, class)?;
            let link_to_callable = |link| {
                let found = overload
                    .iter_functions()
                    .find(|o| o.defined_at == link)
                    .unwrap();
                Callable::new(found, *class)
            };
            Some(match details.previous_solution_cache.borrow().get(&key)? {
                CachedOverloadSolution::Single(link) => {
                    OverloadResult::Single(link_to_callable(*link))
                }
                CachedOverloadSolution::Union(t) => OverloadResult::Union(t.clone()),
                CachedOverloadSolution::MultiAnyMatch => OverloadResult::MultiAnyMatch,
                CachedOverloadSolution::NotFound {
                    had_error_in_callable,
                } => OverloadResult::NotFound {
                    had_error_in_callable: had_error_in_callable.map(link_to_callable),
                },
                CachedOverloadSolution::TooManyUnions => OverloadResult::TooManyUnions,
            })
        })
    }

    fn to_key(
        db: &Database,
        details: &NestedOverloadDetails,
        overload: &FunctionOverload,
        args: &dyn Args,
        class: &Option<Class>,
    ) -> Option<CachedOverloadSolutionKey> {
        if details.count.get() <= 1 {
            return None;
        }
        Some(CachedOverloadSolutionKey {
            overload: overload.clone(),
            arguments_node: args.as_node_ref_internal()?.as_link(),
            class: class.map(|c| c.as_type(db)),
        })
    }

    fn register_solution(
        &self,
        db: &Database,
        overload: &FunctionOverload,
        args: &dyn Args,
        class: &Option<Class>,
        solution: &OverloadResult,
    ) {
        NESTED_OVERLOAD_COUNTER.with(|details| {
            if let Some(key) = Self::to_key(db, details, overload, args, class) {
                let result = match solution {
                    OverloadResult::Single(callable) => {
                        CachedOverloadSolution::Single(callable.content.defined_at)
                    }
                    OverloadResult::Union(u) => CachedOverloadSolution::Union(u.clone()),
                    OverloadResult::MultiAnyMatch => CachedOverloadSolution::MultiAnyMatch,
                    OverloadResult::NotFound {
                        had_error_in_callable,
                    } => CachedOverloadSolution::NotFound {
                        had_error_in_callable: had_error_in_callable.map(|e| e.content.defined_at),
                    },
                    OverloadResult::TooManyUnions => CachedOverloadSolution::TooManyUnions,
                };
                let replaced = details
                    .previous_solution_cache
                    .borrow_mut()
                    .insert(key, result);
                debug_assert!(replaced.is_none());
            }
        })
    }
}

#[inline(always)]
#[must_use]
fn nested_counter() -> NestedOverloadCounter {
    NESTED_OVERLOAD_COUNTER.with(|details| {
        details.count.update(|c| c + 1);
        NestedOverloadCounter()
    })
}

impl Drop for NestedOverloadCounter {
    #[inline(always)]
    fn drop(&mut self) {
        NESTED_OVERLOAD_COUNTER.with(|details| {
            details.count.update(|c| c - 1);
            if details.count.get() == 0 {
                details.previous_solution_cache.borrow_mut().clear()
            }
        })
    }
}
