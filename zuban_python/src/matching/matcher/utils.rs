use std::borrow::Cow;

use parsa_python_ast::ParamKind;

use super::{
    super::{
        params::{
            InferrableParamIterator, Param, ParamArgument, WrappedParamType, WrappedStar,
            WrappedStarStar,
        },
        ArgumentIndexWithParam, FormatData, Generics, Match, Matcher, MismatchReason, OnTypeError,
        ResultContext, SignatureMatch,
    },
    bound::TypeVarBound,
    type_var_matcher::{BoundKind, FunctionOrCallable, TypeVarMatcher},
};
use crate::{
    arguments::{Argument, ArgumentKind},
    database::PointLink,
    debug,
    diagnostics::IssueType,
    inference_state::InferenceState,
    matching::{ErrorTypes, GotType},
    node_ref::NodeRef,
    type_::{
        CallableParams, ClassGenerics, GenericItem, GenericsList, ReplaceSelf, Type,
        TypeVarLikeUsage, TypeVarLikes,
    },
    type_helpers::{Callable, Class, Function},
};

pub(crate) fn calculate_callable_init_type_vars_and_return<'db: 'a, 'a>(
    i_s: &InferenceState<'db, '_>,
    class: &Class,
    callable: Callable<'a>,
    args: impl Iterator<Item = Argument<'db, 'a>>,
    add_issue: impl Fn(IssueType),
    result_context: &mut ResultContext,
    on_type_error: Option<OnTypeError<'db, '_>>,
) -> CalculatedTypeArguments {
    calculate_init_type_vars_and_return(
        i_s,
        class,
        FunctionOrCallable::Callable(callable),
        args,
        add_issue,
        result_context,
        on_type_error,
    )
}

pub(crate) fn calculate_class_init_type_vars_and_return<'db: 'a, 'a>(
    i_s: &InferenceState<'db, '_>,
    class: &Class,
    function: Function<'a, 'a>,
    args: impl Iterator<Item = Argument<'db, 'a>>,
    add_issue: impl Fn(IssueType),
    result_context: &mut ResultContext,
    on_type_error: Option<OnTypeError<'db, '_>>,
) -> CalculatedTypeArguments {
    calculate_init_type_vars_and_return(
        i_s,
        class,
        FunctionOrCallable::Function(function),
        args,
        add_issue,
        result_context,
        on_type_error,
    )
}

fn calculate_init_type_vars_and_return<'db: 'a, 'a>(
    i_s: &InferenceState<'db, '_>,
    class: &Class,
    func_or_callable: FunctionOrCallable<'a>,
    args: impl Iterator<Item = Argument<'db, 'a>>,
    add_issue: impl Fn(IssueType),
    result_context: &mut ResultContext,
    on_type_error: Option<OnTypeError<'db, '_>>,
) -> CalculatedTypeArguments {
    debug!("Calculate __init__ type vars for class {}", class.name());
    let type_vars = class.type_vars(i_s);
    let has_generics =
        !matches!(class.generics, Generics::None | Generics::NotDefinedYet) || type_vars.is_empty();
    // Function type vars need to be calculated, so annotations are used.
    let func_type_vars = func_or_callable.type_vars(i_s);

    let match_in_definition;
    let matcher = if has_generics {
        match_in_definition = func_or_callable.defined_at();
        get_matcher(
            Some(class),
            func_or_callable,
            match_in_definition,
            None,
            func_type_vars,
        )
    } else {
        match_in_definition = class.node_ref.as_link();
        get_matcher(None, func_or_callable, match_in_definition, None, type_vars)
    };

    if has_generics {
        let mut type_arguments = calculate_type_vars(
            i_s,
            matcher,
            func_or_callable,
            None,
            args,
            add_issue,
            true,
            func_type_vars,
            match_in_definition,
            result_context,
            on_type_error,
        );
        type_arguments.type_arguments = match class.generics_as_list(i_s.db) {
            ClassGenerics::List(generics_list) => Some(generics_list),
            ClassGenerics::ExpressionWithClassType(_) => todo!(),
            ClassGenerics::SlicesWithClassTypes(_) => todo!(),
            ClassGenerics::None => None,
            ClassGenerics::NotDefinedYet => unreachable!(),
        };
        type_arguments
    } else {
        calculate_type_vars(
            i_s,
            matcher,
            func_or_callable,
            Some(class),
            args,
            add_issue,
            true,
            type_vars,
            match_in_definition,
            result_context,
            on_type_error,
        )
    }
}

#[derive(Debug)]
pub struct CalculatedTypeArguments {
    pub in_definition: PointLink,
    pub matches: SignatureMatch,
    pub type_arguments: Option<GenericsList>,
}

impl CalculatedTypeArguments {
    pub fn type_arguments_into_class_generics(self) -> ClassGenerics {
        match self.type_arguments {
            Some(g) => ClassGenerics::List(g),
            None => ClassGenerics::None,
        }
    }
}

impl CalculatedTypeArguments {
    pub fn lookup_type_var_usage(
        &self,
        i_s: &InferenceState,
        usage: TypeVarLikeUsage,
    ) -> GenericItem {
        if self.in_definition == usage.in_definition() {
            return if let Some(fm) = &self.type_arguments {
                fm[usage.index()].clone()
            } else {
                // TODO we are just passing the type vars again. Does this make sense?
                // usage.into_generic_item()
                todo!()
            };
        }
        usage.into_generic_item()
    }
}

pub(crate) fn calculate_function_type_vars_and_return<'db: 'a, 'a>(
    i_s: &InferenceState<'db, '_>,
    function: Function<'a, 'a>,
    args: impl Iterator<Item = Argument<'db, 'a>>,
    add_issue: impl Fn(IssueType),
    skip_first_param: bool,
    type_vars: &TypeVarLikes,
    match_in_definition: PointLink,
    replace_self: ReplaceSelf,
    result_context: &mut ResultContext,
    on_type_error: Option<OnTypeError<'db, '_>>,
) -> CalculatedTypeArguments {
    debug!("Calculate type vars for {}", function.diagnostic_string());
    let func_or_callable = FunctionOrCallable::Function(function);
    calculate_type_vars(
        i_s,
        get_matcher(
            None,
            func_or_callable,
            match_in_definition,
            Some(replace_self),
            type_vars,
        ),
        func_or_callable,
        None,
        args,
        add_issue,
        skip_first_param,
        type_vars,
        match_in_definition,
        result_context,
        on_type_error,
    )
}

pub(crate) fn calculate_callable_type_vars_and_return<'db: 'a, 'a>(
    i_s: &InferenceState<'db, '_>,
    callable: Callable<'a>,
    args: impl Iterator<Item = Argument<'db, 'a>>,
    add_issue: impl Fn(IssueType),
    skip_first_param: bool,
    result_context: &mut ResultContext,
    on_type_error: Option<OnTypeError<'db, '_>>,
) -> CalculatedTypeArguments {
    let func_or_callable = FunctionOrCallable::Callable(callable);
    let type_vars = &callable.content.type_vars;
    calculate_type_vars(
        i_s,
        get_matcher(
            None,
            func_or_callable,
            callable.content.defined_at,
            None,
            type_vars,
        ),
        func_or_callable,
        None,
        args,
        add_issue,
        skip_first_param,
        type_vars,
        callable.content.defined_at,
        result_context,
        on_type_error,
    )
}

fn get_matcher<'a>(
    class: Option<&'a Class>,
    func_or_callable: FunctionOrCallable<'a>,
    match_in_definition: PointLink,
    replace_self: Option<ReplaceSelf<'a>>,
    type_vars: &TypeVarLikes,
) -> Matcher<'a> {
    let matcher =
        (!type_vars.is_empty()).then(|| TypeVarMatcher::new(match_in_definition, type_vars.len()));
    Matcher::new(class, func_or_callable, matcher, replace_self)
}

fn calculate_type_vars<'db: 'a, 'a>(
    i_s: &InferenceState<'db, '_>,
    mut matcher: Matcher,
    func_or_callable: FunctionOrCallable<'a>,
    return_class: Option<&Class>,
    mut args: impl Iterator<Item = Argument<'db, 'a>>,
    add_issue: impl Fn(IssueType),
    skip_first_param: bool,
    type_vars: &TypeVarLikes,
    match_in_definition: PointLink,
    result_context: &mut ResultContext,
    on_type_error: Option<OnTypeError<'db, '_>>,
) -> CalculatedTypeArguments {
    if matcher.type_var_matcher.is_some() {
        let add_init_generics = |matcher: &mut _, return_class: &Class| {
            if let Some(t) = func_or_callable.first_self_or_class_annotation(i_s) {
                // When an __init__ has a self annotation, it's a bit special, because it influences
                // the generics.
                let func_class = func_or_callable.class().unwrap();
                if !Class::with_self_generics(i_s.db, return_class.node_ref)
                    .as_type(i_s.db)
                    .is_sub_type_of(i_s, matcher, &t)
                    .bool()
                {
                    todo!()
                }
                for entry in &mut matcher
                    .type_var_matcher
                    .as_mut()
                    .unwrap()
                    .calculated_type_vars
                {
                    entry.avoid_type_vars_from_class_self_arguments(func_class);
                }
            }
        };
        if let Some(return_class) = return_class {
            add_init_generics(&mut matcher, return_class)
        }
        result_context.with_type_if_exists_and_replace_type_var_likes(i_s, |expected| {
            if let Some(return_class) = return_class {
                // This is kind of a special case. Since __init__ has no return annotation, we simply
                // check if the classes match and then push the generics there.
                let type_var_likes = return_class.type_vars(i_s);
                if !type_var_likes.is_empty() {
                    debug_assert!(matches!(return_class.generics, Generics::NotDefinedYet));
                    if Class::with_self_generics(i_s.db, return_class.node_ref)
                        .as_type(i_s.db)
                        .is_sub_type_of(i_s, &mut matcher, expected)
                        .bool()
                    {
                        for calculated in matcher.iter_calculated_type_vars() {
                            let has_any = match &calculated.type_ {
                                BoundKind::TypeVar(
                                    TypeVarBound::Invariant(t)
                                    | TypeVarBound::Upper(t)
                                    | TypeVarBound::Lower(t),
                                ) => t.has_any(i_s),
                                BoundKind::TypeVar(TypeVarBound::UpperAndLower(t1, t2)) => {
                                    t1.has_any(i_s) | t2.has_any(i_s)
                                }
                                BoundKind::TypeVarTuple(ts) => ts.args.has_any(i_s),
                                BoundKind::ParamSpecArgument(params) => match &params.params {
                                    CallableParams::Simple(params) => params.iter().any(|t| {
                                        t.type_.maybe_type().is_some_and(|t| t.has_any(i_s))
                                    }),
                                    CallableParams::WithParamSpec(pre, _) => {
                                        pre.iter().any(|t| t.has_any(i_s))
                                    }
                                    CallableParams::Any(_) => true,
                                },
                                BoundKind::Uncalculated { .. } => {
                                    // Make sure that the fallback is never used from a context.
                                    calculated.type_ = BoundKind::Uncalculated { fallback: None };
                                    continue;
                                }
                            };
                            if has_any {
                                calculated.type_ = BoundKind::Uncalculated { fallback: None }
                            } else {
                                calculated.defined_by_result_context = true;
                            }
                        }
                    } else {
                        for calculated in matcher.iter_calculated_type_vars() {
                            calculated.type_ = BoundKind::Uncalculated { fallback: None }
                        }
                        add_init_generics(&mut matcher, return_class)
                    }
                }
            } else {
                let return_type = func_or_callable.return_type(i_s);
                // Fill the type var arguments from context
                return_type.is_sub_type_of(i_s, &mut matcher, expected);
                for calculated in matcher.iter_calculated_type_vars() {
                    let has_any = match &calculated.type_ {
                        BoundKind::TypeVar(
                            TypeVarBound::Invariant(t)
                            | TypeVarBound::Upper(t)
                            | TypeVarBound::Lower(t),
                        ) => t.has_any(i_s),
                        BoundKind::TypeVar(TypeVarBound::UpperAndLower(t1, t2)) => {
                            t1.has_any(i_s) | t2.has_any(i_s)
                        }
                        BoundKind::TypeVarTuple(ts) => ts.args.has_any(i_s),
                        BoundKind::ParamSpecArgument(params) => match &params.params {
                            CallableParams::Simple(params) => todo!(),
                            CallableParams::WithParamSpec(pre, _) => {
                                pre.iter().any(|t| t.has_any(i_s))
                            }
                            CallableParams::Any(_) => true,
                        },
                        BoundKind::Uncalculated { .. } => {
                            // Make sure that the fallback is never used from a context.
                            calculated.type_ = BoundKind::Uncalculated { fallback: None };
                            continue;
                        }
                    };
                    if has_any {
                        calculated.type_ = BoundKind::Uncalculated { fallback: None }
                    } else {
                        calculated.defined_by_result_context = true;
                    }
                }
            }
        });
    }
    let matches = match func_or_callable {
        FunctionOrCallable::Function(function) => calculate_type_vars_for_params(
            i_s,
            &mut matcher,
            func_or_callable,
            &add_issue,
            on_type_error,
            function.iter_args_with_params(i_s.db, args, skip_first_param),
        ),
        FunctionOrCallable::Callable(callable) => match &callable.content.params {
            CallableParams::Simple(params) => calculate_type_vars_for_params(
                i_s,
                &mut matcher,
                func_or_callable,
                &add_issue,
                on_type_error,
                InferrableParamIterator::new(
                    i_s.db,
                    params.iter().skip(skip_first_param as usize),
                    args,
                ),
            ),
            CallableParams::Any(_) => SignatureMatch::new_true(),
            CallableParams::WithParamSpec(pre_types, param_spec) => {
                if !pre_types.is_empty() {
                    //dbg!(pre_types, args.collect::<Vec<_>>());
                    //todo!()
                    debug!("TODO we should match param spec pre types?");
                }
                if let Some(arg) = args.next() {
                    if let ArgumentKind::ParamSpec { usage, .. } = &arg.kind {
                        if usage.in_definition == param_spec.in_definition {
                            SignatureMatch::new_true()
                        } else {
                            SignatureMatch::False { similar: false }
                        }
                    } else {
                        debug!("TODO is this ok param spec false?");
                        SignatureMatch::False { similar: false }
                    }
                } else {
                    todo!()
                }
            }
        },
    };
    let type_arguments = matcher.into_generics_list(i_s.db, type_vars);
    if cfg!(feature = "zuban_debug") {
        if let Some(type_arguments) = &type_arguments {
            let callable_description: String;
            debug!(
                "Calculated type vars for {}: [{}]",
                func_or_callable
                    .diagnostic_string(i_s.db)
                    .as_deref()
                    .unwrap_or("function"),
                type_arguments.format(&FormatData::new_short(i_s.db)),
            );
        }
    }
    CalculatedTypeArguments {
        in_definition: match_in_definition,
        matches,
        type_arguments,
    }
}

pub(crate) fn match_arguments_against_params<
    'db: 'x,
    'x,
    P: Param<'x>,
    AI: Iterator<Item = Argument<'db, 'x>>,
>(
    i_s: &InferenceState<'db, '_>,
    matcher: &mut Matcher,
    func_or_callable: FunctionOrCallable,
    add_issue: &impl Fn(IssueType),
    on_type_error: Option<OnTypeError<'db, '_>>,
    mut args_with_params: InferrableParamIterator<'db, 'x, impl Iterator<Item = P>, P, AI>,
) -> SignatureMatch {
    let diagnostic_string = |prefix: &str| {
        (on_type_error.unwrap().generate_diagnostic_string)(&func_or_callable, i_s.db)
            .map(|s| (prefix.to_owned() + &s).into())
    };
    let should_generate_errors = on_type_error.is_some();
    let mut missing_params = vec![];
    let mut missing_unpacked_typed_dict_names: Option<Vec<_>> = None;
    let mut argument_indices_with_any = vec![];
    let mut matches = Match::new_true();
    for (i, p) in args_with_params.by_ref().enumerate() {
        if matches!(p.argument, ParamArgument::None) && !p.param.has_default() {
            matches = Match::new_false();
            if should_generate_errors {
                missing_params.push(p.param);
            }
            debug!("Arguments for {:?} missing", p.param.name(i_s.db));
            continue;
        }
        let mut match_arg = |argument: Argument<'db, '_>, expected: Cow<Type>| {
            let value = if matcher.might_have_defined_type_vars() {
                argument.infer(
                    i_s,
                    &mut ResultContext::WithMatcher {
                        type_: &expected,
                        matcher,
                    },
                )
            } else {
                argument.infer(i_s, &mut ResultContext::Known(&expected))
            };
            let value_t = value.as_cow_type(i_s);
            let m = expected.is_super_type_of(i_s, matcher, &value_t);
            if let Match::False { reason, .. } = &m {
                debug!(
                    "Mismatch between {:?} and {:?} -> {:?}",
                    value_t.format_short(i_s.db),
                    expected.format_short(i_s.db),
                    &matches
                );
                if let Some(on_type_error) = on_type_error {
                    let node_ref = argument.as_node_ref();
                    let mut got = GotType::Type(&value_t);
                    if let Some(starred) = node_ref.maybe_starred_expression() {
                        got = GotType::Starred(
                            node_ref
                                .file
                                .inference(i_s)
                                .infer_expression(starred.expression())
                                .as_type(i_s),
                        )
                    } else if let Some(double_starred) = node_ref.maybe_double_starred_expression()
                    {
                        // If we have a defined kwargs name, that's from a TypedDict and
                        // shouldn't be formatted.
                        if !matches!(
                            &argument.kind,
                            ArgumentKind::Inferred {
                                is_keyword: Some(Some(_)),
                                ..
                            }
                        ) {
                            got = GotType::DoubleStarred(
                                node_ref
                                    .file
                                    .inference(i_s)
                                    .infer_expression(double_starred.expression())
                                    .as_type(i_s),
                            )
                        }
                    }
                    match reason {
                        MismatchReason::ConstraintMismatch { expected, type_var } => {
                            node_ref.add_issue(
                                i_s,
                                IssueType::InvalidTypeVarValue {
                                    type_var_name: Box::from(type_var.name(i_s.db)),
                                    of: diagnostic_string("").unwrap_or(Box::from("function")),
                                    actual: expected.format(&FormatData::new_short(i_s.db)),
                                },
                            );
                        }
                        _ => {
                            let error_types = ErrorTypes {
                                matcher,
                                reason,
                                got,
                                expected: &expected,
                            };
                            (on_type_error.callback)(
                                i_s,
                                &diagnostic_string,
                                &argument,
                                error_types,
                            )
                        }
                    };
                }
            }
            if let Type::Type(type_) = expected.as_ref() {
                if let Some(cls) = type_.maybe_class(i_s.db) {
                    if cls.is_protocol(i_s.db) {
                        if let Some(link) = value.maybe_saved_link() {
                            let node_ref = NodeRef::from_link(i_s.db, link);
                            if node_ref.maybe_class().is_some() {
                                let cls2 = Class::from_non_generic_node_ref(node_ref);
                                if cls2.is_protocol(i_s.db) {
                                    add_issue(
                                        IssueType::OnlyConcreteClassAllowedWhereTypeExpected {
                                            type_: expected.format_short(i_s.db),
                                        },
                                    )
                                }
                            }
                        }
                    }
                }
            }
            if matches!(m, Match::True { with_any: true }) {
                argument_indices_with_any.push(ArgumentIndexWithParam {
                    argument_index: argument.index,
                    type_: expected.into_owned(),
                })
            }
            matches &= m
        };
        match p.argument {
            ParamArgument::Argument(argument) => {
                let specific = p.param.specific(i_s.db);
                let expected = match specific {
                    WrappedParamType::PositionalOnly(t)
                    | WrappedParamType::PositionalOrKeyword(t)
                    | WrappedParamType::KeywordOnly(t)
                    | WrappedParamType::Star(WrappedStar::ArbitraryLength(t))
                    | WrappedParamType::StarStar(WrappedStarStar::ValueType(t)) => match t {
                        Some(t) => t,
                        None => continue,
                    },
                    WrappedParamType::StarStar(WrappedStarStar::UnpackTypedDict(td)) => {
                        todo!()
                    }
                    WrappedParamType::Star(WrappedStar::ParamSpecArgs(_))
                    | WrappedParamType::StarStar(WrappedStarStar::ParamSpecKwargs(_)) => {
                        todo!()
                    }
                };
                match_arg(argument, expected)
            }
            ParamArgument::ParamSpecArgs(param_spec, args) => {
                matches &= match matcher.match_param_spec_arguments(
                    i_s,
                    &param_spec,
                    args,
                    func_or_callable,
                    add_issue,
                    on_type_error,
                ) {
                    SignatureMatch::True { .. } => Match::new_true(),
                    SignatureMatch::TrueWithAny { .. } => todo!(),
                    SignatureMatch::False { similar } => Match::False {
                        similar,
                        reason: MismatchReason::None,
                    },
                }
            }
            ParamArgument::MatchedUnpackedTypedDictMember {
                argument,
                type_,
                name,
            } => {
                // Checking totality for **Unpack[<TypedDict>]
                if let Some(m) = missing_unpacked_typed_dict_names.as_mut() {
                    m.retain(|n| *n != name)
                } else {
                    let WrappedParamType::StarStar(WrappedStarStar::UnpackTypedDict(td))
                        = p.param.specific(i_s.db) else {
                        unreachable!();
                    };
                    // Just fill the dict with all names and then remove them gradually.
                    missing_unpacked_typed_dict_names = Some(
                        td.members(i_s.db)
                            .iter()
                            .filter(|m| m.name != name && m.required)
                            .map(|m| m.name)
                            .collect(),
                    );
                }
                match_arg(argument, Cow::Owned(type_))
            }
            ParamArgument::None => (),
        }
    }
    let add_keyword_argument_issue = |arg: &Argument, name: &str| {
        let reference = arg.as_node_ref();
        let s = match func_or_callable.has_keyword_param_with_name(i_s.db, name) {
            true => format!(
                "{} gets multiple values for keyword argument \"{name}\"",
                diagnostic_string("").as_deref().unwrap_or("function"),
            ),
            false => {
                if reference.maybe_double_starred_expression().is_some() {
                    format!(
                        "Extra argument \"{name}\" from **args{}",
                        diagnostic_string(" for ").as_deref().unwrap_or(""),
                    )
                } else {
                    format!(
                        "Unexpected keyword argument \"{name}\"{}",
                        diagnostic_string(" for ").as_deref().unwrap_or(""),
                    )
                }
            }
        };
        arg.add_issue(i_s, IssueType::ArgumentIssue(s.into()));
    };
    if args_with_params.too_many_positional_arguments {
        matches = Match::new_false();
        if should_generate_errors {
            let mut s = "Too many positional arguments".to_owned();
            s += diagnostic_string(" for ").as_deref().unwrap_or("");
            add_issue(IssueType::ArgumentIssue(s.into()));
        }
    } else if args_with_params.has_unused_arguments() {
        matches = Match::new_false();
        if should_generate_errors {
            let mut too_many = false;
            while let Some(arg) = args_with_params.next_arg() {
                if let Some(key) = arg.keyword_name(i_s.db) {
                    add_keyword_argument_issue(&arg, key)
                } else {
                    too_many = true;
                    break;
                }
            }
            if too_many {
                let s = diagnostic_string(" for ").unwrap_or_else(|| Box::from(""));
                add_issue(IssueType::TooManyArguments(s));
            }
        } else {
            debug!("Too many arguments found");
        }
    } else if args_with_params.has_unused_keyword_arguments() {
        matches = Match::new_false();
        if should_generate_errors {
            for unused in &args_with_params.unused_keyword_arguments {
                if let Some(key) = unused.keyword_name(i_s.db) {
                    add_keyword_argument_issue(unused, key)
                } else {
                    unreachable!();
                }
            }
        }
    } else if should_generate_errors {
        let mut missing_positional = vec![];
        let add_missing_kw_issue = |param_name| {
            let mut s = format!("Missing named argument {:?}", param_name);
            s += diagnostic_string(" for ").as_deref().unwrap_or("");
            add_issue(IssueType::ArgumentIssue(s.into()));
        };
        for param in &missing_params {
            let param_kind = param.kind(i_s.db);
            if let Some(param_name) = param
                .name(i_s.db)
                .filter(|_| param_kind != ParamKind::PositionalOnly)
            {
                if param_kind == ParamKind::KeywordOnly {
                    add_missing_kw_issue(param_name)
                } else {
                    missing_positional.push(format!("\"{param_name}\""));
                }
            } else {
                let s = diagnostic_string(" for ").unwrap_or_else(|| Box::from(""));
                add_issue(IssueType::TooFewArguments(s));
                break;
            }
        }
        if let Some(missing_unpacked_typed_dict_names) = missing_unpacked_typed_dict_names {
            for missing in missing_unpacked_typed_dict_names {
                add_missing_kw_issue(missing.as_str(i_s.db))
            }
        }
        if let Some(mut s) = match &missing_positional[..] {
            [] => None,
            [param_name] => Some(format!(
                "Missing positional argument {} in call",
                param_name
            )),
            _ => Some(format!(
                "Missing positional arguments {} in call",
                missing_positional.join(", ")
            )),
        } {
            s += diagnostic_string(" to ").as_deref().unwrap_or("");
            add_issue(IssueType::ArgumentIssue(s.into()));
        };
    } else if missing_unpacked_typed_dict_names.is_some_and(|t| !t.is_empty()) {
        matches = Match::new_false()
    }
    match matches {
        Match::True { with_any: false } => SignatureMatch::True {
            arbitrary_length_handled: args_with_params.had_arbitrary_length_handled(),
        },
        Match::True { with_any: true } => SignatureMatch::TrueWithAny {
            argument_indices: argument_indices_with_any.into(),
        },
        Match::False { similar, .. } => SignatureMatch::False { similar },
    }
}

fn calculate_type_vars_for_params<
    'db: 'x,
    'x,
    P: Param<'x>,
    AI: Iterator<Item = Argument<'db, 'x>>,
>(
    i_s: &InferenceState<'db, '_>,
    matcher: &mut Matcher,
    func_or_callable: FunctionOrCallable,
    add_issue: &impl Fn(IssueType),
    on_type_error: Option<OnTypeError<'db, '_>>,
    args_with_params: InferrableParamIterator<'db, 'x, impl Iterator<Item = P>, P, AI>,
) -> SignatureMatch {
    match_arguments_against_params(
        i_s,
        matcher,
        func_or_callable,
        add_issue,
        on_type_error,
        args_with_params,
    )
}
