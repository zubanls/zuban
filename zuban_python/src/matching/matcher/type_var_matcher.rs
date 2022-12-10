use std::borrow::Cow;

use parsa_python_ast::ParamKind;

use super::super::params::{
    InferrableParamIterator2, Param, ParamArgument, WrappedDoubleStarred, WrappedParamSpecific,
    WrappedStarred,
};
use super::super::{
    ArgumentIndexWithParam, FormatData, Generic, Generics, Match, Matcher, MismatchReason,
    ResultContext, SignatureMatch, Type,
};
use super::bound::TypeVarBound;
use crate::arguments::{ArgumentIterator, ArgumentKind, Arguments};
use crate::database::{
    CallableContent, CallableParams, DbType, GenericItem, GenericsList, ParamSpecArgument,
    PointLink, TupleTypeArguments, TypeArguments, TypeOrTypeVarTuple, TypeVarLike,
    TypeVarLikeUsage, TypeVarLikes,
};
use crate::debug;
use crate::diagnostics::IssueType;
use crate::inference_state::InferenceState;
use crate::node_ref::NodeRef;
use crate::value::{Class, Function, OnTypeError, Value};

#[derive(Debug, Clone, Copy)]
pub enum FunctionOrCallable<'a> {
    Function(Function<'a>),
    Callable(&'a CallableContent),
}

#[derive(Debug)]
pub enum BoundKind {
    TypeVar(TypeVarBound),
    TypeVarTuple(TypeArguments),
    ParamSpecArgument(ParamSpecArgument),
    Uncalculated,
}

impl Default for BoundKind {
    fn default() -> Self {
        Self::Uncalculated
    }
}

#[derive(Debug, Default)]
pub struct CalculatedTypeVarLike {
    pub(super) type_: BoundKind,
    pub(super) defined_by_result_context: bool,
}

fn common_base_class<'x, I: Iterator<Item = &'x TypeOrTypeVarTuple>>(
    i_s: &mut InferenceState,
    mut ts: I,
) -> DbType {
    if let Some(first) = ts.next() {
        let mut result = match first {
            TypeOrTypeVarTuple::Type(t) => Cow::Borrowed(t),
            TypeOrTypeVarTuple::TypeVarTuple(_) => return i_s.db.python_state.object_db_type(),
        };
        for t in ts {
            let t = match t {
                TypeOrTypeVarTuple::Type(t) => t,
                TypeOrTypeVarTuple::TypeVarTuple(_) => return i_s.db.python_state.object_db_type(),
            };
            result = Cow::Owned(Type::Type(result).common_base_class(i_s, &Type::new(t)));
        }
        result.into_owned()
    } else {
        todo!("should probably return never")
    }
}

impl CalculatedTypeVarLike {
    pub fn calculated(&self) -> bool {
        !matches!(self.type_, BoundKind::Uncalculated)
    }

    pub fn merge_fixed_length_type_var_tuple<'x, I: Iterator<Item = &'x TypeOrTypeVarTuple>>(
        &mut self,
        i_s: &mut InferenceState,
        fetch: usize,
        items: I,
    ) {
        match &mut self.type_ {
            BoundKind::TypeVarTuple(ts) => match &mut ts.args {
                TupleTypeArguments::FixedLength(calc_ts) => {
                    if fetch == calc_ts.len() {
                        for (t1, t2) in calc_ts.iter_mut().zip(items) {
                            match (t1, t2) {
                                (TypeOrTypeVarTuple::Type(t1), TypeOrTypeVarTuple::Type(t2)) => {
                                    *t1 = Type::new(t1).common_base_class(i_s, &Type::new(t2));
                                }
                                _ => todo!(),
                            }
                        }
                    } else {
                        // We use map to make an iterator with covariant lifetimes.
                        #[allow(clippy::map_identity)]
                        let t = common_base_class(i_s, calc_ts.iter().chain(items.map(|x| x)));
                        ts.args = TupleTypeArguments::ArbitraryLength(Box::new(t));
                    }
                }
                TupleTypeArguments::ArbitraryLength(calc_t) => {
                    let base = common_base_class(i_s, items);
                    //self.merge_arbitrary_length_type_var_tuple(i_s, &base)
                }
            },
            _ => unreachable!(),
        }
    }

    pub fn merge_arbitrary_length_type_var_tuple(
        &mut self,
        i_s: &mut InferenceState,
        item: &DbType,
    ) {
        todo!()
    }
}

#[derive(Debug)]
pub struct TypeVarMatcher<'a> {
    pub(super) class: Option<&'a Class<'a>>,
    pub(super) func_or_callable: FunctionOrCallable<'a>,
    pub(super) calculated_type_vars: &'a mut [CalculatedTypeVarLike],
    pub(super) match_in_definition: PointLink,
    pub(super) parent_matcher: Option<&'a mut Self>,
    pub match_reverse: bool, // For contravariance subtypes
}

impl<'a> TypeVarMatcher<'a> {
    pub fn new(
        class: Option<&'a Class<'a>>,
        func_or_callable: FunctionOrCallable<'a>,
        match_in_definition: PointLink,
        calculated_type_vars: &'a mut [CalculatedTypeVarLike],
        //parent_matcher: Option<&'a mut Self>,
    ) -> Self {
        Self {
            class,
            func_or_callable,
            calculated_type_vars,
            match_in_definition,
            match_reverse: false,
            parent_matcher: None, //parent_matcher,
        }
    }

    pub(super) fn class(&self) -> Option<Class<'_>> {
        // Currently this is used for formatting, but it probably shouldn't be.
        match self.func_or_callable {
            FunctionOrCallable::Function(func) => func.class,
            FunctionOrCallable::Callable(_) => None,
        }
    }

    pub fn set_all_contained_type_vars_to_any(&mut self, i_s: &mut InferenceState, type_: &DbType) {
        type_.search_type_vars(&mut |t| {
            if t.in_definition() == self.match_in_definition {
                let current = &mut self.calculated_type_vars[t.index().as_usize()];
                if !current.calculated() {
                    current.type_ = match t {
                        TypeVarLikeUsage::TypeVar(_) => {
                            BoundKind::TypeVar(TypeVarBound::Invariant(DbType::Any))
                        }
                        TypeVarLikeUsage::TypeVarTuple(_) => BoundKind::TypeVarTuple(
                            TypeArguments::new_arbitrary_length(DbType::Any),
                        ),
                        TypeVarLikeUsage::ParamSpec(_) => {
                            BoundKind::ParamSpecArgument(ParamSpecArgument::new_any())
                        }
                    }
                }
            }
        });
    }

    pub fn replace_type_var_likes_for_nested_context(
        &self,
        i_s: &mut InferenceState,
        t: &DbType,
    ) -> DbType {
        t.replace_type_var_likes(&mut |type_var_like_usage| {
            if type_var_like_usage.in_definition() == self.match_in_definition {
                let current = &self.calculated_type_vars[type_var_like_usage.index().as_usize()];
                match &current.type_ {
                    BoundKind::TypeVar(t) => GenericItem::TypeArgument(t.clone().into_db_type()),
                    BoundKind::TypeVarTuple(_) => todo!(),
                    BoundKind::ParamSpecArgument(params) => todo!(),
                    // Any is just ignored by the context later.
                    BoundKind::Uncalculated => {
                        type_var_like_usage.as_type_var_like().as_any_generic_item()
                    }
                }
            } else {
                match self.func_or_callable {
                    FunctionOrCallable::Function(f) => {
                        if let Some(class) = self.class {
                            if class.node_ref.as_link() == type_var_like_usage.in_definition() {
                                return class
                                    .generics
                                    .nth_usage(i_s, &type_var_like_usage)
                                    .into_generic_item(i_s);
                            }
                            let func_class = f.class.unwrap();
                            if type_var_like_usage.in_definition() == func_class.node_ref.as_link()
                            {
                                let type_var_remap = func_class.type_var_remap.unwrap();
                                match &type_var_remap[type_var_like_usage.index()] {
                                    GenericItem::TypeArgument(t) => GenericItem::TypeArgument(
                                        self.replace_type_var_likes_for_nested_context(i_s, t),
                                    ),
                                    GenericItem::TypeArguments(_) => todo!(),
                                    GenericItem::ParamSpecArgument(_) => todo!(),
                                }
                            } else {
                                type_var_like_usage.into_generic_item()
                            }
                        } else {
                            todo!()
                        }
                    }
                    FunctionOrCallable::Callable(c) => todo!(),
                }
            }
        })
    }
}

pub fn calculate_class_init_type_vars_and_return<'db>(
    i_s: &mut InferenceState<'db, '_>,
    class: &Class,
    function: Function,
    args: &dyn Arguments<'db>,
    result_context: &mut ResultContext,
    on_type_error: Option<OnTypeError<'db, '_>>,
) -> CalculatedTypeArguments {
    debug!(
        "Calculate type vars for class {} ({})",
        class.name(),
        function.name(),
    );
    let has_generics = !matches!(class.generics, Generics::None | Generics::Any);
    let type_vars = class.type_vars(i_s);
    // Function type vars need to be calculated, so annotations are used.
    let func_type_vars = function.type_vars(i_s);
    if has_generics {
        let mut type_arguments = calculate_type_vars(
            i_s,
            Some(class),
            FunctionOrCallable::Function(function),
            None,
            args,
            true,
            func_type_vars,
            function.node_ref.as_link(),
            result_context,
            on_type_error,
        );
        type_arguments.type_arguments = class.generics_as_list(i_s);
        type_arguments
    } else {
        calculate_type_vars(
            i_s,
            Some(class),
            FunctionOrCallable::Function(function),
            Some(class),
            args,
            true,
            type_vars,
            class.node_ref.as_link(),
            result_context,
            on_type_error,
        )
    }
}

pub struct CalculatedTypeArguments {
    pub in_definition: PointLink,
    pub matches: SignatureMatch,
    pub type_arguments: Option<GenericsList>,
}

impl CalculatedTypeArguments {
    pub fn lookup_type_var_usage(
        &self,
        i_s: &mut InferenceState,
        class: Option<&Class>,
        usage: TypeVarLikeUsage,
    ) -> GenericItem {
        if self.in_definition == usage.in_definition() {
            return if let Some(fm) = &self.type_arguments {
                fm[usage.index()].clone()
            } else {
                // TODO we are just passing the type vars again. Does this make sense?
                // GenericItem::TypeArgument(DbType::TypeVar(usage.clone()))
                todo!()
            };
        }
        if let Some(c) = class {
            if usage.in_definition() == c.node_ref.as_link() {
                return c.generics().nth_usage(i_s, &usage).into_generic_item(i_s);
            }
        }
        usage.into_generic_item()
    }
}

pub fn calculate_function_type_vars_and_return<'db>(
    i_s: &mut InferenceState<'db, '_>,
    class: Option<&Class>,
    function: Function,
    args: &dyn Arguments<'db>,
    skip_first_param: bool,
    type_vars: Option<&TypeVarLikes>,
    match_in_definition: PointLink,
    result_context: &mut ResultContext,
    on_type_error: Option<OnTypeError<'db, '_>>,
) -> CalculatedTypeArguments {
    debug!(
        "Calculate type vars for {} in {}",
        function.name(),
        class.map(|c| c.name()).unwrap_or("-")
    );
    calculate_type_vars(
        i_s,
        class,
        FunctionOrCallable::Function(function),
        None,
        args,
        skip_first_param,
        type_vars,
        match_in_definition,
        result_context,
        on_type_error,
    )
}

pub fn calculate_callable_type_vars_and_return<'db>(
    i_s: &mut InferenceState<'db, '_>,
    class: Option<&Class>,
    callable: &CallableContent,
    args: &dyn Arguments<'db>,
    result_context: &mut ResultContext,
    on_type_error: OnTypeError<'db, '_>,
) -> CalculatedTypeArguments {
    calculate_type_vars(
        i_s,
        None,
        FunctionOrCallable::Callable(callable),
        None,
        args,
        false,
        callable.type_vars.as_ref(),
        callable.defined_at,
        result_context,
        Some(on_type_error),
    )
}

fn calculate_type_vars<'db>(
    i_s: &mut InferenceState<'db, '_>,
    class: Option<&Class>,
    func_or_callable: FunctionOrCallable,
    expected_return_class: Option<&Class>,
    args: &dyn Arguments<'db>,
    skip_first_param: bool,
    type_vars: Option<&TypeVarLikes>,
    match_in_definition: PointLink,
    result_context: &mut ResultContext,
    on_type_error: Option<OnTypeError<'db, '_>>,
) -> CalculatedTypeArguments {
    // We could allocate on stack as described here:
    // https://stackoverflow.com/questions/27859822/is-it-possible-to-have-stack-allocated-arrays-with-the-size-determined-at-runtim
    let type_vars_len = match type_vars {
        Some(type_vars) => type_vars.len(),
        None => 0,
    };
    let mut calculated_type_vars = vec![];
    calculated_type_vars.resize_with(type_vars_len, Default::default);
    let mut used_type_vars = type_vars;
    let matcher = match type_vars {
        Some(type_vars) => Some(TypeVarMatcher::new(
            class,
            func_or_callable,
            match_in_definition,
            &mut calculated_type_vars,
        )),
        None => {
            if let FunctionOrCallable::Function(function) = func_or_callable {
                if let Some(func_class) = function.class {
                    used_type_vars = func_class.type_vars(i_s);
                    used_type_vars.map(|_| {
                        TypeVarMatcher::new(
                            class,
                            func_or_callable,
                            match_in_definition,
                            &mut calculated_type_vars, // TODO There are no type vars in there, should set it to 0
                        )
                    })
                } else {
                    None
                }
            } else {
                None
            }
        }
    };
    let mut matcher = Matcher::new(matcher);
    if matcher.has_type_var_matcher() {
        result_context.with_type_if_exists_and_replace_type_var_likes(i_s, |i_s, type_| {
            if let Some(class) = expected_return_class {
                // This is kind of a special case. Since __init__ has no return annotation, we simply
                // check if the classes match and then push the generics there.
                if let Some(type_vars) = class.type_vars(i_s) {
                    type_.on_any_class(
                        i_s,
                        &mut Matcher::default(),
                        &mut |i_s, _, result_class| {
                            if result_class.node_ref == class.node_ref {
                                let mut calculating = matcher.iter_calculated_type_vars();
                                for (type_var_like, g) in type_vars
                                    .iter()
                                    .zip(result_class.generics().iter(i_s.clone()))
                                {
                                    let calculated = calculating.next().unwrap();
                                    match g {
                                        Generic::TypeArgument(g) => {
                                            if !g.is_any() {
                                                let mut bound = TypeVarBound::new(
                                                    g.as_db_type(i_s),
                                                    match type_var_like {
                                                        TypeVarLike::TypeVar(t) => t.variance,
                                                        _ => unreachable!(),
                                                    },
                                                );
                                                bound.invert_bounds();
                                                calculated.type_ = BoundKind::TypeVar(bound);
                                                calculated.defined_by_result_context = true;
                                            }
                                        }
                                        Generic::TypeVarTuple(ts) => {
                                            calculated.type_ =
                                                BoundKind::TypeVarTuple(ts.into_owned());
                                            calculated.defined_by_result_context = true;
                                        }
                                        Generic::ParamSpecArgument(p) => {
                                            calculated.type_ =
                                                BoundKind::ParamSpecArgument(p.into_owned());
                                            calculated.defined_by_result_context = true;
                                        }
                                    };
                                }
                                true
                            } else {
                                false
                            }
                        },
                    );
                }
            } else {
                let result_type = match func_or_callable {
                    FunctionOrCallable::Function(f) => f.result_type(i_s),
                    FunctionOrCallable::Callable(c) => Type::new(&c.result_type),
                };
                // Fill the type var arguments from context
                result_type.is_sub_type_of(i_s, &mut matcher, type_);
                for calculated in matcher.iter_calculated_type_vars() {
                    let has_any = match &calculated.type_ {
                        BoundKind::TypeVar(
                            TypeVarBound::Invariant(t)
                            | TypeVarBound::Lower(t)
                            | TypeVarBound::Upper(t),
                        ) => t.has_any(),
                        BoundKind::TypeVar(TypeVarBound::LowerAndUpper(t1, t2)) => {
                            t1.has_any() | t2.has_any()
                        }
                        BoundKind::TypeVarTuple(ts) => ts.args.has_any(),
                        BoundKind::ParamSpecArgument(params) => todo!(),
                        BoundKind::Uncalculated => continue,
                    };
                    if has_any {
                        calculated.type_ = BoundKind::Uncalculated
                    } else {
                        calculated.defined_by_result_context = true;
                    }
                }
            }
        });
    }
    let matches = match func_or_callable {
        FunctionOrCallable::Function(function) => {
            // Make sure the type vars are properly pre-calculated, because we are using type
            // vars from in use_cached_annotation_type.
            function.type_vars(i_s);
            calculate_type_vars_for_params(
                i_s,
                &mut matcher,
                class,
                Some(&function),
                args,
                on_type_error,
                function.iter_args_with_params(i_s.db, args, skip_first_param),
            )
        }
        FunctionOrCallable::Callable(callable) => match &callable.params {
            CallableParams::Simple(params) => calculate_type_vars_for_params(
                i_s,
                &mut matcher,
                None,
                None,
                args,
                on_type_error,
                InferrableParamIterator2::new(i_s.db, params.iter(), args.iter_arguments()),
            ),
            CallableParams::Any => SignatureMatch::True,
            CallableParams::WithParamSpec(pre_types, param_spec) => {
                let mut args = args.iter_arguments();
                if !pre_types.is_empty() {
                    todo!()
                }
                if let Some(arg) = args.next() {
                    if let ArgumentKind::ParamSpec { usage, .. } = &arg.kind {
                        if usage.in_definition == param_spec.in_definition {
                            SignatureMatch::True
                        } else {
                            todo!()
                        }
                    } else {
                        todo!()
                    }
                } else {
                    todo!()
                }
            }
        },
    };
    let type_arguments = matcher.has_type_var_matcher().then(|| {
        GenericsList::new_generics(
            calculated_type_vars
                .into_iter()
                .zip(used_type_vars.unwrap().iter())
                .map(|(c, type_var_like)| match c.type_ {
                    BoundKind::TypeVar(t) => GenericItem::TypeArgument(t.into_db_type()),
                    BoundKind::TypeVarTuple(ts) => GenericItem::TypeArguments(ts),
                    BoundKind::ParamSpecArgument(params) => GenericItem::ParamSpecArgument(params),
                    BoundKind::Uncalculated => match type_var_like {
                        TypeVarLike::TypeVar(_) => GenericItem::TypeArgument(DbType::Never),
                        // TODO TypeVarTuple: this feels wrong, should maybe be never?
                        TypeVarLike::TypeVarTuple(_) => GenericItem::TypeArguments(
                            TypeArguments::new_fixed_length(Box::new([])),
                        ),
                        // TODO ParamSpec: this feels wrong, should maybe be never?
                        TypeVarLike::ParamSpec(_) => {
                            GenericItem::ParamSpecArgument(ParamSpecArgument::new_any())
                        }
                    },
                })
                .collect(),
        )
    });
    if cfg!(feature = "zuban_debug") {
        if let Some(type_arguments) = &type_arguments {
            let callable_description: String;
            debug!(
                "Calculated type vars: {}[{}]",
                match &func_or_callable {
                    FunctionOrCallable::Function(function) => function.name(),
                    FunctionOrCallable::Callable(callable) => {
                        callable_description = callable.format(&FormatData::new_short(i_s.db));
                        &callable_description
                    }
                },
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

pub fn match_arguments_against_params<
    'db: 'x,
    'x,
    'c,
    P: Param<'x>,
    AI: ArgumentIterator<'db, 'x>,
>(
    i_s: &mut InferenceState<'db, '_>,
    matcher: &mut Matcher,
    class: Option<&Class>,
    function: Option<&Function>,
    args_node_ref: &impl Fn() -> NodeRef<'c>,
    on_type_error: Option<OnTypeError<'db, '_>>,
    mut args_with_params: InferrableParamIterator2<'db, 'x, impl Iterator<Item = P>, P, AI>,
) -> SignatureMatch {
    let diagnostic_string =
        |prefix: &str| function.map(|f| (prefix.to_owned() + &f.diagnostic_string(class)).into());
    let should_generate_errors = on_type_error.is_some();
    let mut missing_params = vec![];
    let mut argument_indices_with_any = vec![];
    let mut matches = Match::new_true();
    for (i, p) in args_with_params.by_ref().enumerate() {
        if matches!(p.argument, ParamArgument::None) && !p.param.has_default() {
            matches = Match::new_false();
            if should_generate_errors {
                missing_params.push(p.param);
            }
            continue;
        }
        match p.argument {
            ParamArgument::Argument(ref argument) => {
                let specific = p.param.specific(i_s);
                let annotation_type = match &specific {
                    WrappedParamSpecific::PositionalOnly(t)
                    | WrappedParamSpecific::PositionalOrKeyword(t)
                    | WrappedParamSpecific::KeywordOnly(t)
                    | WrappedParamSpecific::Starred(WrappedStarred::ArbitraryLength(t))
                    | WrappedParamSpecific::DoubleStarred(WrappedDoubleStarred::ValueType(t)) => {
                        match t {
                            Some(t) => t,
                            None => continue,
                        }
                    }
                    WrappedParamSpecific::Starred(WrappedStarred::ParamSpecArgs(_))
                    | WrappedParamSpecific::DoubleStarred(WrappedDoubleStarred::ParamSpecKwargs(
                        _,
                    )) => {
                        unreachable!()
                    }
                };
                let value = if matcher.has_type_var_matcher() {
                    argument.infer(
                        i_s,
                        &mut ResultContext::WithMatcher {
                            type_: annotation_type,
                            matcher,
                        },
                    )
                } else {
                    argument.infer(i_s, &mut ResultContext::Known(annotation_type))
                };
                let m = annotation_type.error_if_not_matches_with_matcher(
                    i_s,
                    matcher,
                    &value,
                    on_type_error.as_ref().map(|on_type_error| {
                        |i_s: &mut InferenceState<'db, '_>, mut t1, t2, reason: &MismatchReason| {
                            let node_ref = argument.as_node_ref();
                            if let Some(starred) = node_ref.maybe_starred_expression() {
                                t1 = format!(
                                    "*{}",
                                    node_ref
                                        .file
                                        .inference(i_s)
                                        .infer_expression(starred.expression())
                                        .format(i_s, &FormatData::new_short(i_s.db))
                                )
                                .into()
                            } else if let Some(double_starred) =
                                node_ref.maybe_double_starred_expression()
                            {
                                t1 = format!(
                                    "**{}",
                                    node_ref
                                        .file
                                        .inference(i_s)
                                        .infer_expression(double_starred.expression())
                                        .format(i_s, &FormatData::new_short(i_s.db))
                                )
                                .into()
                            }
                            match reason {
                                MismatchReason::None => (on_type_error.callback)(
                                    i_s,
                                    class,
                                    &diagnostic_string,
                                    argument,
                                    t1,
                                    t2,
                                ),
                                MismatchReason::CannotInferTypeArgument(index) => {
                                    node_ref.add_typing_issue(
                                        i_s.db,
                                        IssueType::CannotInferTypeArgument {
                                            index: *index,
                                            callable: diagnostic_string("")
                                                .unwrap_or_else(|| Box::from("Callable")),
                                        },
                                    );
                                }
                                MismatchReason::ConstraintMismatch { expected, type_var } => {
                                    node_ref.add_typing_issue(
                                        i_s.db,
                                        IssueType::InvalidTypeVarValue {
                                            type_var_name: Box::from(type_var.name(i_s.db)),
                                            func: diagnostic_string("")
                                                .unwrap_or_else(|| Box::from("function")),
                                            actual: expected.format(&FormatData::new_short(i_s.db)),
                                        },
                                    );
                                }
                            }
                        }
                    }),
                );
                if matches!(m, Match::True { with_any: true }) {
                    if let Some(param_annotation_link) = p.param.func_annotation_link() {
                        // This is never reached when matching callables
                        argument_indices_with_any.push(ArgumentIndexWithParam {
                            argument_index: argument.index,
                            param_annotation_link,
                        })
                    }
                }
                matches &= m
            }
            ParamArgument::ParamSpecArgs(param_spec, args) => {
                matches &= match matcher.match_param_spec_arguments(
                    i_s,
                    &param_spec,
                    args,
                    class,
                    function,
                    args_node_ref,
                    on_type_error,
                ) {
                    SignatureMatch::True => Match::new_true(),
                    SignatureMatch::TrueWithAny { .. } => todo!(),
                    SignatureMatch::False { similar } => Match::False {
                        similar,
                        reason: MismatchReason::None,
                    },
                }
            }
            ParamArgument::None => (),
        }
    }
    let add_keyword_argument_issue = |reference: NodeRef, name| {
        let s = if let Some(function) = function {
            if function.iter_params().any(|p| {
                p.name(i_s.db) == Some(name)
                    && matches!(
                        p.kind(i_s.db),
                        ParamKind::PositionalOrKeyword | ParamKind::KeywordOnly
                    )
            }) {
                format!(
                    "{} gets multiple values for keyword argument {name:?}",
                    function.diagnostic_string(class),
                )
            } else {
                format!(
                    "Unexpected keyword argument {name:?} for {}",
                    function.diagnostic_string(class),
                )
            }
        } else {
            debug!("TODO this keyword param could also exist");
            format!("Unexpected keyword argument {name:?}")
        };
        reference.add_typing_issue(i_s.db, IssueType::ArgumentIssue(s.into()));
    };
    if args_with_params.too_many_positional_arguments {
        matches = Match::new_false();
        if should_generate_errors || true {
            // TODO remove true and add test
            let mut s = "Too many positional arguments".to_owned();
            s += diagnostic_string(" for ").as_deref().unwrap_or("");
            args_node_ref().add_typing_issue(i_s.db, IssueType::ArgumentIssue(s.into()));
        }
    } else if args_with_params.has_unused_arguments() {
        matches = Match::new_false();
        if should_generate_errors {
            let mut too_many = false;
            for arg in args_with_params.arguments {
                match arg.kind {
                    ArgumentKind::Keyword { key, node_ref, .. } => {
                        add_keyword_argument_issue(node_ref, key)
                    }
                    _ => {
                        too_many = true;
                        break;
                    }
                }
            }
            if too_many {
                let mut s = "Too many arguments".to_owned();
                s += diagnostic_string(" for ").as_deref().unwrap_or("");
                args_node_ref().add_typing_issue(i_s.db, IssueType::ArgumentIssue(s.into()));
            }
        }
    } else if args_with_params.has_unused_keyword_arguments() && should_generate_errors {
        for unused in args_with_params.unused_keyword_arguments {
            match unused.kind {
                ArgumentKind::Keyword { key, node_ref, .. } => {
                    add_keyword_argument_issue(node_ref, key)
                }
                _ => unreachable!(),
            }
        }
    } else if should_generate_errors {
        let mut missing_positional = vec![];
        for param in &missing_params {
            if let Some(param_name) = param.name(i_s.db) {
                if param.kind(i_s.db) == ParamKind::KeywordOnly {
                    let mut s = format!("Missing named argument {:?}", param_name);
                    s += diagnostic_string(" for ").as_deref().unwrap_or("");
                    args_node_ref().add_typing_issue(i_s.db, IssueType::ArgumentIssue(s.into()));
                } else {
                    missing_positional.push(format!("\"{param_name}\""));
                }
            } else {
                let mut s = "Too few arguments".to_owned();
                s += diagnostic_string(" for ").as_deref().unwrap_or("");
                args_node_ref().add_typing_issue(i_s.db, IssueType::ArgumentIssue(s.into()));
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
            args_node_ref().add_typing_issue(i_s.db, IssueType::ArgumentIssue(s.into()));
        };
    }
    match matches {
        Match::True { with_any: false } => SignatureMatch::True,
        Match::True { with_any: true } => SignatureMatch::TrueWithAny {
            argument_indices: argument_indices_with_any.into(),
        },
        Match::False { similar, .. } => SignatureMatch::False { similar },
    }
}

fn calculate_type_vars_for_params<'db: 'x, 'x, P: Param<'x>, AI: ArgumentIterator<'db, 'x>>(
    i_s: &mut InferenceState<'db, '_>,
    matcher: &mut Matcher,
    class: Option<&Class>,
    function: Option<&Function>,
    args: &dyn Arguments<'db>,
    on_type_error: Option<OnTypeError<'db, '_>>,
    args_with_params: InferrableParamIterator2<'db, 'x, impl Iterator<Item = P>, P, AI>,
) -> SignatureMatch {
    match_arguments_against_params(
        i_s,
        matcher,
        class,
        function,
        &|| args.as_node_ref(),
        on_type_error,
        args_with_params,
    )
}
