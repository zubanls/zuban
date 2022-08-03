use parsa_python_ast::ParamType;

use super::params::{InferrableParamIterator2, Param};
use super::{Match, ResultContext, SignatureMatch, Type};
use crate::arguments::{Argument, Arguments};
use crate::database::{
    DbType, FormatStyle, GenericsList, PointLink, TypeVar, TypeVarType, TypeVarUsage, TypeVars,
    Variance,
};
use crate::debug;
use crate::diagnostics::IssueType;
use crate::inference_state::InferenceState;
use crate::value::{Callable, Class, Function, OnTypeError, Value};

type OnConstraintMismatch<'db, 'a> =
    &'a mut dyn FnMut(&mut InferenceState<'db, '_>, &TypeVar, &Type<'db, '_>);
type OnCannotInferTypeArgument<'db, 'a> =
    &'a mut dyn FnMut(&mut InferenceState<'db, '_>, &TypeVarUsage);

#[derive(Debug, Clone, Copy)]
pub enum FunctionOrCallable<'db, 'a> {
    Function(Option<&'a Class<'db, 'a>>, Function<'db, 'a>),
    Callable(&'a Callable<'a>),
}

#[derive(Debug, Default)]
struct CalculatedTypeVar {
    type_: Option<DbType>,
    //variance: Variance,
    defined_by_result_type: bool,
}

pub struct TypeVarMatcher<'db, 'a> {
    pub func_or_callable: FunctionOrCallable<'db, 'a>,
    calculated_type_vars: &'a mut [CalculatedTypeVar],
    match_type: TypeVarType,
    match_in_definition: PointLink,
    on_constraint_mismatch: OnConstraintMismatch<'db, 'a>,
    on_cannot_infer_type_argument: OnCannotInferTypeArgument<'db, 'a>,
}

impl<'db, 'a> TypeVarMatcher<'db, 'a> {
    fn new(
        func_or_callable: FunctionOrCallable<'db, 'a>,
        match_type: TypeVarType,
        match_in_definition: PointLink,
        calculated_type_vars: &'a mut [CalculatedTypeVar],
        on_constraint_mismatch: OnConstraintMismatch<'db, 'a>,
        on_cannot_infer_type_argument: OnCannotInferTypeArgument<'db, 'a>,
    ) -> Self {
        Self {
            func_or_callable,
            calculated_type_vars,
            match_type,
            match_in_definition,
            on_constraint_mismatch,
            on_cannot_infer_type_argument,
        }
    }

    pub fn match_or_add_type_var(
        &mut self,
        i_s: &mut InferenceState<'db, '_>,
        type_var_usage: &TypeVarUsage,
        value_type: &Type<'db, '_>,
        variance: Variance,
    ) -> Match {
        let type_var = &type_var_usage.type_var;
        if type_var_usage.in_definition != self.match_in_definition {
            match self.func_or_callable {
                FunctionOrCallable::Function(class, f) => {
                    if let Some(class) = class {
                        if class.node_ref.as_link() == type_var_usage.in_definition {
                            let g = class.generics.nth(i_s, type_var_usage.index);
                            // TODO nth should return a type instead of DbType
                            let g = Type::from_db_type(i_s.db, &g);
                            return g.matches(i_s, None, value_type, type_var.variance);
                        }
                        // If we're in a class context, we must also be in a method.
                        let func_class = f.class.unwrap();
                        if type_var_usage.in_definition == func_class.node_ref.as_link() {
                            // By definition, because the class did not match there will never be a
                            // type_var_remap that is not defined.
                            let type_var_remap = func_class.type_var_remap.unwrap();
                            let g = type_var_remap.nth(type_var_usage.index).unwrap();
                            let g = Type::from_db_type(i_s.db, g);
                            // The remapping of type vars needs to be checked now. In a lot of
                            // cases this is T -> T and S -> S, but it could also be T -> S and S
                            // -> List[T] or something completely arbitrary.
                            let result = g.matches(i_s, Some(self), value_type, type_var.variance);
                            return result;
                        }
                    } else {
                        todo!("Probably nested generic functions???")
                    }
                }
                FunctionOrCallable::Callable(c) => todo!(),
            }
        }
        let mut mismatch_constraints = !type_var.restrictions.is_empty()
            && !type_var.restrictions.iter().any(|t| {
                Type::from_db_type(i_s.db, t)
                    .matches(i_s, None, value_type, Variance::Covariant)
                    .bool()
            });
        if let Some(bound) = &type_var.bound {
            mismatch_constraints = mismatch_constraints
                || !Type::from_db_type(i_s.db, bound).matches(
                    i_s,
                    None,
                    value_type,
                    Variance::Covariant,
                );
        }
        if mismatch_constraints {
            (self.on_constraint_mismatch)(i_s, type_var, value_type);
        }
        if self.match_in_definition == type_var_usage.in_definition {
            let current = &mut self.calculated_type_vars[type_var_usage.index.as_usize()];
            if let Some(current_type) = &current.type_ {
                let current_type = Type::from_db_type(i_s.db, current_type);
                if !current_type.matches(i_s, None, value_type, variance).bool() {
                    if value_type
                        .matches(i_s, None, &current_type, variance)
                        .bool()
                    {
                        // In case A(B) and B are given, use B, because it's the super class.
                        current.type_ = Some(value_type.as_db_type(i_s));
                    } else {
                        (self.on_cannot_infer_type_argument)(i_s, type_var_usage);
                    }
                }
            } else {
                current.type_ = Some(value_type.as_db_type(i_s));
            }
        } else {
            // Happens e.g. for testInvalidNumberOfTypeArgs
            // class C:  # Forgot to add type params here
            //     def __init__(self, t: T) -> None: pass
            todo!(
                "TODO free type param annotations; searched {:?} ({:?}), found {:?} ({:?})",
                self.match_type,
                self.match_in_definition,
                type_var_usage.type_,
                type_var_usage.in_definition,
            )
        }
        Match::True
    }
}

pub fn calculate_function_type_vars_and_return<'db>(
    i_s: &mut InferenceState<'db, '_>,
    class: Option<&Class<'db, '_>>,
    function: Function<'db, '_>,
    args: &dyn Arguments<'db>,
    skip_first_param: bool,
    type_vars: Option<&TypeVars>,
    match_type: TypeVarType,
    match_in_definition: PointLink,
    result_context: &ResultContext<'db, '_>,
    on_type_error: Option<OnTypeError<'db, '_>>,
) -> (SignatureMatch, Option<GenericsList>) {
    debug!(
        "Calculate type vars for {} in {}",
        function.name(),
        class.map(|c| c.name()).unwrap_or("-")
    );
    calculate_type_vars(
        i_s,
        class,
        FunctionOrCallable::Function(class, function),
        args,
        skip_first_param,
        type_vars,
        match_type,
        match_in_definition,
        result_context,
        on_type_error,
    )
}

pub fn calculate_callable_type_vars_and_return<'db>(
    i_s: &mut InferenceState<'db, '_>,
    callable: &Callable,
    args: &dyn Arguments<'db>,
    type_vars: Option<&TypeVars>,
    match_type: TypeVarType,
    match_in_definition: PointLink,
    result_context: &ResultContext<'db, '_>,
    on_type_error: OnTypeError<'db, '_>,
) -> Option<GenericsList> {
    calculate_type_vars(
        i_s,
        None,
        FunctionOrCallable::Callable(callable),
        args,
        false,
        type_vars,
        match_type,
        match_in_definition,
        result_context,
        Some(on_type_error),
    )
    .1
}

fn calculate_type_vars<'db>(
    i_s: &mut InferenceState<'db, '_>,
    class: Option<&Class<'db, '_>>, // TODO it appears this param is unused?
    func_or_callable: FunctionOrCallable<'db, '_>,
    args: &dyn Arguments<'db>,
    skip_first_param: bool,
    type_vars: Option<&TypeVars>,
    match_type: TypeVarType,
    match_in_definition: PointLink,
    result_context: &ResultContext<'db, '_>,
    on_type_error: Option<OnTypeError<'db, '_>>,
) -> (SignatureMatch, Option<GenericsList>) {
    let should_generate_errors = on_type_error.is_some();
    let mut matches_constraints = true;
    let mut on_constraint_mismatch =
        |i_s: &mut InferenceState<'db, '_>, type_var: &TypeVar, value_type: &Type<'db, '_>| {
            match func_or_callable {
                FunctionOrCallable::Function(class, f) => {
                    if should_generate_errors {
                        args.as_node_ref().add_typing_issue(
                            i_s.db,
                            IssueType::InvalidTypeVarValue {
                                type_var: Box::from(type_var.name(i_s.db)),
                                func: f.diagnostic_string(class),
                                actual: value_type.format(i_s, None, FormatStyle::Short),
                            },
                        );
                    } else {
                        debug!(
                            "TODO this is wrong, because this might also be Match::FalseButSimilar"
                        );
                        matches_constraints = false;
                    }
                }
                _ => todo!(),
            }
        };
    let mut on_cannot_infer_type_argument =
        |i_s: &mut InferenceState<'db, '_>, type_var_usage: &TypeVarUsage| {
            args.as_node_ref().add_typing_issue(
                i_s.db,
                IssueType::CannotInferTypeArgument {
                    index: type_var_usage.index,
                    callable: match func_or_callable {
                        FunctionOrCallable::Function(class, function) => {
                            function.diagnostic_string(class)
                        }
                        FunctionOrCallable::Callable(callable) => {
                            Box::from(callable.content.format(i_s.db, FormatStyle::Short))
                        }
                    },
                },
            );
        };
    // We could allocate on stack as described here:
    // https://stackoverflow.com/questions/27859822/is-it-possible-to-have-stack-allocated-arrays-with-the-size-determined-at-runtim
    let type_vars_len = match type_vars {
        Some(type_vars) => type_vars.len(),
        None => 0,
    };
    let mut calculated_type_vars = vec![];
    calculated_type_vars.resize_with(type_vars_len, Default::default);
    let mut matcher = match type_vars {
        Some(type_vars) => Some(TypeVarMatcher::new(
            func_or_callable,
            match_type,
            match_in_definition,
            &mut calculated_type_vars,
            &mut on_constraint_mismatch,
            &mut on_cannot_infer_type_argument,
        )),
        None => {
            if let FunctionOrCallable::Function(_, function) = func_or_callable {
                if let Some(func_class) = function.class {
                    func_class.type_vars(i_s).map(|type_vars| {
                        TypeVarMatcher::new(
                            func_or_callable,
                            match_type,
                            match_in_definition,
                            &mut calculated_type_vars, // TODO There rae no type vars in there, should set it to 0
                            &mut on_constraint_mismatch,
                            &mut on_cannot_infer_type_argument,
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
    if let ResultContext::Known(type_) = result_context {
        let result_type = match func_or_callable {
            FunctionOrCallable::Function(_, f) => f.result_type(i_s),
            FunctionOrCallable::Callable(c) => c.result_type(i_s),
        };
        result_type.matches(i_s, matcher.as_mut(), type_, Variance::Covariant);
    }
    let mut result = match func_or_callable {
        FunctionOrCallable::Function(class, function) => {
            // Make sure the type vars are properly pre-calculated, because we are using type
            // vars from in use_cached_annotation_type.
            function.type_vars(i_s);
            calculate_type_vars_for_params(
                i_s,
                matcher.as_mut(),
                class,
                Some(&function),
                args,
                on_type_error,
                function.iter_args_with_params(args, skip_first_param),
            )
        }
        FunctionOrCallable::Callable(callable) => {
            if let Some(params) = callable.iter_params() {
                calculate_type_vars_for_params(
                    i_s,
                    matcher.as_mut(),
                    None,
                    None,
                    args,
                    on_type_error,
                    InferrableParamIterator2::new(params, args.iter_arguments().peekable()),
                )
            } else {
                SignatureMatch::True
            }
        }
    };
    let generics_out = matcher.is_some().then(|| {
        GenericsList::new_generics(
            calculated_type_vars
                .into_iter()
                .map(|c| c.type_.unwrap_or(DbType::Never))
                .collect(),
        )
    });
    if cfg!(feature = "zuban_debug") {
        if let Some(generics_out) = &generics_out {
            let callable_description: String;
            debug!(
                "Calculated type vars: {}[{}]",
                match &func_or_callable {
                    FunctionOrCallable::Function(_, function) => function.name(),
                    FunctionOrCallable::Callable(callable) => {
                        callable_description = callable.description(i_s);
                        &callable_description
                    }
                },
                generics_out.format(i_s.db, None, FormatStyle::Short),
            );
        }
    }
    if !matches_constraints {
        result = SignatureMatch::False
    }
    (result, generics_out)
}

fn calculate_type_vars_for_params<'db: 'x, 'x, P: Param<'db, 'x>>(
    i_s: &mut InferenceState<'db, '_>,
    mut matcher: Option<&mut TypeVarMatcher<'db, '_>>,
    class: Option<&Class<'db, '_>>,
    function: Option<&Function<'db, '_>>,
    args: &dyn Arguments<'db>,
    on_type_error: Option<OnTypeError<'db, '_>>,
    mut args_with_params: InferrableParamIterator2<'db, '_, impl Iterator<Item = P>, P>,
) -> SignatureMatch {
    // TODO this can be calculated multiple times from different places
    let should_generate_errors = on_type_error.is_some();
    let mut missing_params = vec![];
    let mut any_args = vec![];
    let mut matches = Match::True;
    for (i, p) in args_with_params.by_ref().enumerate() {
        if p.argument.is_none() && !p.param.has_default() {
            matches = Match::False;
            missing_params.push(p.param);
            continue;
        }
        if let Some(argument) = p.argument {
            if let Some(annotation_type) = p.param.annotation_type(i_s) {
                let value = argument.infer(i_s);
                let value_class = value.class_as_type(i_s);

                let on_type_error = on_type_error;
                let m = annotation_type.error_if_not_matches_with_matcher(
                    i_s,
                    matcher.as_deref_mut(),
                    &value,
                    |i_s, t1, t2| {
                        if let Some(on_type_error) = on_type_error {
                            on_type_error(i_s, argument.as_node_ref(), class, function, &p, t1, t2);
                        }
                    },
                );
                if matches!(m, Match::TrueWithAny) {
                    any_args.push(i)
                }
                matches &= m;
            }
        }
    }
    if args_with_params.too_many_positional_arguments {
        matches = Match::False;
        if should_generate_errors || true {
            // TODO remove true and add test
            let mut s = "Too many positional arguments".to_owned();
            if let Some(function) = function {
                s += " for ";
                s += &function.diagnostic_string(class);
            }

            args.as_node_ref()
                .add_typing_issue(i_s.db, IssueType::ArgumentIssue(s.into()));
        }
    } else if args_with_params.arguments.peek().is_some() {
        matches = Match::False;
        if should_generate_errors {
            let mut too_many = false;
            for arg in args_with_params.arguments {
                match arg {
                    Argument::Keyword(name, reference) => {
                        let mut s = format!("Unexpected keyword argument {name:?}");
                        if let Some(function) = function {
                            s += " for ";
                            s += &function.diagnostic_string(class);
                        }
                        reference.add_typing_issue(i_s.db, IssueType::ArgumentIssue(s.into()));
                    }
                    _ => too_many = true,
                }
            }
            if too_many {
                let mut s = "Too many arguments".to_owned();
                if let Some(function) = function {
                    s += " for ";
                    s += &function.diagnostic_string(class);
                }

                args.as_node_ref()
                    .add_typing_issue(i_s.db, IssueType::ArgumentIssue(s.into()));
            }
        }
    } else if !args_with_params.unused_keyword_arguments.is_empty() && should_generate_errors {
        for unused in args_with_params.unused_keyword_arguments {
            match unused {
                Argument::Keyword(name, reference) => {
                    let s = if let Some(function) = function {
                        if function
                            .node()
                            .params()
                            .iter()
                            .any(|p| p.name_definition().as_code() == name)
                        {
                            format!(
                                "{:?} gets multiple values for keyword argument {name:?}",
                                function.name(),
                            )
                        } else {
                            format!(
                                "Unexpected keyword argument {name:?} for {:?}",
                                function.name(),
                            )
                        }
                    } else {
                        debug!("TODO this keyword param could also exist");
                        format!("Unexpected keyword argument {name:?}")
                    };
                    reference.add_typing_issue(i_s.db, IssueType::ArgumentIssue(s.into()));
                }
                _ => unreachable!(),
            }
        }
    } else if should_generate_errors {
        let mut missing_positional = vec![];
        for param in &missing_params {
            if let Some(param_name) = param.name() {
                if param.param_type() == ParamType::KeywordOnly {
                    let mut s = format!("Missing named argument {:?}", param_name);
                    if let Some(function) = function {
                        s += " for ";
                        s += &function.diagnostic_string(class);
                    }
                    args.as_node_ref()
                        .add_typing_issue(i_s.db, IssueType::ArgumentIssue(s.into()));
                } else {
                    missing_positional.push(format!("\"{param_name}\""));
                }
            } else {
                args.as_node_ref().add_typing_issue(
                    i_s.db,
                    IssueType::ArgumentIssue(Box::from("Too few arguments")),
                );
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
            if let Some(function) = function {
                s += " to ";
                s += &function.diagnostic_string(class);
            }
            args.as_node_ref()
                .add_typing_issue(i_s.db, IssueType::ArgumentIssue(s.into()));
        };
    }
    match matches {
        Match::True => SignatureMatch::True,
        Match::TrueWithAny => SignatureMatch::TrueWithAny(any_args),
        Match::FalseButSimilar => SignatureMatch::FalseButSimilar,
        Match::False => SignatureMatch::False,
    }
}
