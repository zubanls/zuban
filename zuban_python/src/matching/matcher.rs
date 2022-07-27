use parsa_python_ast::ParamType;

use super::params::{InferrableParamIterator2, Param};
use super::{Generics, Match, SignatureMatch, Type};
use crate::arguments::{Argument, Arguments};
use crate::database::{
    DbType, FormatStyle, GenericsList, TypeVarType, TypeVarUsage, TypeVars, Variance,
};
use crate::debug;
use crate::diagnostics::IssueType;
use crate::inference_state::InferenceState;
use crate::value::{Callable, Class, Function, OnTypeError, Value};

#[derive(Debug, Clone, Copy)]
pub enum FunctionOrCallable<'db, 'a> {
    Function(Option<&'a Class<'db, 'a>>, Function<'db, 'a>),
    Callable(&'a Callable<'a>),
}

pub struct TypeVarMatcher<'db, 'a> {
    pub func_or_callable: FunctionOrCallable<'db, 'a>,
    args: Option<&'a dyn Arguments<'db>>,
    calculated_type_vars: GenericsList,
    matches: Match,
    match_type: TypeVarType,
    should_generate_errors: bool,
    generics_length: usize,
}

impl<'db, 'a> TypeVarMatcher<'db, 'a> {
    pub fn new(
        func_or_callable: FunctionOrCallable<'db, 'a>,
        args: Option<&'a dyn Arguments<'db>>,
        match_type: TypeVarType,
        should_generate_errors: bool,
        generics_length: usize,
    ) -> Self {
        Self {
            func_or_callable,
            args,
            calculated_type_vars: GenericsList::new_unknown(generics_length),
            matches: Match::True,
            match_type,
            should_generate_errors,
            generics_length,
        }
    }

    pub fn match_or_add_type_var(
        &mut self,
        i_s: &mut InferenceState<'db, '_>,
        type_var_usage: &TypeVarUsage,
        value_type: Type<'db, '_>,
    ) -> Match {
        let type_var = &type_var_usage.type_var;
        if type_var_usage.type_ == TypeVarType::Class {
            match self.func_or_callable {
                FunctionOrCallable::Function(class, f) => {
                    if let Some(type_var_remap) = f.class.unwrap().type_var_remap {
                        let g = type_var_remap.nth(type_var_usage.index).unwrap();
                        let g = Type::from_db_type(i_s.db, g);
                        let mut new_func = f;
                        new_func.class.as_mut().unwrap().type_var_remap = None;
                        // Since we now used the type_var_remap, it needs to be temporarily
                        // replaced with no type_var_remap, to avoid looping when we find type vars
                        // again in the type_var_remap.
                        let old = std::mem::replace(
                            &mut self.func_or_callable,
                            FunctionOrCallable::Function(class, new_func),
                        );
                        let result = g.matches(i_s, Some(self), value_type, type_var.variance);
                        self.func_or_callable = old;
                        return result;
                    } else if !matches!(f.class.unwrap().generics, Generics::None) {
                        let g = f.class.unwrap().generics.nth(i_s, type_var_usage.index);
                        // TODO nth should return a type instead of DbType
                        let g = Type::from_db_type(i_s.db, &g);
                        return g.matches(i_s, Some(self), value_type, type_var.variance);
                    }
                }
                FunctionOrCallable::Callable(c) => todo!(),
            }
        }
        let mut mismatch_constraints = !type_var.restrictions.is_empty()
            && !type_var.restrictions.iter().any(|t| {
                Type::from_db_type(i_s.db, t)
                    .matches(i_s, None, value_type.clone(), Variance::Covariant)
                    .bool()
            });
        if let Some(bound) = &type_var.bound {
            mismatch_constraints = mismatch_constraints
                || !Type::from_db_type(i_s.db, bound).matches(
                    i_s,
                    None,
                    value_type.clone(),
                    Variance::Covariant,
                );
        }
        if mismatch_constraints {
            match self.func_or_callable {
                FunctionOrCallable::Function(class, f) => {
                    if self.should_generate_errors {
                        self.args
                            .unwrap_or_else(|| todo!())
                            .as_node_ref()
                            .add_typing_issue(
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
                        self.matches = Match::False;
                    }
                }
                _ => todo!(),
            }
        }
        if self.match_type == type_var_usage.type_ {
            let current = self.calculated_type_vars.nth(type_var_usage.index).unwrap();
            if current == &DbType::Unknown {
                self.calculated_type_vars
                    .set_generic(type_var_usage.index, value_type.into_db_type(i_s));
            } else {
                let value_db_type = value_type.into_db_type(i_s);
                if current != &value_db_type {
                    dbg!(current, value_db_type);
                    todo!(
                        "should be: Cannot infer type argument {}",
                        type_var_usage.type_var.name(i_s.db)
                    )
                }
            }
        } else {
            // Happens e.g. for testInvalidNumberOfTypeArgs
            // class C:  # Forgot to add type params here
            //     def __init__(self, t: T) -> None: pass
            debug!(
                "TODO free type param annotations; searched {:?}, found {:?}",
                self.match_type, type_var_usage.in_definition
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
    on_type_error: Option<OnTypeError<'db, '_>>,
) -> (SignatureMatch, Option<GenericsList>) {
    calculate_type_vars(
        i_s,
        class,
        FunctionOrCallable::Function(class, function),
        args,
        skip_first_param,
        type_vars,
        match_type,
        on_type_error,
    )
}

pub fn calculate_callable_type_vars_and_return<'db>(
    i_s: &mut InferenceState<'db, '_>,
    callable: &Callable,
    args: &dyn Arguments<'db>,
    type_vars: Option<&TypeVars>,
    match_type: TypeVarType,
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
    on_type_error: Option<OnTypeError<'db, '_>>,
) -> (SignatureMatch, Option<GenericsList>) {
    let calculated_type_vars = type_vars.map(|t| GenericsList::new_unknown(t.len()));
    let matcher = type_vars.map(|t| {
        TypeVarMatcher::new(
            func_or_callable,
            Some(args),
            match_type,
            on_type_error.is_some(),
            t.len(),
        )
    });
    let result = match func_or_callable {
        FunctionOrCallable::Function(class, function) => {
            // Make sure the type vars are properly pre-calculated, because we are using type
            // vars from in use_cached_annotation_type.
            function.type_vars(i_s);
            calculate_type_vars_for_params(
                i_s,
                matcher,
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
                    matcher,
                    None,
                    None,
                    args,
                    on_type_error,
                    InferrableParamIterator2::new(params, args.iter_arguments().peekable()),
                )
            } else {
                (SignatureMatch::True, None)
            }
        }
    };
    if cfg!(feature = "zuban_debug") {
        if let Some(calculated) = &result.1 {
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
                calculated.format(i_s.db, None, FormatStyle::Short),
            );
        }
    }
    result
}

fn calculate_type_vars_for_params<'db: 'x, 'x, P: Param<'db, 'x>>(
    i_s: &mut InferenceState<'db, '_>,
    mut matcher: Option<TypeVarMatcher<'db, '_>>,
    class: Option<&Class<'db, '_>>,
    function: Option<&Function<'db, '_>>,
    args: &dyn Arguments<'db>,
    on_type_error: Option<OnTypeError<'db, '_>>,
    mut args_with_params: InferrableParamIterator2<'db, '_, impl Iterator<Item = P>, P>,
) -> (SignatureMatch, Option<GenericsList>) {
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
                    matcher.as_mut(),
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
    (
        match matches {
            Match::True => SignatureMatch::True,
            Match::TrueWithAny => SignatureMatch::TrueWithAny(any_args),
            Match::FalseButSimilar => SignatureMatch::FalseButSimilar,
            Match::False => SignatureMatch::False,
        },
        matcher.map(|m| m.calculated_type_vars),
    )
}
