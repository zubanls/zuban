use parsa_python_ast::ParamType;

use super::{Generics, Match, SignatureMatch, Type};
use crate::arguments::{Argument, Arguments};
use crate::database::{
    DbType, FormatStyle, GenericsList, TypeVarIndex, TypeVarType, TypeVarUsage, TypeVars, Variance,
};
use crate::debug;
use crate::diagnostics::IssueType;
use crate::inference_state::InferenceState;
use crate::params::{InferrableParamIterator2, Param};
use crate::value::{Callable, Class, Function, OnTypeError, Value};

#[derive(Debug)]
pub(super) enum FunctionOrCallable<'db, 'a> {
    Function(Option<&'a Class<'db, 'a>>, Function<'db, 'a>),
    Callable(&'a Callable<'a>),
}

pub struct TypeVarMatcher<'db, 'a> {
    pub func_or_callable: FunctionOrCallable<'db, 'a>,
    args: &'a dyn Arguments<'db>,
    skip_first_param: bool,
    pub calculated_type_vars: Option<GenericsList>,
    matches: Match,
    type_vars: Option<&'a TypeVars>,
    pub match_type: TypeVarType,
    on_type_error: Option<OnTypeError<'db, 'a>>,
}

impl<'db, 'a> TypeVarMatcher<'db, 'a> {
    pub fn new(
        class: Option<&'a Class<'db, 'a>>,
        function: Function<'db, 'a>,
        args: &'a dyn Arguments<'db>,
        skip_first_param: bool,
        type_vars: Option<&'a TypeVars>,
        match_type: TypeVarType,
        on_type_error: Option<OnTypeError<'db, 'a>>,
    ) -> Self {
        Self {
            func_or_callable: FunctionOrCallable::Function(class, function),
            args,
            calculated_type_vars: None,
            skip_first_param,
            matches: Match::True,
            type_vars,
            match_type,
            on_type_error,
        }
    }
    // TODO the structure of this impl looks very weird, strange funcs

    pub fn from_callable(
        callable: &'a Callable<'a>,
        args: &'a dyn Arguments<'db>,
        type_vars: Option<&'a TypeVars>,
        match_type: TypeVarType,
        on_type_error: OnTypeError<'db, 'a>,
    ) -> Self {
        Self {
            func_or_callable: FunctionOrCallable::Callable(callable),
            args,
            calculated_type_vars: None,
            skip_first_param: false,
            matches: Match::True,
            type_vars,
            match_type,
            on_type_error: Some(on_type_error),
        }
    }

    #[inline]
    fn should_generate_errors(&self) -> bool {
        // If no type error function is given, we are probably checking overloads
        self.on_type_error.is_some()
    }

    pub fn calculate_and_return(
        i_s: &mut InferenceState<'db, '_>,
        class: Option<&'a Class<'db, 'a>>,
        function: Function<'db, 'a>,
        args: &'a dyn Arguments<'db>,
        skip_first_param: bool,
        type_vars: Option<&'db TypeVars>,
        match_type: TypeVarType,
        on_type_error: Option<OnTypeError<'db, 'a>>,
    ) -> Option<GenericsList> {
        let mut self_ = Self::new(
            class,
            function,
            args,
            skip_first_param,
            type_vars,
            match_type,
            on_type_error,
        );
        self_.calculate_type_vars(i_s);
        self_.calculated_type_vars
    }

    fn calculate_type_vars(&mut self, i_s: &mut InferenceState<'db, '_>) -> SignatureMatch {
        // TODO this can be calculated multiple times from different places
        if let Some(type_vars) = self.type_vars {
            if !type_vars.is_empty() {
                self.calculated_type_vars = Some(GenericsList::new_unknown(type_vars.len()));
            }
        }
        let result = match self.func_or_callable {
            FunctionOrCallable::Function(class, function) => {
                // Make sure the type vars are properly pre-calculated, because we are using type
                // vars from in use_cached_annotation_type.
                function.type_vars(i_s);
                self.calculate_type_vars_for_params(
                    i_s,
                    class,
                    Some(&function),
                    function.iter_args_with_params(self.args, self.skip_first_param),
                )
            }
            FunctionOrCallable::Callable(callable) => {
                if let Some(params) = callable.iter_params() {
                    self.calculate_type_vars_for_params(
                        i_s,
                        None,
                        None,
                        InferrableParamIterator2::new(
                            params,
                            self.args.iter_arguments().peekable(),
                        ),
                    )
                } else {
                    SignatureMatch::True
                }
            }
        };
        if cfg!(feature = "zuban_debug") {
            if let Some(calculated) = &self.calculated_type_vars {
                let callable_description: String;
                debug!(
                    "Calculated type vars: {}[{}]",
                    match self.func_or_callable {
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

    fn calculate_type_vars_for_params<'x, P: Param<'db, 'x>>(
        &mut self,
        i_s: &mut InferenceState<'db, '_>,
        class: Option<&Class<'db, '_>>,
        function: Option<&Function<'db, '_>>,
        mut args_with_params: InferrableParamIterator2<'db, '_, impl Iterator<Item = P>, P>,
    ) -> SignatureMatch
    where
        'db: 'x,
    {
        let mut missing_params = vec![];
        let mut any_args = vec![];
        for (i, p) in args_with_params.by_ref().enumerate() {
            if p.argument.is_none() && !p.param.has_default() {
                self.matches = Match::False;
                missing_params.push(p.param);
                continue;
            }
            if let Some(argument) = p.argument {
                if let Some(annotation_type) = p.param.annotation_type(i_s) {
                    let value = argument.infer(i_s);
                    let value_class = value.class_as_type(i_s);

                    let on_type_error = self.on_type_error;
                    let matches = annotation_type.error_if_not_matches(
                        i_s,
                        Some(self),
                        &value,
                        |i_s, t1, t2| {
                            if let Some(on_type_error) = on_type_error {
                                on_type_error(
                                    i_s,
                                    argument.as_node_ref(),
                                    class,
                                    function,
                                    &p,
                                    t1,
                                    t2,
                                );
                            }
                        },
                    );
                    if matches!(matches, Match::TrueWithAny) {
                        any_args.push(i)
                    }
                    self.matches &= matches;
                }
            }
        }
        if args_with_params.too_many_positional_arguments {
            self.matches = Match::False;
            if self.should_generate_errors() || true {
                // TODO remove true and add test
                let mut s = "Too many positional arguments".to_owned();
                if let Some(function) = function {
                    s += " for ";
                    s += &function.diagnostic_string(class);
                }

                self.args
                    .as_node_ref()
                    .add_typing_issue(i_s.db, IssueType::ArgumentIssue(s.into()));
            }
        } else if args_with_params.arguments.peek().is_some() {
            self.matches = Match::False;
            if self.should_generate_errors() {
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

                    self.args
                        .as_node_ref()
                        .add_typing_issue(i_s.db, IssueType::ArgumentIssue(s.into()));
                }
            }
        } else if !args_with_params.unused_keyword_arguments.is_empty()
            && self.should_generate_errors()
        {
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
        } else if self.should_generate_errors() {
            let mut missing_positional = vec![];
            for param in &missing_params {
                if let Some(param_name) = param.name() {
                    if param.param_type() == ParamType::KeywordOnly {
                        let mut s = format!("Missing named argument {:?}", param_name);
                        if let Some(function) = function {
                            s += " for ";
                            s += &function.diagnostic_string(class);
                        }
                        self.args
                            .as_node_ref()
                            .add_typing_issue(i_s.db, IssueType::ArgumentIssue(s.into()));
                    } else {
                        missing_positional.push(format!("\"{param_name}\""));
                    }
                } else {
                    self.args.as_node_ref().add_typing_issue(
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
                self.args
                    .as_node_ref()
                    .add_typing_issue(i_s.db, IssueType::ArgumentIssue(s.into()));
            };
        }
        match self.matches {
            Match::True => SignatureMatch::True,
            Match::TrueWithAny => SignatureMatch::TrueWithAny(any_args),
            Match::FalseButSimilar => SignatureMatch::FalseButSimilar,
            Match::False => SignatureMatch::False,
        }
    }

    pub fn nth(
        &mut self,
        i_s: &mut InferenceState<'db, '_>,
        index: TypeVarIndex,
    ) -> Option<DbType> {
        if let Some(type_vars) = &self.calculated_type_vars {
            type_vars.nth(index).cloned()
        } else {
            self.calculate_type_vars(i_s);
            self.nth(i_s, index)
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
                    if self.should_generate_errors() {
                        self.args.as_node_ref().add_typing_issue(
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
            if let Some(calculated) = self.calculated_type_vars.as_mut() {
                let current = calculated.nth(type_var_usage.index).unwrap();
                if current == &DbType::Unknown {
                    calculated.set_generic(type_var_usage.index, value_type.into_db_type(i_s));
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

    pub fn matches_signature(&mut self, i_s: &mut InferenceState<'db, '_>) -> SignatureMatch {
        self.calculate_type_vars(i_s)
    }
}
