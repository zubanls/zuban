use std::rc::Rc;

use super::function::{format_pretty_function_like, format_pretty_function_with_params};
use super::Class;
use crate::arguments::Arguments;
use crate::database::{
    CallableContent, CallableParams, Database, DbType, FormatStyle, TypeVar, TypeVarKind,
    TypeVarLike, TypeVarLikes, TypeVarName, TypeVarUsage, Variance,
};
use crate::diagnostics::IssueType;
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::matching::{
    calculate_callable_type_vars_and_return, maybe_class_usage, FormatData, OnTypeError,
    ResultContext, Type,
};

#[derive(Debug, Copy, Clone)]
pub struct Callable<'a> {
    pub content: &'a CallableContent,
    pub defined_in: Option<Class<'a>>,
}

impl<'a> Callable<'a> {
    pub fn new(content: &'a CallableContent, defined_in: Option<Class<'a>>) -> Self {
        Self {
            content,
            defined_in,
        }
    }

    pub fn diagnostic_string(&self, db: &Database) -> Option<String> {
        self.content.name.map(|n| {
            let name = n.as_str(db);
            match self.content.class_name {
                Some(c) => format!("\"{}\" of \"{}\"", name, c.as_str(db)),
                None => format!("\"{name}\""),
            }
        })
    }

    pub fn execute<'db>(
        &self,
        i_s: &InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
        on_type_error: OnTypeError<'db, '_>,
        result_context: &mut ResultContext,
    ) -> Inferred {
        self.execute_internal(i_s, args, false, on_type_error, result_context)
    }

    pub(super) fn execute_internal<'db>(
        &self,
        i_s: &InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
        skip_first_argument: bool,
        on_type_error: OnTypeError<'db, '_>,
        result_context: &mut ResultContext,
    ) -> Inferred {
        let return_type = &self.content.result_type;
        if result_context.expect_not_none(i_s) && matches!(&return_type, DbType::None) {
            args.as_node_ref().add_issue(
                i_s,
                IssueType::DoesNotReturnAValue(
                    self.diagnostic_string(i_s.db)
                        .unwrap_or_else(|| "Function".into())
                        .into(),
                ),
            );
            return Inferred::new_any();
        }
        let calculated_type_vars = calculate_callable_type_vars_and_return(
            i_s,
            *self,
            args.iter(),
            &|| args.as_node_ref(),
            skip_first_argument,
            result_context,
            Some(on_type_error),
        );
        Type::new(return_type).execute_and_resolve_type_vars(
            i_s,
            &calculated_type_vars,
            self.defined_in.as_ref(),
            &|| {
                self.defined_in
                    .map(|c| c.as_db_type(i_s.db))
                    .unwrap_or(DbType::Self_)
            },
        )
    }
}

pub fn format_pretty_callable(format_data: &FormatData, callable: &CallableContent) -> Box<str> {
    let db = format_data.db;
    let not_reveal_type = format_data.style != FormatStyle::MypyRevealType;
    let name = callable
        .name
        .and_then(|s| not_reveal_type.then(|| s.as_str(db)))
        .unwrap_or("");
    match &callable.params {
        CallableParams::Simple(params) => {
            let first_param = params
                .iter()
                .next()
                .and_then(|p| p.param_specific.maybe_positional_db_type())
                .map(|t| t.format(format_data));
            format_pretty_function_like(
                format_data,
                None,
                callable.class_name.map(|c| c.as_str(db)) == first_param.as_deref()
                    && not_reveal_type,
                name,
                &callable.type_vars,
                params.iter(),
                Some(Type::new(&callable.result_type)),
            )
        }
        CallableParams::WithParamSpec(pre_types, usage) => {
            if !pre_types.is_empty() {
                todo!()
            }
            let spec = usage.param_spec.name(db);
            format_pretty_function_with_params(
                format_data,
                None,
                &callable.type_vars,
                Some(Type::new(&callable.result_type)),
                name,
                &format!("*{spec}.args, **{spec}.kwargs"),
            )
        }
        CallableParams::Any => format!(
            "def {name}(*Any, **Any) -> {}",
            callable.result_type.format(format_data)
        )
        .into(),
    }
}

pub fn merge_class_type_vars_into_callable(
    db: &Database,
    class: Class,
    attribute_class: Class,
    callable: &CallableContent,
) -> CallableContent {
    let mut needs_self_type_variable = Type::new(&callable.result_type).has_explicit_self_type(db);
    let CallableParams::Simple(params) = &callable.params else {
        unreachable!()
    };
    for param in params.iter() {
        if let Some(t) = param.param_specific.maybe_db_type() {
            needs_self_type_variable |= Type::new(t).has_explicit_self_type(db);
        }
    }
    let mut type_vars = callable.type_vars.as_vec();
    let mut self_type_var_usage = None;
    for type_var in class.use_cached_type_vars(db).iter() {
        type_vars.push(type_var.clone());
    }
    if needs_self_type_variable {
        let bound = Type::owned(Class::with_self_generics(db, class.node_ref).as_db_type(db))
            .replace_type_var_likes(db, &mut |mut usage| {
                if usage.in_definition() == class.node_ref.as_link() {
                    usage.add_to_index(callable.type_vars.len() as i32);
                }
                usage.into_generic_item()
            });
        let self_type_var = Rc::new(TypeVar {
            name_string: TypeVarName::Self_,
            kind: TypeVarKind::Bound(bound),
            variance: Variance::Invariant,
        });
        self_type_var_usage = Some(TypeVarUsage {
            in_definition: callable.defined_at,
            type_var: self_type_var.clone(),
            index: type_vars.len().into(),
        });
        type_vars.push(TypeVarLike::TypeVar(self_type_var));
    }
    let type_vars = TypeVarLikes::from_vec(type_vars);
    let mut callable = Type::replace_type_var_likes_and_self_for_callable(
        callable,
        db,
        &mut |usage| {
            let in_definition = usage.in_definition();
            if let Some(result) = maybe_class_usage(db, &attribute_class, &usage) {
                result.replace_type_var_likes(
                    db,
                    &mut |usage| {
                        if usage.in_definition() == class.node_ref.as_link() {
                            type_vars
                                .find(usage.as_type_var_like(), callable.defined_at)
                                .unwrap()
                                .into_generic_item()
                        } else {
                            usage.into_generic_item()
                        }
                    },
                    &|| todo!("DbType::TypeVar(self_type_var_usage.clone().unwrap())"),
                )
            } else {
                // This can happen for example if the return value is a Callable with its
                // own type vars.
                usage.into_generic_item()
            }
        },
        &|| DbType::TypeVar(self_type_var_usage.clone().unwrap()),
    );
    callable.type_vars = type_vars;
    callable
}
