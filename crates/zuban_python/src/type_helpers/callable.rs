use std::borrow::Cow;

use super::Class;
use crate::{
    arguments::Args,
    database::{Database, PointLink},
    diagnostics::IssueKind,
    file::FLOW_ANALYSIS,
    inference_state::InferenceState,
    inferred::Inferred,
    matching::{OnTypeError, calc_callable_type_vars},
    result_context::ResultContext,
    type_::{
        CallableContent, CallableParams, NeverCause, ParamType, ReplaceSelf, Type, TypeVarLikes,
    },
};

#[derive(Debug, Copy, Clone)]
pub(crate) struct Callable<'a> {
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

    pub(crate) fn execute<'db>(
        &self,
        i_s: &InferenceState<'db, '_>,
        args: &dyn Args<'db>,
        on_type_error: OnTypeError,
        result_context: &mut ResultContext,
    ) -> Inferred {
        let result = self.execute_internal(i_s, args, false, on_type_error, result_context, None);
        if matches!(self.content.return_type, Type::Never(NeverCause::Explicit)) {
            FLOW_ANALYSIS.with(|fa| fa.mark_current_frame_unreachable())
        }
        result
    }

    pub(crate) fn execute_internal<'db>(
        &self,
        i_s: &InferenceState<'db, '_>,
        args: &dyn Args<'db>,
        skip_first_argument: bool,
        on_type_error: OnTypeError,
        result_context: &mut ResultContext,
        as_self_type: Option<ReplaceSelf>,
    ) -> Inferred {
        if self.content.is_abstract_from_super {
            args.add_issue(
                i_s,
                IssueKind::CallToAbstractMethodViaSuper {
                    method_name: self.content.name(i_s.db).into(),
                    class_name: self
                        .content
                        .class_name
                        .map(|c| c.as_str(i_s.db).into())
                        .unwrap_or_else(|| "<class>".into()),
                },
            );
        }
        let return_type = &self.content.return_type;
        if result_context.expect_not_none() && matches!(&return_type, Type::None) {
            args.add_issue(
                i_s,
                IssueKind::DoesNotReturnAValue(
                    self.diagnostic_string(i_s.db)
                        .unwrap_or_else(|| "Function".into())
                        .into(),
                ),
            );
            if i_s.db.mypy_compatible() {
                return Inferred::new_any_from_error();
            }
        }
        self.execute_for_custom_return_type(
            i_s,
            args,
            skip_first_argument,
            return_type,
            on_type_error,
            result_context,
            as_self_type,
        )
    }

    pub(crate) fn execute_for_custom_return_type<'db>(
        &self,
        i_s: &InferenceState<'db, '_>,
        args: &dyn Args<'db>,
        skip_first_argument: bool,
        return_type: &Type,
        on_type_error: OnTypeError,
        result_context: &mut ResultContext,
        as_self_type: Option<ReplaceSelf>,
    ) -> Inferred {
        let calculated_type_vars = calc_callable_type_vars(
            i_s,
            *self,
            args.iter(i_s.mode),
            |issue| args.add_issue(i_s, issue),
            skip_first_argument,
            result_context,
            as_self_type,
            Some(on_type_error),
        );
        calculated_type_vars.into_return_type(
            i_s,
            return_type,
            self.defined_in.as_ref(),
            as_self_type.unwrap_or(&|| self.defined_in.map(|c| c.as_type(i_s.db))),
        )
    }
}

pub(crate) trait FuncLike: std::fmt::Debug {
    fn inferred_return_type<'a>(&'a self, i_s: &InferenceState<'a, '_>) -> Cow<'a, Type>;
    fn diagnostic_string(&self, db: &Database) -> Option<String>;
    fn defined_at(&self) -> PointLink;
    fn type_vars<'a>(&'a self, db: &'a Database) -> &'a TypeVarLikes;
    fn class(&self) -> Option<Class<'_>>;
    fn first_self_or_class_annotation<'a>(
        &'a self,
        i_s: &'a InferenceState,
    ) -> Option<Cow<'a, Type>>;
    fn has_keyword_param_with_name(&self, db: &Database, name: &str) -> bool;
    fn is_callable(&self) -> bool;
}

impl FuncLike for Callable<'_> {
    fn inferred_return_type<'a>(&'a self, _: &InferenceState) -> Cow<'a, Type> {
        Cow::Borrowed(&self.content.return_type)
    }

    fn diagnostic_string(&self, db: &Database) -> Option<String> {
        self.content.name.as_ref().map(|n| {
            let name = n.as_str(db);
            match self.content.class_name {
                Some(c) => format!("\"{}\" of \"{}\"", name, c.as_str(db)),
                None => format!("\"{name}\""),
            }
        })
    }

    fn defined_at(&self) -> PointLink {
        self.content.defined_at
    }

    fn type_vars<'a>(&'a self, _: &'a Database) -> &'a TypeVarLikes {
        &self.content.type_vars
    }

    fn class(&self) -> Option<Class<'_>> {
        self.defined_in
    }

    fn first_self_or_class_annotation(&self, _: &InferenceState) -> Option<Cow<'_, Type>> {
        if !self.content.kind.had_first_self_or_class_annotation() {
            return None;
        }
        Some(Cow::Owned(self.content.first_positional_type()?))
    }

    fn has_keyword_param_with_name(&self, db: &Database, name: &str) -> bool {
        match &self.content.params {
            CallableParams::Simple(params) => params.iter().any(|p| {
                p.name.as_ref().is_some_and(|n| {
                    n.as_str(db) == name
                        && matches!(
                            p.type_,
                            ParamType::PositionalOrKeyword(_) | ParamType::KeywordOnly(_)
                        )
                })
            }),
            _ => false,
        }
    }

    fn is_callable(&self) -> bool {
        true
    }
}
