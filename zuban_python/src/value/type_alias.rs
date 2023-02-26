use std::rc::Rc;

use super::{LookupResult, OnTypeError, Value, ValueKind};
use crate::arguments::Arguments;
use crate::database::{ComplexPoint, DbType, TypeAlias as DbTypeAlias};
use crate::debug;
use crate::diagnostics::IssueType;
use crate::getitem::SliceType;
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::matching::{ResultContext, Type};
use crate::node_ref::NodeRef;

#[derive(Debug)]
pub struct TypeAlias<'a> {
    alias: &'a DbTypeAlias,
}

impl<'a> TypeAlias<'a> {
    pub fn new(alias: &'a DbTypeAlias) -> Self {
        Self { alias }
    }
}

impl<'db, 'a> Value<'db, 'a> for TypeAlias<'a> {
    fn kind(&self) -> ValueKind {
        ValueKind::Class
    }

    fn name(&self) -> &str {
        "TypeAlias"
    }

    fn lookup_internal(
        &self,
        i_s: &mut InferenceState,
        node_ref: Option<NodeRef>,
        name: &str,
    ) -> LookupResult {
        debug!("TODO this should at least have the object results");
        LookupResult::None
    }

    fn get_item(
        &self,
        i_s: &mut InferenceState,
        slice_type: &SliceType,
        result_context: &mut ResultContext,
    ) -> Inferred {
        slice_type
            .file
            .inference(i_s)
            .compute_type_application_on_alias(
                self.alias,
                *slice_type,
                matches!(result_context, ResultContext::AssignmentNewDefinition),
            )
    }

    fn as_type(&self, i_s: &mut InferenceState<'db, '_>) -> Type<'a> {
        Type::owned(DbType::Type(Rc::new(
            self.alias.as_db_type_and_set_type_vars_any(i_s.db),
        )))
    }

    fn execute(
        &self,
        i_s: &mut InferenceState,
        args: &dyn Arguments<'db>,
        result_context: &mut ResultContext,
        on_type_error: OnTypeError,
    ) -> Inferred {
        if self.alias.is_class() {
            return Inferred::new_unsaved_complex(ComplexPoint::TypeInstance(Box::new(
                self.alias.as_db_type_and_set_type_vars_any(i_s.db),
            )));
        }
        args.as_node_ref().add_typing_issue(
            i_s.db,
            IssueType::NotCallable {
                type_: Box::from("\"<typing special form>\""),
            },
        );
        Inferred::new_any()
    }
}
