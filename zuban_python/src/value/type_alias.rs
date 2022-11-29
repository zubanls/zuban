use super::{LookupResult, OnTypeError, Value, ValueKind};
use crate::arguments::Arguments;
use crate::database::{ComplexPoint, DbType, TypeAlias as DbTypeAlias};
use crate::debug;
use crate::diagnostics::IssueType;
use crate::getitem::SliceType;
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::matching::{ResultContext, Type};
use parsa_python_ast::SliceType as ASTSliceType;

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

    fn lookup_internal(&self, i_s: &mut InferenceState, name: &str) -> LookupResult {
        debug!("TODO this should at least have the object results");
        LookupResult::None
    }

    fn get_item(&self, i_s: &mut InferenceState, slice_type: &SliceType) -> Inferred {
        let count_given = match slice_type.ast_node {
            ASTSliceType::Slices(s) => s.iter().count(),
            _ => 1,
        };
        let expected = self.alias.type_vars.len();
        slice_type
            .file
            .inference(i_s)
            .compute_type_application_on_alias(self.alias, *slice_type)
    }

    fn as_type(&self, i_s: &mut InferenceState<'db, '_>) -> Type<'a> {
        Type::owned(DbType::Type(Box::new(self.alias.db_type.as_ref().clone())))
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
                self.alias.as_db_type_and_set_type_vars_any(),
            )));
        }
        args.as_node_ref().add_typing_issue(
            i_s.db,
            IssueType::NotCallable {
                type_: Box::from("\"object\""),
            },
        );
        Inferred::new_any()
    }
}
