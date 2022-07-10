use super::{ClassLike, LookupResult, OnTypeError, Value, ValueKind};
use crate::arguments::Arguments;
use crate::database::{ComplexPoint, DbType, TypeAlias as DbTypeAlias};
use crate::debug;
use crate::diagnostics::IssueType;
use crate::getitem::SliceType;
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
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

    fn name(&self) -> &'db str {
        "TypeAlias"
    }

    fn lookup_internal(&self, i_s: &mut InferenceState<'db, '_>, name: &str) -> LookupResult<'db> {
        debug!("TODO this should at least have the object results");
        LookupResult::None
    }

    fn get_item(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        slice_type: &SliceType<'db, '_>,
    ) -> Inferred<'db> {
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

    fn class(&self, i_s: &mut InferenceState<'db, '_>) -> ClassLike<'db, 'a> {
        ClassLike::TypeWithDbType(&self.alias.db_type)
    }

    fn execute(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
        on_type_error: OnTypeError<'db, '_>,
    ) -> Inferred<'db> {
        if matches!(
            self.alias.db_type.as_ref(),
            DbType::Class(_) | DbType::GenericClass(_, _)
        ) {
            return Inferred::new_unsaved_complex(ComplexPoint::TypeInstance(Box::new(
                self.alias.db_type.as_ref().clone(),
            )));
        }
        args.as_node_ref()
            .add_typing_issue(i_s.db, IssueType::NotCallable("\"object\"".to_owned()));
        Inferred::new_any()
    }
}
