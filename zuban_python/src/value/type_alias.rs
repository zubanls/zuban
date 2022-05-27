use super::{ClassLike, LookupResult, Value, ValueKind};
use crate::database::TypeAlias as DbTypeAlias;
use crate::generics::Generics;
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
        todo!()
    }

    fn get_item(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        slice_type: &SliceType<'db>,
    ) -> Inferred<'db> {
        let count_given = match slice_type.ast_node {
            ASTSliceType::Slices(s) => s.iter().count(),
            _ => 1,
        };
        let expected = self.alias.type_vars.len();
        let given_generics = Generics::new_slice(slice_type.file, slice_type.ast_node);
        slice_type
            .file
            .inference(i_s)
            .compute_type_get_item_on_alias(self.alias, *slice_type)
    }

    fn class(&self, i_s: &mut InferenceState<'db, '_>) -> ClassLike<'db, 'a> {
        ClassLike::TypeWithDbType(&self.alias.db_type)
    }
}
