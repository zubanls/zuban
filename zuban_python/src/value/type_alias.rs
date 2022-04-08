use super::{ClassLike, Value, ValueKind};
use crate::database::{ComplexPoint, TypeAlias as DbTypeAlias};
use crate::diagnostics::IssueType;
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

    fn lookup_internal(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        name: &str,
    ) -> Option<Inferred<'db>> {
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
        if count_given != expected {
            slice_type.as_node_ref().add_typing_issue(
                i_s.database,
                IssueType::TypeAliasArgumentIssue(expected, count_given),
            );
        }
        let given_generics = Generics::new_slice(slice_type.file, slice_type.ast_node);
        /*
        let replaced = self
            .alias
            .db_type
            .clone()
            .replace_type_vars(&mut |t| given_generics.nth(i_s, t.index));
        Inferred::new_unsaved_complex(ComplexPoint::TypeInstance(Box::new(replaced)))
        */
        todo!()
    }

    fn class(&self, i_s: &mut InferenceState<'db, '_>) -> ClassLike<'db, 'a> {
        todo!()
    }
}
