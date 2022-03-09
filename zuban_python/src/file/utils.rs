use parsa_python_ast::{ListOrSetElementIterator, StarLikeExpression};

use crate::database::GenericPart;
use crate::file::PythonInference;
use crate::node_ref::NodeRef;

impl<'db, 'a, 'b> PythonInference<'db, 'a, 'b> {
    pub fn create_list_or_set_generics(
        &mut self,
        elements: ListOrSetElementIterator<'db>,
    ) -> GenericPart {
        let mut result = GenericPart::Unknown;
        for child in elements {
            result.union_in_place(match child {
                StarLikeExpression::NamedExpression(named_expr) => self
                    .infer_named_expression(named_expr)
                    .as_class_generic_part(self.i_s),
                StarLikeExpression::StarNamedExpression(e) => self
                    .infer_expression_part(e.expression_part())
                    .iter(self.i_s, NodeRef::new(self.file, e.index()))
                    .infer_all(self.i_s)
                    .as_class_generic_part(self.i_s),
            });
        }
        result
    }
}
