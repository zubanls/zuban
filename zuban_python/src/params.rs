use parsa_python_ast::{Param as ASTParam, ParamType};

use crate::generics::Type;

pub trait Param<'db>: Copy {
    fn has_default(&self) -> bool;
    fn name(&self) -> &str;
    fn annotation_type(&self) -> Type<'db, 'db>;
    fn param_type(&self) -> ParamType;
}

impl<'db> Param<'db> for ASTParam<'db> {
    fn has_default(&self) -> bool {
        self.default().is_some()
    }

    fn name(&self) -> &str {
        self.name_definition().as_code()
    }

    fn annotation_type(&self) -> Type<'db, 'db> {
        todo!()
    }

    fn param_type(&self) -> ParamType {
        self.type_()
    }
}
