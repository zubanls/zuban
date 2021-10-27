use parsa_python_ast::Name;

use super::{Value, ValueKind};
use crate::getitem::SliceType;
use crate::arguments::Arguments;
use crate::inference_state::InferenceState;
use crate::database::{Specific, Point, Locality};
use crate::inferred::{Inferred, NodeReference};

#[derive(Debug)]
pub struct TypingClass<'db> {
    reference: NodeReference<'db>,
    specific: Specific
}

impl<'db> TypingClass<'db> {
    pub fn new(reference: NodeReference<'db>, specific: Specific) -> Self {
        Self { reference, specific }
    }
}

impl<'db> Value<'db> for TypingClass<'db> {
    fn get_kind(&self) -> ValueKind {
        ValueKind::Class
    }

    fn get_name(&self) -> &'db str {
        Name::by_index(&self.reference.file.tree, self.reference.node_index).as_str()
    }

    fn lookup(&self, i_s: &mut InferenceState<'db, '_>, name: &str) -> Inferred<'db> {
        todo!()
    }

    fn get_item(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        slice_type: &SliceType<'db>,
    ) -> Inferred<'db> {
        if matches!(self.specific, Specific::TypingGeneric | Specific::TypingProtocol) {
            let point = Point::new_simple_language_specific(Specific::TypingWithGenerics, Locality::Stmt);
            match slice_type {
                SliceType::Simple(simple) => {
                    Inferred::new_and_save(simple.file, simple.primary_index, point)
                }
                _ => todo!(),
            }
        } else {
            unreachable!()
        }
    }

    fn execute(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
    ) -> Inferred<'db> {
        todo!()
    }
}

#[derive(Debug)]
pub struct TypingWithGenerics<'db> {
    reference: NodeReference<'db>,
}

impl<'db> TypingWithGenerics<'db> {
    pub fn new(reference: NodeReference<'db>) -> Self {
        Self { reference }
    }
}

impl<'db> Value<'db> for TypingWithGenerics<'db> {
    fn get_kind(&self) -> ValueKind {
        ValueKind::Class
    }

    fn get_name(&self) -> &'db str {
        // TODO wrong
        "TODO"
    }

    fn lookup(&self, i_s: &mut InferenceState<'db, '_>, name: &str) -> Inferred<'db> {
        todo!()
    }
}
