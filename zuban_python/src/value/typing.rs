use parsa_python_ast::{Name, PrimaryContent};

use super::{Value, ValueKind};
use crate::arguments::{ArgumentIterator, Arguments};
use crate::database::{Locality, Point, Specific};
use crate::getitem::SliceType;
use crate::inference_state::InferenceState;
use crate::inferred::{Inferred, NodeReference};

#[derive(Debug)]
pub struct TypingClass<'db> {
    reference: NodeReference<'db>,
    specific: Specific,
}

impl<'db> TypingClass<'db> {
    pub fn new(reference: NodeReference<'db>, specific: Specific) -> Self {
        Self {
            reference,
            specific,
        }
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
        if matches!(
            self.specific,
            Specific::TypingGeneric | Specific::TypingProtocol
        ) {
            let point =
                Point::new_simple_language_specific(Specific::TypingWithGenerics, Locality::Stmt);
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
    pub specific: Specific,
}

impl<'db> TypingWithGenerics<'db> {
    pub fn new(reference: NodeReference<'db>, specific: Specific) -> Self {
        Self {
            reference,
            specific,
        }
    }

    pub fn get_generics(&self) -> SliceType<'db> {
        let primary = self.reference.as_primary();
        if let PrimaryContent::GetItem(slice_type) = primary.second() {
            //value.get_item(i_s, &SliceType::new(f, primary.index(), slice_type))
            SliceType::new(self.reference.file, primary.index(), slice_type)
        } else {
            unreachable!()
        }
    }
}

impl<'db> Value<'db> for TypingWithGenerics<'db> {
    fn get_kind(&self) -> ValueKind {
        ValueKind::Class
    }

    fn get_name(&self) -> &'db str {
        match self.specific {
            Specific::TypingGeneric => "Generic",
            Specific::TypingProtocol => "Protocol",
            _ => unreachable!(),
        }
    }

    fn lookup(&self, i_s: &mut InferenceState<'db, '_>, name: &str) -> Inferred<'db> {
        todo!()
    }
    fn as_typing_with_generics(&self, i_s: &mut InferenceState<'db, '_>) -> Option<&Self> {
        Some(self)
    }
}
