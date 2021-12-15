use parsa_python_ast::{Name, PrimaryContent};

use super::{ClassLike, Value, ValueKind};
use crate::arguments::Arguments;
use crate::database::{
    ComplexPoint, GenericPart, GenericsList, Locality, Point, Specific, TupleContent,
};
use crate::generics::Generics;
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

impl<'db> Value<'db, '_> for TypingClass<'db> {
    fn kind(&self) -> ValueKind {
        ValueKind::Class
    }

    fn name(&self) -> &'db str {
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
        match self.specific {
            Specific::TypingGeneric | Specific::TypingProtocol => {
                let point =
                    Point::new_simple_specific(Specific::TypingWithGenerics, Locality::Stmt);
                Inferred::new_and_save(slice_type.file(), slice_type.primary_index(), point)
            }
            Specific::TypingTuple => {
                let content = match slice_type {
                    SliceType::Simple(simple) => {
                        // TODO if it is a (), it's am empty tuple
                        TupleContent {
                            generics: Some(GenericsList::new(Box::new([
                                simple.infer_annotation_generic_part(i_s)
                            ]))),
                            arbitrary_length: false,
                        }
                    }
                    SliceType::Slice(x) => {
                        todo!()
                    }
                    SliceType::Slices(x) => {
                        todo!()
                    }
                };
                Inferred::new_unsaved_complex(ComplexPoint::TupleClass(content))
            }
            Specific::TypingCallable => {
                todo!()
            }
            _ => unreachable!("{:?}", self.specific),
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

    pub fn generics(&self) -> SliceType<'db> {
        let primary = self.reference.as_primary();
        if let PrimaryContent::GetItem(slice_type) = primary.second() {
            //value.get_item(i_s, &SliceType::new(f, primary.index(), slice_type))
            SliceType::new(self.reference.file, primary.index(), slice_type)
        } else {
            unreachable!()
        }
    }
}

impl<'db> Value<'db, '_> for TypingWithGenerics<'db> {
    fn kind(&self) -> ValueKind {
        ValueKind::Class
    }

    fn name(&self) -> &'db str {
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

#[derive(Debug, Clone, Copy)]
pub struct TupleClass<'a> {
    content: &'a TupleContent,
}

impl<'a> TupleClass<'a> {
    pub fn new(content: &'a TupleContent) -> Self {
        Self { content }
    }

    pub fn as_generic_part(&self) -> GenericPart {
        GenericPart::Tuple(self.content.clone())
    }

    pub(super) fn generics(&self) -> Generics<'static, 'a> {
        self.content
            .generics
            .as_ref()
            .map(|c| Generics::List(c))
            .unwrap_or(Generics::None)
    }
}

impl<'db, 'a> Value<'db, 'a> for TupleClass<'a> {
    fn kind(&self) -> ValueKind {
        ValueKind::Class
    }

    fn name(&self) -> &'db str {
        "Tuple"
    }

    fn lookup(&self, i_s: &mut InferenceState<'db, '_>, name: &str) -> Inferred<'db> {
        todo!()
    }

    fn as_class_like(&self) -> Option<ClassLike<'db, 'a>> {
        Some(ClassLike::Tuple(*self))
    }
}

#[derive(Debug)]
pub struct Tuple<'a> {
    content: &'a TupleContent,
}

impl<'a> Tuple<'a> {
    pub fn new(content: &'a TupleContent) -> Self {
        Self { content }
    }

    pub fn as_generic_part(&self) -> GenericPart {
        GenericPart::Tuple(self.content.clone())
    }
}

impl<'db, 'a> Value<'db, 'a> for Tuple<'a> {
    fn kind(&self) -> ValueKind {
        ValueKind::Object
    }

    fn name(&self) -> &'db str {
        "Tuple"
    }

    fn lookup(&self, i_s: &mut InferenceState<'db, '_>, name: &str) -> Inferred<'db> {
        todo!()
    }

    fn class(&self, i_s: &mut InferenceState<'db, '_>) -> ClassLike<'db, 'a> {
        ClassLike::Tuple(TupleClass::new(self.content))
    }
}
