use std::fmt;

use parsa_python_ast::{Name, PrimaryContent};

use super::{ClassLike, SimpleClassLike, Value, ValueKind};
use crate::arguments::Arguments;
use crate::base_description;
use crate::database::{
    CallableContent, ComplexPoint, Database, GenericPart, GenericsList, Locality, Point, Specific,
    TupleContent, TypeVarIndex,
};
use crate::generics::Generics;
use crate::getitem::{SliceOrSimple, SliceType};
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
                        // TODO if it is a (), it's an empty tuple
                        TupleContent {
                            generics: Some(GenericsList::new(Box::new([simple
                                .infer_annotation_class(i_s)
                                .as_generic_part(i_s)]))),
                            arbitrary_length: false,
                        }
                    }
                    SliceType::Slice(x) => {
                        todo!()
                    }
                    SliceType::Slices(slices) => {
                        let mut arbitrary_length = false;
                        TupleContent {
                            generics: Some(GenericsList::new(
                                slices
                                    .iter()
                                    .filter_map(|slice_content| match slice_content {
                                        SliceOrSimple::Simple(n) => {
                                            let result =
                                                n.infer_annotation_class(i_s).as_generic_part(i_s);
                                            if let GenericPart::Unknown = result {
                                                if n.named_expr.is_ellipsis_literal() {
                                                    arbitrary_length = true;
                                                    return None;
                                                }
                                            }
                                            Some(result)
                                        }
                                        SliceOrSimple::Slice(s) => todo!(),
                                    })
                                    .collect(),
                            )),
                            arbitrary_length,
                        }
                    }
                };
                Inferred::new_unsaved_complex(ComplexPoint::TupleClass(content))
            }
            Specific::TypingCallable => {
                let content = match slice_type {
                    SliceType::Simple(simple) => {
                        todo!()
                    }
                    SliceType::Slice(x) => {
                        todo!()
                    }
                    SliceType::Slices(slices) => {
                        let mut params = vec![];
                        let mut iterator = slices.iter();
                        let param_node = iterator.next().map(|slice_content| match slice_content {
                            SliceOrSimple::Simple(n) => {
                                let mut list = n.infer(i_s).iter(i_s);
                                while let Some(next) = list.next(i_s) {
                                    params.push(next.as_generic_part(i_s));
                                }
                            }
                            SliceOrSimple::Slice(s) => todo!(),
                        });
                        let return_class = iterator
                            .next()
                            .map(|n| n.infer_annotation_class(i_s).as_generic_part(i_s))
                            .unwrap_or(GenericPart::Unknown);
                        CallableContent {
                            params: Some(GenericsList::new(params.into_boxed_slice())),
                            return_class: Box::new(return_class),
                        }
                    }
                };
                Inferred::new_unsaved_complex(ComplexPoint::CallableClass(content))
            }
            Specific::TypingUnion => match slice_type {
                SliceType::Simple(simple) => simple.infer_annotation_class(i_s),
                SliceType::Slice(x) => {
                    todo!()
                }
                SliceType::Slices(slices) => Inferred::gather_union(|callable| {
                    for slice_content in slices.iter() {
                        if let SliceOrSimple::Simple(n) = slice_content {
                            callable(n.infer_annotation_class(i_s));
                        }
                    }
                }),
            },
            Specific::TypingOptional => match slice_type {
                SliceType::Simple(simple) => simple
                    .infer_annotation_class(i_s)
                    .union(Inferred::new_unsaved_specific(Specific::None)),
                _ => todo!(),
            },
            Specific::TypingType => match slice_type {
                SliceType::Simple(simple) => {
                    let g = simple.infer_annotation_class(i_s).as_generic_part(i_s);
                    Inferred::new_unsaved_complex(ComplexPoint::Type(Box::new(g)))
                }
                _ => todo!(),
            },
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
    pub content: &'a TupleContent,
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
            .map(Generics::List)
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
        Some(ClassLike::Simple(SimpleClassLike::Tuple(TupleClass::new(
            self.content,
        ))))
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

    fn description(&self, i_s: &mut InferenceState) -> String {
        let base = base_description!(self);
        if let Some(generics) = &self.content.generics {
            return base + "[" + &generics.as_string(i_s.database) + "]";
        }
        base
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
        ClassLike::Simple(SimpleClassLike::Tuple(TupleClass::new(self.content)))
    }

    fn get_item(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        slice_type: &SliceType<'db>,
    ) -> Inferred<'db> {
        match slice_type {
            SliceType::Simple(simple) => {
                let by_index = |i_s: &mut InferenceState<'db, '_>, index| {
                    self.content
                        .generics
                        .as_ref()
                        .and_then(|generics| {
                            generics.nth(TypeVarIndex::new(index)).map(|generic_part| {
                                Inferred::execute_generic_part(i_s.database, generic_part.clone())
                            })
                        })
                        .unwrap_or_else(Inferred::new_unknown)
                };
                if self.content.arbitrary_length {
                    by_index(i_s, 0)
                } else if let Some(wanted) = simple.infer(i_s).expect_int() {
                    by_index(i_s, usize::try_from(wanted).ok().unwrap_or_else(|| todo!()))
                } else {
                    todo!()
                }
            }
            SliceType::Slice(simple) => {
                todo!()
            }
            SliceType::Slices(simple) => {
                todo!()
            }
        }
    }

    fn description(&self, i_s: &mut InferenceState) -> String {
        let base = base_description!(self);
        if let Some(generics) = &self.content.generics {
            return base + "[" + &generics.as_string(i_s.database) + "]";
        }
        base
    }
}

#[derive(Debug)]
pub struct TypingClassVar();

impl<'db, 'a> Value<'db, 'a> for TypingClassVar {
    fn kind(&self) -> ValueKind {
        ValueKind::Class
    }

    fn name(&self) -> &'db str {
        "ClassVar"
    }

    fn lookup(&self, i_s: &mut InferenceState<'db, '_>, name: &str) -> Inferred<'db> {
        todo!()
    }

    fn get_item(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        slice_type: &SliceType<'db>,
    ) -> Inferred<'db> {
        match slice_type {
            SliceType::Simple(simple) => {
                // TODO if it is a (), it's am empty tuple
                simple.infer(i_s)
            }
            SliceType::Slice(x) => {
                todo!()
            }
            SliceType::Slices(x) => {
                todo!()
            }
        }
    }
}

pub struct TypingType<'db, 'a> {
    database: &'db Database,
    pub generic_part: &'a GenericPart,
}

impl<'db, 'a> TypingType<'db, 'a> {
    pub fn new(database: &'db Database, generic_part: &'a GenericPart) -> Self {
        Self {
            database,
            generic_part,
        }
    }
}

impl<'db, 'a> Value<'db, 'a> for TypingType<'db, 'a> {
    fn kind(&self) -> ValueKind {
        ValueKind::Object
    }

    fn name(&self) -> &'db str {
        "Type"
    }

    fn lookup(&self, i_s: &mut InferenceState<'db, '_>, name: &str) -> Inferred<'db> {
        todo!()
    }

    fn class(&self, i_s: &mut InferenceState<'db, '_>) -> ClassLike<'db, 'a> {
        todo!()
    }

    fn as_class_like(&self) -> Option<ClassLike<'db, 'a>> {
        Some(ClassLike::type_from_generic_part(
            self.database,
            self.generic_part,
        ))
    }
}

impl<'db> fmt::Debug for TypingType<'db, '_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("TypingType")
            .field(
                "generic_part",
                &self.generic_part.as_type_string(self.database),
            )
            .finish()
    }
}

#[derive(Debug)]
pub struct TypingCast();

impl<'db, 'a> Value<'db, 'a> for TypingCast {
    fn kind(&self) -> ValueKind {
        ValueKind::Function
    }

    fn name(&self) -> &'db str {
        "cast"
    }

    fn lookup(&self, i_s: &mut InferenceState<'db, '_>, name: &str) -> Inferred<'db> {
        todo!()
    }

    fn class(&self, i_s: &mut InferenceState<'db, '_>) -> ClassLike<'db, 'a> {
        todo!()
    }

    fn execute(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
    ) -> Inferred<'db> {
        args.iter_arguments()
            .next()
            .map(|arg| {
                Inferred::execute_generic_part(i_s.database, arg.infer(i_s).as_generic_part(i_s))
            })
            .unwrap_or_else(|| todo!())
    }
}

#[derive(Debug, Clone, Copy)]
pub struct CallableClass<'a> {
    content: &'a CallableContent,
}

impl<'a> CallableClass<'a> {
    pub fn new(content: &'a CallableContent) -> Self {
        Self { content }
    }

    pub fn as_generic_part(&self) -> GenericPart {
        GenericPart::Callable(self.content.clone())
    }
}

impl<'db, 'a> Value<'db, 'a> for CallableClass<'a> {
    fn kind(&self) -> ValueKind {
        ValueKind::Class
    }

    fn name(&self) -> &'db str {
        "Callable"
    }

    fn lookup(&self, i_s: &mut InferenceState<'db, '_>, name: &str) -> Inferred<'db> {
        todo!()
    }

    fn as_class_like(&self) -> Option<ClassLike<'db, 'a>> {
        Some(ClassLike::Simple(SimpleClassLike::Callable(
            CallableClass::new(self.content),
        )))
    }
}

#[derive(Debug)]
pub struct Callable<'a> {
    content: &'a CallableContent,
}

impl<'a> Callable<'a> {
    pub fn new(content: &'a CallableContent) -> Self {
        Self { content }
    }

    pub fn as_generic_part(&self) -> GenericPart {
        GenericPart::Callable(self.content.clone())
    }

    fn description(&self, i_s: &mut InferenceState) -> String {
        base_description!(self) + &self.content.as_string(i_s.database)
    }
}

impl<'db, 'a> Value<'db, 'a> for Callable<'a> {
    fn kind(&self) -> ValueKind {
        ValueKind::Object
    }

    fn name(&self) -> &'db str {
        "Callable"
    }

    fn lookup(&self, i_s: &mut InferenceState<'db, '_>, name: &str) -> Inferred<'db> {
        todo!()
    }

    fn class(&self, i_s: &mut InferenceState<'db, '_>) -> ClassLike<'db, 'a> {
        ClassLike::Simple(SimpleClassLike::Callable(CallableClass::new(self.content)))
    }

    fn get_item(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        slice_type: &SliceType<'db>,
    ) -> Inferred<'db> {
        match slice_type {
            SliceType::Simple(simple) => {
                todo!()
            }
            SliceType::Slice(simple) => {
                todo!()
            }
            SliceType::Slices(simple) => {
                todo!()
            }
        }
    }

    fn description(&self, i_s: &mut InferenceState) -> String {
        base_description!(self) + &self.content.as_string(i_s.database)
    }
}
