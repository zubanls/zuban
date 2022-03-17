use std::fmt;

use parsa_python_ast::PrimaryContent;

use super::{ClassLike, IteratorContent, Value, ValueKind};
use crate::arguments::{Argument, ArgumentIterator, Arguments};
use crate::base_description;
use crate::database::{
    CallableContent, ComplexPoint, Database, DbType, FormatStyle, GenericsList, Specific,
    TupleContent, TypeVarIndex,
};
use crate::diagnostics::IssueType;
use crate::generics::{Generics, Type, TypeVarMatcher};
use crate::getitem::{SliceOrSimple, SliceType, SliceTypeContent};
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::node_ref::NodeRef;

#[derive(Debug, Clone, Copy)]
pub struct TypingClass {
    pub specific: Specific,
}

impl TypingClass {
    pub fn new(specific: Specific) -> Self {
        Self { specific }
    }

    pub fn as_db_type(&self) -> DbType {
        match self.specific {
            Specific::TypingTuple => DbType::Tuple(TupleContent {
                generics: None,
                arbitrary_length: true,
            }),
            Specific::TypingType => DbType::Type(Box::new(DbType::Any)),
            _ => todo!("{:?}", self.specific),
        }
    }
}

impl<'db, 'a> Value<'db, 'a> for TypingClass {
    fn kind(&self) -> ValueKind {
        ValueKind::Class
    }

    fn name(&self) -> &'db str {
        match self.specific {
            Specific::TypingGeneric => "Generic",
            Specific::TypingProtocol => "Protocol",
            Specific::TypingTuple => "Tuple",
            Specific::TypingCallable => "Callable",
            Specific::TypingUnion => "Union",
            Specific::TypingOptional => "Optional",
            Specific::TypingType => "Type",
            _ => unreachable!("{:?}", self.specific),
        }
    }

    fn lookup_internal(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        name: &str,
    ) -> Option<Inferred<'db>> {
        todo!()
    }

    fn as_typing_class(&self) -> Option<&TypingClass> {
        Some(self)
    }

    fn get_item(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        slice_type: &SliceType<'db>,
    ) -> Inferred<'db> {
        match self.specific {
            Specific::TypingGeneric | Specific::TypingProtocol => {
                Inferred::new_unsaved_specific(Specific::TypingWithGenerics)
            }
            Specific::TypingTuple => {
                let content = match slice_type.unpack() {
                    SliceTypeContent::Simple(simple) => {
                        // TODO if it is a (), it's an empty tuple
                        TupleContent {
                            generics: Some(GenericsList::new(Box::new([simple
                                .infer_annotation_class(i_s)
                                .as_db_type(i_s)]))),
                            arbitrary_length: false,
                        }
                    }
                    SliceTypeContent::Slice(x) => {
                        todo!()
                    }
                    SliceTypeContent::Slices(slices) => {
                        let mut arbitrary_length = false;
                        TupleContent {
                            generics: Some(GenericsList::new(
                                slices
                                    .iter()
                                    .filter_map(|slice_content| match slice_content {
                                        SliceOrSimple::Simple(n) => {
                                            let result =
                                                n.infer_annotation_class(i_s).as_db_type(i_s);
                                            if let DbType::Unknown = result {
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
                let g = DbType::Type(Box::new(DbType::Tuple(content)));
                Inferred::new_unsaved_complex(ComplexPoint::TypeInstance(Box::new(g)))
            }
            Specific::TypingCallable => {
                let content = match slice_type.unpack() {
                    SliceTypeContent::Simple(simple) => {
                        todo!()
                    }
                    SliceTypeContent::Slice(x) => {
                        todo!()
                    }
                    SliceTypeContent::Slices(slices) => {
                        let mut params = Some(vec![]);
                        let mut iterator = slices.iter();
                        let param_node = iterator.next().map(|slice_content| match slice_content {
                            SliceOrSimple::Simple(n) => {
                                let i = n.infer(i_s);
                                if n.named_expr.as_code() == "..." {
                                    params = None
                                } else {
                                    let mut list = i.iter(i_s, slice_type.as_node_ref());
                                    while let Some(next) = list.next(i_s) {
                                        if let Some(params) = &mut params {
                                            params.push(next.as_db_type(i_s));
                                        }
                                    }
                                }
                            }
                            SliceOrSimple::Slice(s) => todo!(),
                        });
                        let return_class = iterator
                            .next()
                            .map(|n| n.infer_annotation_class(i_s).as_db_type(i_s))
                            .unwrap_or(DbType::Unknown);
                        CallableContent {
                            params: params.map(GenericsList::from_vec),
                            return_class: Box::new(return_class),
                        }
                    }
                };
                let g = DbType::Type(Box::new(DbType::Callable(content)));
                Inferred::new_unsaved_complex(ComplexPoint::TypeInstance(Box::new(g)))
            }
            Specific::TypingUnion => match slice_type.unpack() {
                SliceTypeContent::Simple(simple) => simple.infer_annotation_class(i_s),
                SliceTypeContent::Slice(x) => {
                    todo!()
                }
                SliceTypeContent::Slices(slices) => Inferred::gather_union(|callable| {
                    for slice_content in slices.iter() {
                        if let SliceOrSimple::Simple(n) = slice_content {
                            callable(n.infer_annotation_class(i_s));
                        }
                    }
                }),
            },
            Specific::TypingOptional => match slice_type.unpack() {
                SliceTypeContent::Simple(simple) => simple
                    .infer_annotation_class(i_s)
                    .union(Inferred::new_unsaved_specific(Specific::None)),
                _ => todo!(),
            },
            Specific::TypingType => match slice_type.unpack() {
                SliceTypeContent::Simple(simple) => {
                    let g = simple.infer_annotation_class(i_s).as_db_type(i_s);
                    Inferred::new_unsaved_complex(ComplexPoint::TypeInstance(Box::new(
                        DbType::Type(Box::new(DbType::Type(Box::new(g)))),
                    )))
                }
                _ => todo!(),
            },
            _ => unreachable!("{:?}", self.specific),
        }
    }

    fn as_class_like(&self) -> Option<ClassLike<'db, 'a>> {
        Some(ClassLike::TypingClass(*self))
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
    reference: NodeRef<'db>,
    pub specific: Specific,
}

impl<'db> TypingWithGenerics<'db> {
    pub fn new(reference: NodeRef<'db>, specific: Specific) -> Self {
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

    fn lookup_internal(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        name: &str,
    ) -> Option<Inferred<'db>> {
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

    pub fn as_db_type(&self) -> DbType {
        DbType::Tuple(self.content.clone())
    }

    pub(super) fn generics(&self) -> Generics<'static, 'a> {
        self.content
            .generics
            .as_ref()
            .map(Generics::new_list)
            .unwrap_or(Generics::None)
    }

    pub fn as_type_string(&self, db: &Database, style: FormatStyle) -> String {
        format!(
            "{}{}",
            match style {
                FormatStyle::Short => "tuple",
                FormatStyle::Qualified => "builtins.tuple",
            },
            &self.content.as_string(db, style)
        )
    }
}

impl<'db, 'a> Value<'db, 'a> for TupleClass<'a> {
    fn kind(&self) -> ValueKind {
        ValueKind::Class
    }

    fn name(&self) -> &'db str {
        "tuple"
    }

    fn lookup_internal(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        name: &str,
    ) -> Option<Inferred<'db>> {
        todo!()
    }

    fn as_class_like(&self) -> Option<ClassLike<'db, 'a>> {
        Some(ClassLike::Tuple(TupleClass::new(self.content)))
    }

    fn execute(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
    ) -> Inferred<'db> {
        Inferred::new_unsaved_complex(ComplexPoint::TypeInstance(Box::new(DbType::Tuple(
            self.content.clone(),
        ))))
    }

    fn description(&self, i_s: &mut InferenceState) -> String {
        base_description!(self) + &self.as_type_string(i_s.database, FormatStyle::Short)
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

    pub fn as_db_type(&self) -> DbType {
        DbType::Tuple(self.content.clone())
    }
}

impl<'db, 'a> Value<'db, 'a> for Tuple<'a> {
    fn kind(&self) -> ValueKind {
        ValueKind::Object
    }

    fn name(&self) -> &'db str {
        "tuple"
    }

    fn lookup_internal(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        name: &str,
    ) -> Option<Inferred<'db>> {
        todo!()
    }

    fn iter(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        from: NodeRef<'db>,
    ) -> IteratorContent<'db, 'a> {
        if let Some(generics) = self.content.generics.as_ref() {
            if self.content.arbitrary_length {
                IteratorContent::Inferred(Inferred::execute_db_type(
                    i_s,
                    generics.nth(TypeVarIndex::new(0)).unwrap().clone(),
                ))
            } else {
                match &self.content.generics {
                    Some(generics) => IteratorContent::TupleGenerics(generics.iter()),
                    None => todo!(),
                }
            }
        } else {
            todo!()
        }
    }

    fn class(&self, i_s: &mut InferenceState<'db, '_>) -> ClassLike<'db, 'a> {
        ClassLike::Tuple(TupleClass::new(self.content))
    }

    fn get_item(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        slice_type: &SliceType<'db>,
    ) -> Inferred<'db> {
        match slice_type.unpack() {
            SliceTypeContent::Simple(simple) => {
                let by_index = |i_s: &mut InferenceState<'db, '_>, index| {
                    self.content
                        .generics
                        .as_ref()
                        .and_then(|generics| {
                            generics
                                .nth(TypeVarIndex::new(index))
                                .map(|db_type| Inferred::execute_db_type(i_s, db_type.clone()))
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
            SliceTypeContent::Slice(simple) => {
                todo!()
            }
            SliceTypeContent::Slices(simple) => {
                todo!()
            }
        }
    }

    fn description(&self, i_s: &mut InferenceState) -> String {
        base_description!(self) + &self.content.as_string(i_s.database, FormatStyle::Short)
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
        match slice_type.unpack() {
            SliceTypeContent::Simple(simple) => {
                // TODO if it is a (), it's am empty tuple
                simple.infer(i_s)
            }
            SliceTypeContent::Slice(x) => {
                todo!()
            }
            SliceTypeContent::Slices(x) => {
                todo!()
            }
        }
    }
}

pub struct TypingType<'db, 'a> {
    database: &'db Database,
    pub db_type: &'a DbType,
}

impl<'db, 'a> TypingType<'db, 'a> {
    pub fn new(database: &'db Database, db_type: &'a DbType) -> Self {
        Self { database, db_type }
    }
}

impl<'db, 'a> Value<'db, 'a> for TypingType<'db, 'a> {
    fn kind(&self) -> ValueKind {
        ValueKind::Object
    }

    fn name(&self) -> &'db str {
        "Type"
    }

    fn lookup_internal(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        name: &str,
    ) -> Option<Inferred<'db>> {
        todo!()
    }

    fn class(&self, i_s: &mut InferenceState<'db, '_>) -> ClassLike<'db, 'a> {
        todo!()
    }

    fn as_class_like(&self) -> Option<ClassLike<'db, 'a>> {
        Some(ClassLike::TypeWithDbType(self.db_type))
    }
}

impl<'db> fmt::Debug for TypingType<'db, '_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("TypingType")
            .field(
                "db_type",
                &self
                    .db_type
                    .as_type_string(self.database, None, FormatStyle::Short),
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

    fn lookup_internal(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        name: &str,
    ) -> Option<Inferred<'db>> {
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
                let g = arg.infer(i_s).as_db_type(i_s);
                Inferred::execute_db_type(i_s, g)
            })
            .unwrap_or_else(|| todo!())
    }
}

#[derive(Debug)]
pub struct Any();

impl<'db, 'a> Value<'db, 'a> for Any {
    fn kind(&self) -> ValueKind {
        ValueKind::Object
    }

    fn name(&self) -> &'db str {
        "Any"
    }

    fn is_any(&self) -> bool {
        true
    }

    fn lookup_internal(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        name: &str,
    ) -> Option<Inferred<'db>> {
        todo!()
    }

    fn class(&self, i_s: &mut InferenceState<'db, '_>) -> ClassLike<'db, 'a> {
        ClassLike::AnyType
    }
}

#[derive(Debug, Clone, Copy)]
pub struct CallableClass<'a> {
    pub content: &'a CallableContent,
}

impl<'a> CallableClass<'a> {
    pub fn new(content: &'a CallableContent) -> Self {
        Self { content }
    }

    pub fn as_db_type(&self) -> DbType {
        DbType::Callable(self.content.clone())
    }

    pub fn param_generics<'db>(&self) -> Generics<'db, 'a> {
        self.content
            .params
            .as_ref()
            .map(Generics::new_list)
            .unwrap_or(Generics::None)
    }

    pub fn result_generics<'db>(&self) -> Generics<'db, 'a> {
        Generics::DbType(&self.content.return_class)
    }
}

impl<'db, 'a> Value<'db, 'a> for CallableClass<'a> {
    fn kind(&self) -> ValueKind {
        ValueKind::Class
    }

    fn name(&self) -> &'db str {
        "Callable"
    }

    fn lookup_internal(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        name: &str,
    ) -> Option<Inferred<'db>> {
        todo!()
    }

    fn as_class_like(&self) -> Option<ClassLike<'db, 'a>> {
        Some(ClassLike::Callable(CallableClass::new(self.content)))
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

    pub fn as_db_type(&self) -> DbType {
        DbType::Callable(self.content.clone())
    }

    fn description(&self, i_s: &mut InferenceState) -> String {
        base_description!(self) + &self.content.as_string(i_s.database, FormatStyle::Short)
    }

    pub fn iter_params_with_args<'db, 'b>(
        &self,
        args: &'b dyn Arguments<'db>,
    ) -> CallableParamIterator<'db, 'a, 'b> {
        CallableParamIterator {
            params: self.content.params.as_ref().map(|params| params.iter()),
            arguments: args.iter_arguments(),
        }
    }
}

impl<'db, 'a> Value<'db, 'a> for Callable<'a> {
    fn kind(&self) -> ValueKind {
        ValueKind::Object
    }

    fn name(&self) -> &'db str {
        "Callable"
    }

    fn lookup_internal(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        name: &str,
    ) -> Option<Inferred<'db>> {
        todo!()
    }

    fn class(&self, i_s: &mut InferenceState<'db, '_>) -> ClassLike<'db, 'a> {
        ClassLike::Callable(CallableClass::new(self.content))
    }

    fn execute(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
    ) -> Inferred<'db> {
        let mut type_vars = vec![]; // todo!()
        if let Some(params) = &self.content.params {
            params.scan_for_late_bound_type_vars(i_s.database, &mut type_vars)
        }
        let mut finder =
            TypeVarMatcher::from_callable(self, args, Some(&type_vars), Specific::LateBoundTypeVar);
        let g_o = Type::from_db_type(i_s.database, &self.content.return_class);
        g_o.execute_and_resolve_type_vars(i_s, None, Some(&mut finder))
    }

    fn description(&self, i_s: &mut InferenceState) -> String {
        base_description!(self) + &self.content.as_string(i_s.database, FormatStyle::Short)
    }
}

pub struct CallableParam<'db, 'a, 'b> {
    pub param_type: &'a DbType,
    pub argument: Option<Argument<'db, 'b>>,
}

pub struct CallableParamIterator<'db, 'a, 'b> {
    params: Option<std::slice::Iter<'a, DbType>>,
    arguments: ArgumentIterator<'db, 'b>,
}

impl<'db, 'a, 'b> Iterator for CallableParamIterator<'db, 'a, 'b> {
    type Item = CallableParam<'db, 'a, 'b>;
    fn next(&mut self) -> Option<Self::Item> {
        self.params
            .as_mut()
            .map(|params| {
                params.next().map(|param_type| Self::Item {
                    param_type,
                    argument: self.arguments.next(),
                })
            })
            .flatten()
    }
}

#[derive(Debug)]
pub struct RevealTypeFunction();

impl<'db> Value<'db, '_> for RevealTypeFunction {
    fn kind(&self) -> ValueKind {
        ValueKind::Function
    }

    fn name(&self) -> &'static str {
        "reveal_type"
    }

    fn lookup_internal(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        name: &str,
    ) -> Option<Inferred<'db>> {
        todo!()
    }

    fn execute(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
    ) -> Inferred<'db> {
        let mut iterator = args.iter_arguments();
        let arg = iterator.next().unwrap_or_else(|| todo!());

        let s = arg
            .infer(i_s)
            .class_as_type(i_s)
            .as_string(i_s, None, FormatStyle::Qualified);
        args.node_reference().add_typing_issue(
            i_s.database,
            IssueType::Note(format!("Revealed type is {:?}", &s)),
        );
        if iterator.next().is_some() {
            todo!()
        }
        Inferred::new_none()
    }
}

#[derive(Debug)]
pub struct TypeVarInstance<'db, 'a> {
    db_type: &'a DbType,
    node_ref: NodeRef<'db>,
}

impl<'db, 'a> TypeVarInstance<'db, 'a> {
    pub fn new(db_type: &'a DbType, node_ref: NodeRef<'db>) -> Self {
        Self { db_type, node_ref }
    }
}

impl<'db, 'a> Value<'db, 'a> for TypeVarInstance<'db, 'a> {
    fn kind(&self) -> ValueKind {
        ValueKind::TypeParameter
    }

    fn name(&self) -> &'db str {
        self.node_ref.as_name().as_str()
    }

    fn lookup_internal(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        name: &str,
    ) -> Option<Inferred<'db>> {
        todo!()
    }

    fn class(&self, i_s: &mut InferenceState<'db, '_>) -> ClassLike<'db, 'a> {
        ClassLike::TypeWithDbType(self.db_type)
    }
}
