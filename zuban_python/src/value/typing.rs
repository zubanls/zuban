use std::fmt;
use std::rc::Rc;

use parsa_python_ast::PrimaryContent;

use super::class::MroIterator;
use super::{ClassLike, Instance, IteratorContent, LookupResult, OnTypeError, Value, ValueKind};
use crate::arguments::{Argument, Arguments};
use crate::base_description;
use crate::database::{
    CallableContent, CallableParam, ComplexPoint, Database, DbType, FormatStyle, PointLink,
    Specific, TupleContent, TypeVar, TypeVarIndex, TypeVarType, TypeVarUsage, TypeVars, Variance,
};
use crate::debug;
use crate::diagnostics::IssueType;
use crate::generics::{Generics, Type, TypeVarMatcher};
use crate::getitem::{SliceType, SliceTypeContent};
use crate::inference_state::InferenceState;
use crate::inferred::{run_on_db_type, Inferred};
use crate::node_ref::NodeRef;

const ANY: DbType = DbType::Any;

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

    fn lookup_internal(&self, i_s: &mut InferenceState<'db, '_>, name: &str) -> LookupResult<'db> {
        todo!()
    }

    fn as_typing_class(&self) -> Option<&TypingClass> {
        Some(self)
    }

    fn get_item(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        slice_type: &SliceType<'db, '_>,
    ) -> Inferred<'db> {
        slice_type
            .file
            .inference(i_s)
            .compute_type_application_on_typing_class(self.specific, *slice_type)
    }

    fn as_class_like(&self) -> Option<ClassLike<'db, 'a>> {
        Some(ClassLike::TypingClass(*self))
    }

    fn class(&self, i_s: &mut InferenceState<'db, '_>) -> ClassLike<'db, 'a> {
        ClassLike::TypingClassType(*self)
    }

    fn execute(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
        on_type_error: OnTypeError<'db, '_>,
    ) -> Inferred<'db> {
        let mut iterator = args.iter_arguments();
        let first = iterator.next();
        if let Some(x) = iterator.next() {
            todo!()
        } else if let Some(first) = first {
            Inferred::new_unsaved_complex(ComplexPoint::TypeInstance(Box::new(DbType::Type(
                Box::new(first.infer(i_s).class_as_db_type(i_s)),
            ))))
        } else {
            todo!()
        }
    }
}

#[derive(Debug)]
pub struct TypingWithGenerics<'db> {
    node_ref: NodeRef<'db>,
    pub specific: Specific,
}

impl<'db> TypingWithGenerics<'db> {
    pub fn new(node_ref: NodeRef<'db>, specific: Specific) -> Self {
        Self { node_ref, specific }
    }

    pub fn generics(&self) -> SliceType<'db, '_> {
        let primary = self.node_ref.as_primary();
        if let PrimaryContent::GetItem(slice_type) = primary.second() {
            //value.get_item(i_s, &SliceType::new(f, primary.index(), slice_type))
            SliceType::new(self.node_ref.file, primary.index(), slice_type)
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

    fn lookup_internal(&self, i_s: &mut InferenceState<'db, '_>, name: &str) -> LookupResult<'db> {
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

    pub fn mro<'db>(&self, i_s: &mut InferenceState<'db, '_>) -> MroIterator<'db, 'a> {
        let class_infos = i_s.db.python_state.tuple().class_infos(i_s);
        if !self.content.arbitrary_length {
            debug!("TODO Only used TypeVarIndex #0, and not all of them");
        }
        MroIterator::new(
            i_s.db,
            ClassLike::Tuple(*self),
            Some(Generics::DbType(
                self.content
                    .generics
                    .as_ref()
                    .map(|g| g.nth(TypeVarIndex::new(0)).unwrap())
                    .unwrap_or(&ANY),
            )),
            class_infos.mro.iter(),
        )
    }

    pub(super) fn generics(&self) -> Generics<'static, 'a> {
        self.content
            .generics
            .as_ref()
            .map(Generics::new_list)
            .unwrap_or(Generics::None)
    }

    pub fn matches<'db>(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        other: &TupleClass,
        mut matcher: Option<&mut TypeVarMatcher<'db, '_>>,
        variance: Variance,
    ) -> bool {
        if let Some(generics1) = &self.content.generics {
            if let Some(generics2) = &other.content.generics {
                return match (
                    self.content.arbitrary_length,
                    other.content.arbitrary_length,
                ) {
                    (false, false) | (true, true) => {
                        generics1.len() == generics2.len()
                            && Generics::new_list(generics1)
                                .matches(
                                    i_s,
                                    matcher,
                                    Generics::new_list(generics2),
                                    variance,
                                    None,
                                )
                                .bool()
                    }
                    (false, true) => todo!(),
                    (true, false) => {
                        let t1 = Type::from_db_type(
                            i_s.db,
                            generics1.nth(TypeVarIndex::new(0)).unwrap(),
                        );
                        for g in generics2.iter() {
                            let t2 = Type::from_db_type(
                                i_s.db,
                                generics2.nth(TypeVarIndex::new(0)).unwrap(),
                            );
                            if !t1.matches(i_s, matcher.as_deref_mut(), t2, variance) {
                                return false;
                            }
                        }
                        true
                    }
                };
            }
        }
        true
    }

    pub fn as_type_string(&self, db: &Database, style: FormatStyle) -> Box<str> {
        format!(
            "{}{}",
            match style {
                FormatStyle::Short | FormatStyle::MypyOverload => "tuple",
                FormatStyle::Qualified | FormatStyle::MypyRevealType => "builtins.tuple",
            },
            &self.content.as_string(db, style)
        )
        .into()
    }
}

impl<'db, 'a> Value<'db, 'a> for TupleClass<'a> {
    fn kind(&self) -> ValueKind {
        ValueKind::Class
    }

    fn name(&self) -> &'db str {
        "tuple"
    }

    fn lookup_internal(&self, i_s: &mut InferenceState<'db, '_>, name: &str) -> LookupResult<'db> {
        todo!()
    }

    fn as_class_like(&self) -> Option<ClassLike<'db, 'a>> {
        Some(ClassLike::Tuple(TupleClass::new(self.content)))
    }

    fn execute(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
        on_type_error: OnTypeError<'db, '_>,
    ) -> Inferred<'db> {
        Inferred::new_unsaved_complex(ComplexPoint::TypeInstance(Box::new(DbType::Tuple(
            self.content.clone(),
        ))))
    }

    fn description(&self, i_s: &mut InferenceState) -> String {
        base_description!(self) + &self.as_type_string(i_s.db, FormatStyle::Short)
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

    fn lookup_internal(&self, i_s: &mut InferenceState<'db, '_>, name: &str) -> LookupResult<'db> {
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
        slice_type: &SliceType<'db, '_>,
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
        base_description!(self) + &self.content.as_string(i_s.db, FormatStyle::Short)
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

    fn lookup_internal(&self, i_s: &mut InferenceState<'db, '_>, name: &str) -> LookupResult<'db> {
        todo!()
    }

    fn get_item(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        slice_type: &SliceType<'db, '_>,
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
    db: &'db Database,
    pub db_type: &'a DbType,
}

impl<'db, 'a> TypingType<'db, 'a> {
    pub fn new(db: &'db Database, db_type: &'a DbType) -> Self {
        Self { db, db_type }
    }
}

impl<'db, 'a> Value<'db, 'a> for TypingType<'db, 'a> {
    fn kind(&self) -> ValueKind {
        ValueKind::Object
    }

    fn name(&self) -> &'db str {
        "Type"
    }

    fn lookup_internal(&self, i_s: &mut InferenceState<'db, '_>, name: &str) -> LookupResult<'db> {
        todo!()
    }

    fn class(&self, i_s: &mut InferenceState<'db, '_>) -> ClassLike<'db, 'a> {
        ClassLike::TypeWithDbType(self.db_type)
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
                    .as_type_string(self.db, None, FormatStyle::Short),
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

    fn lookup_internal(&self, i_s: &mut InferenceState<'db, '_>, name: &str) -> LookupResult<'db> {
        todo!()
    }

    fn class(&self, i_s: &mut InferenceState<'db, '_>) -> ClassLike<'db, 'a> {
        todo!()
    }

    fn execute(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
        on_type_error: OnTypeError<'db, '_>,
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

#[derive(Debug, Clone, Copy)]
pub struct CallableClass<'a> {
    pub content: &'a CallableContent,
    db_type: &'a DbType,
}

impl<'a> CallableClass<'a> {
    pub fn new(db_type: &'a DbType, content: &'a CallableContent) -> Self {
        Self { db_type, content }
    }

    pub fn as_db_type(&self) -> DbType {
        DbType::Callable(self.content.clone())
    }

    pub fn param_generics<'db>(&self) -> Generics<'db, 'a> {
        self.content
            .params
            .as_ref()
            .map(|p| Generics::Params(p))
            .unwrap_or(Generics::None)
    }

    pub fn result_generics<'db>(&self) -> Generics<'db, 'a> {
        Generics::DbType(&self.content.return_class)
    }

    pub fn as_type_string(&self, db: &Database, style: FormatStyle) -> Box<str> {
        self.content.as_string(db, style).into()
    }
}

impl<'db, 'a> Value<'db, 'a> for CallableClass<'a> {
    fn kind(&self) -> ValueKind {
        ValueKind::Class
    }

    fn name(&self) -> &'db str {
        "Callable"
    }

    fn lookup_internal(&self, i_s: &mut InferenceState<'db, '_>, name: &str) -> LookupResult<'db> {
        debug!("TODO this should at least have the object results");
        LookupResult::None
    }

    fn as_class_like(&self) -> Option<ClassLike<'db, 'a>> {
        Some(ClassLike::Callable(*self))
    }

    fn class(&self, i_s: &mut InferenceState<'db, '_>) -> ClassLike<'db, 'a> {
        ClassLike::TypeWithDbType(self.db_type)
    }

    fn get_item(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        slice_type: &SliceType<'db, '_>,
    ) -> Inferred<'db> {
        slice_type
            .as_node_ref()
            .add_typing_issue(i_s.db, IssueType::OnlyClassTypeApplication);
        Inferred::new_any()
    }
}

#[derive(Debug)]
pub struct Callable<'a> {
    db_type: &'a DbType,
    content: &'a CallableContent,
}

impl<'a> Callable<'a> {
    pub fn new(db_type: &'a DbType, content: &'a CallableContent) -> Self {
        Self { db_type, content }
    }

    pub fn as_db_type(&self) -> DbType {
        DbType::Callable(self.content.clone())
    }

    fn description(&self, i_s: &mut InferenceState) -> String {
        base_description!(self) + &self.content.as_string(i_s.db, FormatStyle::Short)
    }

    pub fn iter_params(&self) -> Option<impl Iterator<Item = &'a CallableParam>> {
        self.content.params.as_ref().map(|params| params.iter())
    }
}

impl<'db, 'a> Value<'db, 'a> for Callable<'a> {
    fn kind(&self) -> ValueKind {
        ValueKind::Object
    }

    fn name(&self) -> &'db str {
        "Callable"
    }

    fn lookup_internal(&self, i_s: &mut InferenceState<'db, '_>, name: &str) -> LookupResult<'db> {
        todo!()
    }

    fn class(&self, i_s: &mut InferenceState<'db, '_>) -> ClassLike<'db, 'a> {
        ClassLike::Callable(CallableClass::new(self.db_type, self.content))
    }

    fn execute(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
        on_type_error: OnTypeError<'db, '_>,
    ) -> Inferred<'db> {
        let mut type_vars = vec![]; // todo!()
        if let Some(params) = &self.content.params {
            for param in params.iter() {
                param
                    .db_type
                    .scan_for_late_bound_type_vars(i_s.db, &mut type_vars)
            }
        }
        let type_vars = TypeVars::from_vec(type_vars);
        let mut finder = TypeVarMatcher::from_callable(
            self,
            args,
            Some(&type_vars),
            TypeVarType::LateBound,
            on_type_error,
        );
        finder.matches_signature(i_s); // TODO this should be different
        let g_o = Type::from_db_type(i_s.db, &self.content.return_class);
        g_o.execute_and_resolve_type_vars(i_s, None, Some(&mut finder))
    }

    fn description(&self, i_s: &mut InferenceState) -> String {
        base_description!(self) + &self.content.as_string(i_s.db, FormatStyle::Short)
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

    fn lookup_internal(&self, i_s: &mut InferenceState<'db, '_>, name: &str) -> LookupResult<'db> {
        todo!()
    }

    fn execute(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
        on_type_error: OnTypeError<'db, '_>,
    ) -> Inferred<'db> {
        let mut iterator = args.iter_arguments();
        let arg = iterator.next().unwrap_or_else(|| todo!());

        let s = arg
            .infer(i_s)
            .class_as_type(i_s)
            .as_string(i_s, None, FormatStyle::MypyRevealType);
        args.as_node_ref().add_typing_issue(
            i_s.db,
            IssueType::Note(format!("Revealed type is {s:?}").into()),
        );
        if iterator.next().is_some() {
            todo!()
        }
        Inferred::new_none()
    }
}

pub struct TypeVarInstance<'db, 'a> {
    db: &'db Database,
    db_type: &'a DbType,
    type_var_usage: &'a TypeVarUsage,
}

impl<'db, 'a> TypeVarInstance<'db, 'a> {
    pub fn new(db: &'db Database, db_type: &'a DbType, type_var_usage: &'a TypeVarUsage) -> Self {
        Self {
            db,
            db_type,
            type_var_usage,
        }
    }
}

impl<'db, 'a> Value<'db, 'a> for TypeVarInstance<'db, 'a> {
    fn kind(&self) -> ValueKind {
        ValueKind::TypeParameter
    }

    fn name(&self) -> &'db str {
        self.type_var_usage.type_var.name(self.db)
    }

    fn lookup_internal(&self, i_s: &mut InferenceState<'db, '_>, name: &str) -> LookupResult<'db> {
        if !self.type_var_usage.type_var.restrictions.is_empty() {
            debug!("TODO type var values");
            /*
            for db_type in self.type_var_usage.type_var.restrictions.iter() {
                return match db_type {
                    DbType::Class(link) => Instance::new(
                        Class::from_position(NodeRef::from_link(i_s.db, *link), Generics::None, None)
                            .unwrap(),
                        &Inferred::new_unsaved_complex(ComplexPoint::Instance(*link, None)),
                    )
                    .lookup_internal(i_s, name),
                    _ => todo!("{:?}", db_type),
                }
            }
            */
        }
        if let Some(db_type) = &self.type_var_usage.type_var.bound {
            run_on_db_type(
                i_s,
                db_type,
                &mut |i_s, v| {
                    let result = v.lookup_internal(i_s, name);
                    if matches!(result, LookupResult::None) {
                        debug!(
                            "Item \"{}\" of the upper bound \"{}\" of type variable \"{}\" has no attribute \"{}\"",
                            v.class(i_s).as_string(i_s, None, FormatStyle::Short),
                            db_type.as_type_string(i_s.db, None, FormatStyle::Short),
                            self.name(),
                            name,
                        );
                    }
                    result
                },
                &|i_s, a, b| a.union(b),
                &mut |i_s| todo!(),
            )
        } else {
            let s = &i_s.db.python_state;
            // TODO it's kind of stupid that we recreate an instance object here all the time, we
            // should just use a precreated object() from somewhere.
            Instance::new(s.object_class(), None).lookup_internal(i_s, name)
        }
    }

    fn class(&self, i_s: &mut InferenceState<'db, '_>) -> ClassLike<'db, 'a> {
        ClassLike::TypeVar(self.type_var_usage)
    }
}

impl fmt::Debug for TypeVarInstance<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("TypeVarInstance")
            .field("db_type", &self.db_type)
            .finish()
    }
}

#[derive(Debug)]
pub struct TypeVarClass();

pub fn maybe_type_var<'db>(
    i_s: &mut InferenceState<'db, '_>,
    args: &dyn Arguments<'db>,
) -> Option<TypeVar> {
    let mut iterator = args.iter_arguments();
    if let Some(first_arg) = iterator.next() {
        let result = if let Argument::Positional(_, name_node) = first_arg {
            name_node
                .as_named_expression()
                .maybe_single_string_literal()
                .map(|py_string| (name_node, py_string))
        } else {
            None
        };
        let (name_node, py_string) = match result {
            Some(result) => result,
            None => {
                first_arg
                    .as_node_ref()
                    .add_typing_issue(i_s.db, IssueType::TypeVarFirstArgMustBeString);
                return None;
            }
        };
        if let Some(name) = py_string.in_simple_assignment() {
            if name.as_code() != py_string.content() {
                name_node.add_typing_issue(
                    i_s.db,
                    IssueType::TypeVarNameMismatch {
                        string_name: Box::from(py_string.content()),
                        variable_name: Box::from(name.as_code()),
                    },
                );
            }
        } else {
            todo!()
        }

        let mut restrictions = vec![];
        let mut bound = None;
        let mut covariant = false;
        let mut contravariant = false;
        for arg in iterator {
            match arg {
                Argument::Positional(_, node) => {
                    let mut inference = node.file.inference(i_s);
                    if let Some(t) = inference
                        .compute_type_var_constraint(node.as_named_expression().expression())
                    {
                        restrictions.push(t);
                    } else {
                        return None;
                    }
                }
                Argument::Keyword(name, node) => match name {
                    "covariant" => {
                        let code = node.as_expression().as_code();
                        match code {
                            "True" => covariant = true,
                            "False" => (),
                            _ => {
                                node.add_typing_issue(
                                    i_s.db,
                                    IssueType::TypeVarVarianceMustBeBool {
                                        argument: "covariant",
                                    },
                                );
                                return None;
                            }
                        }
                    }
                    "contravariant" => {
                        let code = node.as_expression().as_code();
                        match code {
                            "True" => contravariant = true,
                            "False" => (),
                            _ => {
                                node.add_typing_issue(
                                    i_s.db,
                                    IssueType::TypeVarVarianceMustBeBool {
                                        argument: "contravariant",
                                    },
                                );
                                return None;
                            }
                        }
                    }
                    "bound" => {
                        if !restrictions.is_empty() {
                            node.add_typing_issue(i_s.db, IssueType::TypeVarValuesAndUpperBound);
                            return None;
                        }
                        if let Some(t) = node
                            .file
                            .inference(i_s)
                            .compute_type_var_constraint(node.as_expression())
                        {
                            bound = Some(t)
                        } else {
                            return None;
                        }
                    }
                    _ => {
                        node.add_typing_issue(
                            i_s.db,
                            IssueType::TypeVarUnexpectedArgument {
                                argument_name: Box::from(name),
                            },
                        );
                        return None;
                    }
                },
                Argument::Inferred(v, _) => unreachable!(),
                Argument::SlicesTuple(slices) => return None,
            }
        }
        if restrictions.len() == 1 {
            args.as_node_ref()
                .add_typing_issue(i_s.db, IssueType::TypeVarOnlySingleRestriction);
            return None;
        }
        return Some(TypeVar {
            name_string: PointLink {
                file: name_node.file_index(),
                node_index: py_string.index(),
            },
            restrictions: restrictions.into_boxed_slice(),
            bound,
            variance: match (covariant, contravariant) {
                (false, false) => Variance::Invariant,
                (true, false) => Variance::Covariant,
                (false, true) => Variance::Contravariant,
                (true, true) => {
                    args.as_node_ref()
                        .add_typing_issue(i_s.db, IssueType::TypeVarCoAndContravariant);
                    return None;
                }
            },
        });
    } else {
        args.as_node_ref()
            .add_typing_issue(i_s.db, IssueType::TypeVarTooFewArguments);
    }
    None
}

impl<'db, 'a> Value<'db, 'a> for TypeVarClass {
    fn kind(&self) -> ValueKind {
        ValueKind::Class
    }

    fn name(&self) -> &'db str {
        "TypeVar"
    }

    fn lookup_internal(&self, i_s: &mut InferenceState<'db, '_>, name: &str) -> LookupResult<'db> {
        LookupResult::None
    }

    fn execute(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
        on_type_error: OnTypeError<'db, '_>,
    ) -> Inferred<'db> {
        if let Some(t) = maybe_type_var(i_s, args) {
            Inferred::new_unsaved_complex(ComplexPoint::TypeVar(Rc::new(t)))
        } else {
            Inferred::new_unknown()
        }
    }

    fn class(&self, i_s: &mut InferenceState<'db, '_>) -> ClassLike<'db, 'a> {
        ClassLike::TypingClass(TypingClass::new(Specific::TypingType))
    }
}
