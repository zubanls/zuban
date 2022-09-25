use std::borrow::Cow;
use std::fmt;
use std::rc::Rc;

use parsa_python_ast::PrimaryContent;

use super::{Class, Instance, LookupResult, OnTypeError, Value, ValueKind};
use crate::arguments::{ArgumentKind, Arguments};
use crate::database::{
    ComplexPoint, Database, DbType, FormatStyle, PointLink, Specific, TupleContent, TypeVar,
    TypeVarUsage, Variance,
};
use crate::debug;
use crate::diagnostics::IssueType;
use crate::getitem::{SliceType, SliceTypeContent};
use crate::inference_state::InferenceState;
use crate::inferred::{run_on_db_type, Inferred};
use crate::matching::{FormatData, ResultContext, Type};
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

    fn name(&self) -> &'a str {
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

    fn lookup_internal(&self, i_s: &mut InferenceState, name: &str) -> LookupResult {
        todo!()
    }

    fn as_typing_class(&self) -> Option<&TypingClass> {
        Some(self)
    }

    fn get_item(&self, i_s: &mut InferenceState, slice_type: &SliceType) -> Inferred {
        slice_type
            .file
            .inference(i_s)
            .compute_type_application_on_typing_class(self.specific, *slice_type)
    }

    fn as_type(&self, i_s: &mut InferenceState<'db, '_>) -> Type<'a> {
        match self.specific {
            Specific::TypingGeneric
            | Specific::TypingProtocol
            | Specific::TypingUnion
            | Specific::TypingOptional => todo!(),
            Specific::TypingTuple => Type::new(&i_s.db.python_state.type_of_arbitrary_tuple),
            Specific::TypingCallable => todo!(),
            Specific::TypingType => Type::new(&i_s.db.python_state.type_of_any),
            _ => unreachable!("{:?}", self.specific),
        }
    }

    fn execute(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
        result_context: ResultContext,
        on_type_error: OnTypeError,
    ) -> Inferred {
        let mut iterator = args.iter_arguments();
        let first = iterator.next();
        if let Some(x) = iterator.next() {
            todo!()
        } else if let Some(first) = first {
            Inferred::new_unsaved_complex(ComplexPoint::TypeInstance(Box::new(DbType::Type(
                Box::new(
                    first
                        .infer(i_s, ResultContext::Unknown)
                        .class_as_db_type(i_s),
                ),
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

    pub fn generics(&self) -> SliceType {
        let primary = self.node_ref.as_primary();
        if let PrimaryContent::GetItem(slice_type) = primary.second() {
            //value.get_item(i_s, &SliceType::new(f, primary.index(), slice_type))
            SliceType::new(self.node_ref.file, primary.index(), slice_type)
        } else {
            unreachable!()
        }
    }
}

impl<'db, 'a> Value<'db, 'a> for TypingWithGenerics<'a> {
    fn kind(&self) -> ValueKind {
        ValueKind::Class
    }

    fn name(&self) -> &'a str {
        match self.specific {
            Specific::TypingGeneric => "Generic",
            Specific::TypingProtocol => "Protocol",
            _ => unreachable!(),
        }
    }

    fn lookup_internal(&self, i_s: &mut InferenceState, name: &str) -> LookupResult {
        todo!()
    }

    fn as_typing_with_generics(&self, i_s: &mut InferenceState) -> Option<&Self> {
        Some(self)
    }
}

#[derive(Debug)]
pub struct TypingClassVar();

impl<'db, 'a> Value<'db, 'a> for TypingClassVar {
    fn kind(&self) -> ValueKind {
        ValueKind::Class
    }

    fn name(&self) -> &'a str {
        "ClassVar"
    }

    fn lookup_internal(&self, i_s: &mut InferenceState, name: &str) -> LookupResult {
        todo!()
    }

    fn get_item(&self, i_s: &mut InferenceState, slice_type: &SliceType) -> Inferred {
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

pub struct TypingType<'a> {
    db: &'a Database,
    full_db_type: Cow<'a, DbType>,
    pub db_type: &'a DbType,
}

impl<'db, 'a> TypingType<'a> {
    pub fn new(db: &'a Database, full_db_type: Cow<'a, DbType>, db_type: &'a DbType) -> Self {
        Self {
            db,
            full_db_type,
            db_type,
        }
    }
}

impl<'db, 'a> Value<'db, 'a> for TypingType<'a> {
    fn kind(&self) -> ValueKind {
        ValueKind::Object
    }

    fn name(&self) -> &'a str {
        "Type"
    }

    fn lookup_internal(&self, i_s: &mut InferenceState, name: &str) -> LookupResult {
        match self.db_type {
            DbType::TypeVar(t) => {
                if let Some(bound) = &t.type_var.bound {
                    TypingType::new(
                        self.db,
                        Cow::Owned(DbType::Type(Box::new(bound.clone()))),
                        bound,
                    )
                    .lookup_internal(i_s, name)
                } else {
                    todo!("{t:?}")
                }
            }
            DbType::Class(link, generics_list) => {
                Class::from_db_type(i_s.db, *link, generics_list).lookup_internal(i_s, name)
            }
            DbType::Callable(_) => LookupResult::None,
            _ => todo!("{:?}", self.db_type),
        }
    }

    fn get_item(&self, i_s: &mut InferenceState, slice_type: &SliceType) -> Inferred {
        slice_type
            .as_node_ref()
            .add_typing_issue(i_s.db, IssueType::OnlyClassTypeApplication);
        Inferred::new_any()
    }

    fn as_type(&self, i_s: &mut InferenceState<'db, '_>) -> Type<'a> {
        Type::Type(Cow::Owned(DbType::Type(Box::new(self.db_type.clone()))))
    }

    fn execute(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
        result_context: ResultContext,
        on_type_error: OnTypeError<'db, '_>,
    ) -> Inferred {
        match self.db_type {
            DbType::Tuple(_) => {
                debug!("TODO this does not check the arguments");
                Inferred::new_unsaved_complex(ComplexPoint::TypeInstance(Box::new(
                    self.db_type.clone(),
                )))
            }
            DbType::Class(link, generics_list) => Class::from_db_type(i_s.db, *link, generics_list)
                .execute(i_s, args, result_context, on_type_error),
            DbType::TypeVar(t) => {
                if let Some(bound) = &t.type_var.bound {
                    TypingType::new(
                        self.db,
                        Cow::Owned(DbType::Type(Box::new(bound.clone()))),
                        bound,
                    )
                    .execute(i_s, args, result_context, on_type_error)
                } else {
                    todo!("{t:?}")
                }
            }
            _ => todo!("{:?}", self.db_type),
        }
    }
}

impl<'db> fmt::Debug for TypingType<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("TypingType")
            .field(
                "db_type",
                &self.db_type.format(&FormatData::new_short(self.db)),
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

    fn name(&self) -> &'a str {
        "cast"
    }

    fn lookup_internal(&self, i_s: &mut InferenceState, name: &str) -> LookupResult {
        todo!()
    }

    fn as_type(&self, i_s: &mut InferenceState<'db, '_>) -> Type<'a> {
        todo!()
    }

    fn execute(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
        result_context: ResultContext,
        on_type_error: OnTypeError<'db, '_>,
    ) -> Inferred {
        let mut result = None;
        let mut count = 0;
        let mut had_non_positional = false;
        for arg in args.iter_arguments() {
            // TODO something like *Iterable[str] looped forever and then we put in this hack
            if arg.in_args_or_kwargs_and_arbitrary_len() {
                count = 2;
                had_non_positional = true;
                break;
            }
            match arg.kind {
                ArgumentKind::Positional {
                    position, node_ref, ..
                } => {
                    if position == 1 {
                        result = Some(
                            arg.as_node_ref()
                                .file
                                .inference(i_s)
                                .compute_cast_target(node_ref),
                        )
                    } else {
                        arg.infer(i_s, ResultContext::Unknown);
                    }
                }
                _ => {
                    arg.infer(i_s, ResultContext::Unknown);
                    had_non_positional = true;
                }
            }
            count += 1;
        }
        if count != 2 {
            args.as_node_ref().add_typing_issue(
                i_s.db,
                IssueType::ArgumentIssue(Box::from("\"cast\" expects 2 arguments")),
            );
            return Inferred::new_any();
        } else if had_non_positional {
            args.as_node_ref().add_typing_issue(
                i_s.db,
                IssueType::ArgumentIssue(Box::from(
                    "\"cast\" must be called with 2 positional arguments",
                )),
            );
        }
        result.unwrap_or_else(Inferred::new_any)
    }
}

#[derive(Debug)]
pub struct RevealTypeFunction();

impl<'db, 'a> Value<'db, 'a> for RevealTypeFunction {
    fn kind(&self) -> ValueKind {
        ValueKind::Function
    }

    fn name(&self) -> &'static str {
        "reveal_type"
    }

    fn lookup_internal(&self, i_s: &mut InferenceState, name: &str) -> LookupResult {
        todo!()
    }

    fn execute(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
        result_context: ResultContext,
        on_type_error: OnTypeError<'db, '_>,
    ) -> Inferred {
        let mut iterator = args.iter_arguments();
        let arg = iterator.next().unwrap_or_else(|| todo!());

        let s = arg.infer(i_s, result_context).format(
            i_s,
            &FormatData::with_style(i_s.db, FormatStyle::MypyRevealType),
        );
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

pub struct TypeVarInstance<'a> {
    db: &'a Database,
    db_type: &'a DbType,
    type_var_usage: &'a TypeVarUsage,
}

impl<'a> TypeVarInstance<'a> {
    pub fn new(db: &'a Database, db_type: &'a DbType, type_var_usage: &'a TypeVarUsage) -> Self {
        Self {
            db,
            db_type,
            type_var_usage,
        }
    }
}

impl<'db, 'a> Value<'db, 'a> for TypeVarInstance<'a> {
    fn kind(&self) -> ValueKind {
        ValueKind::TypeParameter
    }

    fn name(&self) -> &'a str {
        self.type_var_usage.type_var.name(self.db)
    }

    fn lookup_internal(&self, i_s: &mut InferenceState, name: &str) -> LookupResult {
        if !self.type_var_usage.type_var.restrictions.is_empty() {
            debug!("TODO type var values");
            /*
            for db_type in self.type_var_usage.type_var.restrictions.iter() {
                return match db_type {
                    DbType::Class(link) => Instance::new(
                        Class::from_position(NodeRef::from_link(i_s.db, *link), Generics::Any, None)
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
                            v.as_type(i_s).format(&FormatData::new_short(i_s.db)),
                            db_type.format(&FormatData::new_short(i_s.db)),
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

    fn as_type(&self, i_s: &mut InferenceState<'db, '_>) -> Type<'a> {
        Type::new(self.db_type)
    }
}

impl fmt::Debug for TypeVarInstance<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("TypeVarInstance")
            .field("db_type", &self.db_type)
            .finish()
    }
}

#[derive(Debug)]
pub struct TypeVarClass();

pub fn maybe_type_var(i_s: &mut InferenceState, args: &dyn Arguments) -> Option<TypeVar> {
    let mut iterator = args.iter_arguments();
    if let Some(first_arg) = iterator.next() {
        let result = if let ArgumentKind::Positional { node_ref, .. } = first_arg.kind {
            node_ref
                .as_named_expression()
                .maybe_single_string_literal()
                .map(|py_string| (node_ref, py_string))
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
            match arg.kind {
                ArgumentKind::Positional { node_ref, .. } => {
                    let mut inference = node_ref.file.inference(i_s);
                    if let Some(t) = inference
                        .compute_type_var_constraint(node_ref.as_named_expression().expression())
                    {
                        restrictions.push(t);
                    } else {
                        return None;
                    }
                }
                ArgumentKind::Keyword { key, node_ref, .. } => match key {
                    "covariant" => {
                        let code = node_ref.as_expression().as_code();
                        match code {
                            "True" => covariant = true,
                            "False" => (),
                            _ => {
                                node_ref.add_typing_issue(
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
                        let code = node_ref.as_expression().as_code();
                        match code {
                            "True" => contravariant = true,
                            "False" => (),
                            _ => {
                                node_ref.add_typing_issue(
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
                            node_ref
                                .add_typing_issue(i_s.db, IssueType::TypeVarValuesAndUpperBound);
                            return None;
                        }
                        if let Some(t) = node_ref
                            .file
                            .inference(i_s)
                            .compute_type_var_constraint(node_ref.as_expression())
                        {
                            bound = Some(t)
                        } else {
                            return None;
                        }
                    }
                    _ => {
                        node_ref.add_typing_issue(
                            i_s.db,
                            IssueType::TypeVarUnexpectedArgument {
                                argument_name: Box::from(key),
                            },
                        );
                        return None;
                    }
                },
                ArgumentKind::Inferred { .. } => unreachable!(),
                ArgumentKind::SlicesTuple { slices, .. } => return None,
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

    fn name(&self) -> &'a str {
        "TypeVar"
    }

    fn lookup_internal(&self, i_s: &mut InferenceState, name: &str) -> LookupResult {
        LookupResult::None
    }

    fn execute(
        &self,
        i_s: &mut InferenceState,
        args: &dyn Arguments,
        result_context: ResultContext,
        on_type_error: OnTypeError,
    ) -> Inferred {
        if let Some(t) = maybe_type_var(i_s, args) {
            Inferred::new_unsaved_complex(ComplexPoint::TypeVar(Rc::new(t)))
        } else {
            Inferred::new_unknown()
        }
    }

    fn as_type(&self, i_s: &mut InferenceState<'db, '_>) -> Type<'a> {
        Type::Type(Cow::Borrowed(&i_s.db.python_state.type_of_object))
    }
}
