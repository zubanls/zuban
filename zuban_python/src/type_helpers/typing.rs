use std::fmt;
use std::rc::Rc;

use super::{lookup_on_enum_class, Class};
use crate::arguments::{ArgumentKind, Arguments};
use crate::database::{
    ComplexPoint, Database, DbType, FormatStyle, NewType, ParamSpec, PointLink, Specific, TypeVar,
    TypeVarKind, TypeVarLike, TypeVarName, TypeVarTuple, Variance,
};
use crate::debug;
use crate::diagnostics::IssueType;
use crate::file::{new_collections_named_tuple, new_typing_named_tuple};
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::matching::{FormatData, LookupKind, LookupResult, OnTypeError, ResultContext, Type};
use crate::node_ref::NodeRef;

#[derive(Debug, Clone, Copy)]
pub struct TypingClass {
    pub specific: Specific,
}

impl TypingClass {
    pub fn new(specific: Specific) -> Self {
        Self { specific }
    }

    pub fn execute<'db>(
        &self,
        i_s: &InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
        result_context: &mut ResultContext,
        on_type_error: OnTypeError<'db, '_>,
    ) -> Inferred {
        if self.specific == Specific::TypingNamedTuple {
            return match new_typing_named_tuple(i_s, args) {
                Some(rc) => Inferred::new_unsaved_complex(ComplexPoint::NamedTupleDefinition(
                    Rc::new(DbType::NamedTuple(rc)),
                )),
                None => Inferred::new_any(),
            };
        }
        if self.specific == Specific::CollectionsNamedTuple {
            i_s.db
                .python_state
                .collections_namedtuple_function()
                .execute(i_s, args, result_context, on_type_error);
            return match new_collections_named_tuple(i_s, args) {
                Some(rc) => Inferred::new_unsaved_complex(ComplexPoint::NamedTupleDefinition(
                    Rc::new(DbType::NamedTuple(rc)),
                )),
                None => Inferred::new_any(),
            };
        }
        let mut iterator = args.iter();
        let first = iterator.next();
        if let Some(x) = iterator.next() {
            todo!()
        } else if let Some(first) = first {
            Inferred::from_type(DbType::Type(Rc::new(
                first
                    .infer(i_s, &mut ResultContext::Unknown)
                    .as_db_type(i_s),
            )))
        } else {
            todo!()
        }
    }
}

pub struct TypingType<'a> {
    db: &'a Database,
    pub db_type: &'a DbType,
}

impl<'a> TypingType<'a> {
    pub fn new(db: &'a Database, db_type: &'a DbType) -> Self {
        Self { db, db_type }
    }

    pub fn lookup(
        &self,
        i_s: &InferenceState,
        node_ref: NodeRef,
        name: &str,
        kind: LookupKind,
        result_context: &mut ResultContext,
    ) -> LookupResult {
        match self.db_type {
            DbType::TypeVar(t) => match &t.type_var.kind {
                TypeVarKind::Bound(bound) => TypingType::new(self.db, bound).lookup(
                    i_s,
                    node_ref,
                    name,
                    kind,
                    result_context,
                ),
                TypeVarKind::Constraints(_) => todo!(),
                TypeVarKind::Unrestricted => todo!(),
            },
            DbType::Class(g) => {
                Class::from_generic_class(i_s.db, g).lookup(i_s, node_ref, name, kind)
            }
            DbType::Literal(l) => i_s
                .db
                .python_state
                .literal_instance(&l.kind)
                .class
                .lookup(i_s, node_ref, name, kind),
            DbType::Callable(_) => LookupResult::None,
            DbType::Self_ => i_s
                .current_class()
                .unwrap()
                .lookup(i_s, node_ref, name, kind),
            DbType::Any => LookupResult::any(),
            t @ DbType::Enum(e) => lookup_on_enum_class(i_s, node_ref, e, name, result_context),
            DbType::NamedTuple(nt) => match name {
                "__new__" => LookupResult::UnknownName(Inferred::from_type(DbType::Callable(
                    nt.__new__.clone(),
                ))),
                _ => todo!(),
            },
            DbType::Tuple(tup) => i_s
                .db
                .python_state
                .tuple_class(i_s.db, tup)
                .lookup(i_s, node_ref, name, kind),
            _ => todo!("{name} on {:?}", self.db_type),
        }
    }
}

impl fmt::Debug for TypingType<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("TypingType")
            .field("db_type", &Type::new(self.db_type).format_short(self.db))
            .finish()
    }
}

#[derive(Debug)]
pub struct TypingCast();

impl<'db> TypingCast {
    pub fn execute(
        &self,
        i_s: &InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
        result_context: &mut ResultContext,
        on_type_error: OnTypeError<'db, '_>,
    ) -> Inferred {
        let mut result = None;
        let mut count = 0;
        let mut had_non_positional = false;
        for arg in args.iter() {
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
                        arg.infer(i_s, &mut ResultContext::ExpectUnused);
                    }
                }
                _ => {
                    arg.infer(i_s, &mut ResultContext::ExpectUnused);
                    had_non_positional = true;
                }
            }
            count += 1;
        }
        if count != 2 {
            args.as_node_ref().add_issue(
                i_s,
                IssueType::ArgumentIssue(Box::from("\"cast\" expects 2 arguments")),
            );
            return Inferred::new_any();
        } else if had_non_positional {
            args.as_node_ref().add_issue(
                i_s,
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

impl RevealTypeFunction {
    pub fn execute<'db>(
        &self,
        i_s: &InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
        result_context: &mut ResultContext,
        on_type_error: OnTypeError<'db, '_>,
    ) -> Inferred {
        let mut iterator = args.iter();
        let arg = iterator.next().unwrap_or_else(|| todo!());

        let inferred = if matches!(result_context, ResultContext::ExpectUnused) {
            // For some reason mypy wants to generate a literal here if possible.
            arg.infer(i_s, &mut ResultContext::RevealType)
        } else {
            arg.infer(i_s, result_context)
        };
        let s = inferred.format(
            i_s,
            &FormatData::with_style(i_s.db, FormatStyle::MypyRevealType),
        );
        arg.as_node_ref().add_issue(
            i_s,
            IssueType::Note(format!("Revealed type is \"{s}\"").into()),
        );
        if iterator.next().is_some() {
            todo!()
        }
        inferred
    }
}

pub fn execute_assert_type<'db>(
    i_s: &InferenceState<'db, '_>,
    args: &dyn Arguments<'db>,
    on_type_error: OnTypeError<'db, '_>,
) -> Inferred {
    if args.iter().count() != 2 {
        args.as_node_ref().add_issue(
            i_s,
            IssueType::ArgumentIssue(Box::from("\"assert_type\" expects 2 arguments")),
        );
        return Inferred::new_any();
    };

    let mut iterator = args.iter();
    let first = iterator.next().unwrap();
    let second = iterator.next().unwrap();

    let error_non_positional = || {
        args.as_node_ref().add_issue(
            i_s,
            IssueType::ArgumentIssue(Box::from(
                "\"assert_type\" must be called with 2 positional arguments",
            )),
        );
        Inferred::new_any()
    };
    if !matches!(&first.kind, ArgumentKind::Positional { .. }) {
        return error_non_positional();
    }
    let ArgumentKind::Positional { node_ref: second_node_ref, ..}= second.kind else {
        return error_non_positional()
    };
    let first = first.infer(i_s, &mut ResultContext::ExpectLiteral);
    let first_type = first.as_type(i_s);

    let second = second_node_ref
        .file
        .inference(i_s)
        .compute_cast_target(second_node_ref);
    let second_type = second.as_type(i_s);
    if first_type.as_ref() != second_type.as_ref() {
        args.as_node_ref().add_issue(
            i_s,
            IssueType::InvalidAssertType {
                actual: first_type.format_short(i_s.db),
                wanted: second_type.format_short(i_s.db),
            },
        );
    }
    first
}

#[derive(Debug)]
pub struct TypeVarClass();

impl TypeVarClass {
    pub fn execute(
        &self,
        i_s: &InferenceState,
        args: &dyn Arguments,
        result_context: &mut ResultContext,
        on_type_error: OnTypeError,
    ) -> Inferred {
        if let Some(t) = maybe_type_var(i_s, args, result_context) {
            Inferred::new_unsaved_complex(ComplexPoint::TypeVarLike(t))
        } else {
            Inferred::new_unknown()
        }
    }
}

fn maybe_type_var(
    i_s: &InferenceState,
    args: &dyn Arguments,
    result_context: &ResultContext,
) -> Option<TypeVarLike> {
    if !matches!(result_context, ResultContext::AssignmentNewDefinition) {
        args.as_node_ref()
            .add_issue(i_s, IssueType::UnexpectedTypeForTypeVar);
        return None;
    }
    let mut iterator = args.iter();
    if let Some(first_arg) = iterator.next() {
        let result = if let ArgumentKind::Positional { node_ref, .. } = first_arg.kind {
            node_ref
                .as_named_expression()
                .maybe_single_string_literal()
                .map(|py_string| (node_ref, py_string))
        } else {
            debug!("TODO this should probably add an error");
            None
        };
        let (name_node, py_string) = match result {
            Some(result) => result,
            None => {
                first_arg.as_node_ref().add_issue(
                    i_s,
                    IssueType::TypeVarLikeFirstArgMustBeString {
                        class_name: "TypeVar",
                    },
                );
                return None;
            }
        };
        if let Some(name) = py_string.in_simple_assignment() {
            if name.as_code() != py_string.content() {
                name_node.add_issue(
                    i_s,
                    IssueType::TypeVarNameMismatch {
                        class_name: "TypeVar",
                        string_name: Box::from(py_string.content()),
                        variable_name: Box::from(name.as_code()),
                    },
                );
            }
        } else {
            todo!()
        }

        let mut constraints = vec![];
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
                        constraints.push(t);
                    } else {
                        //
                        debug!("TODO invalid type var constraint, this needs a lint?");
                        return None;
                    }
                }
                ArgumentKind::Keyword {
                    key,
                    node_ref,
                    expression,
                    ..
                } => match key {
                    "covariant" => {
                        let code = expression.as_code();
                        match code {
                            "True" => covariant = true,
                            "False" => (),
                            _ => {
                                node_ref.add_issue(
                                    i_s,
                                    IssueType::TypeVarVarianceMustBeBool {
                                        argument: "covariant",
                                    },
                                );
                                return None;
                            }
                        }
                    }
                    "contravariant" => {
                        let code = expression.as_code();
                        match code {
                            "True" => contravariant = true,
                            "False" => (),
                            _ => {
                                node_ref.add_issue(
                                    i_s,
                                    IssueType::TypeVarVarianceMustBeBool {
                                        argument: "contravariant",
                                    },
                                );
                                return None;
                            }
                        }
                    }
                    "bound" => {
                        if !constraints.is_empty() {
                            node_ref.add_issue(i_s, IssueType::TypeVarValuesAndUpperBound);
                            return None;
                        }
                        if let Some(t) = node_ref
                            .file
                            .inference(i_s)
                            .compute_type_var_constraint(expression)
                        {
                            bound = Some(t)
                        } else {
                            debug!("TODO invalid type var bound, this needs a lint?");
                            return None;
                        }
                    }
                    _ => {
                        node_ref.add_issue(
                            i_s,
                            IssueType::UnexpectedArgument {
                                class_name: "TypeVar",
                                argument_name: Box::from(key),
                            },
                        );
                        return None;
                    }
                },
                ArgumentKind::Comprehension { .. } => {
                    arg.as_node_ref()
                        .add_issue(i_s, IssueType::UnexpectedComprehension);
                    return None;
                }
                ArgumentKind::Inferred { .. }
                | ArgumentKind::SlicesTuple { .. }
                | ArgumentKind::Overridden { .. }
                | ArgumentKind::ParamSpec { .. } => {
                    arg.as_node_ref()
                        .add_issue(i_s, IssueType::UnexpectedArgumentTo { name: "TypeVar" });
                }
            }
        }
        if constraints.len() == 1 {
            args.as_node_ref()
                .add_issue(i_s, IssueType::TypeVarOnlySingleRestriction);
            return None;
        }
        let kind = if let Some(bound) = bound {
            debug_assert!(constraints.is_empty());
            TypeVarKind::Bound(bound)
        } else if !constraints.is_empty() {
            TypeVarKind::Constraints(constraints.into())
        } else {
            TypeVarKind::Unrestricted
        };
        Some(TypeVarLike::TypeVar(Rc::new(TypeVar {
            name_string: TypeVarName::PointLink(PointLink {
                file: name_node.file_index(),
                node_index: py_string.index(),
            }),
            kind,
            variance: match (covariant, contravariant) {
                (false, false) => Variance::Invariant,
                (true, false) => Variance::Covariant,
                (false, true) => Variance::Contravariant,
                (true, true) => {
                    args.as_node_ref()
                        .add_issue(i_s, IssueType::TypeVarCoAndContravariant);
                    return None;
                }
            },
        })))
    } else {
        args.as_node_ref().add_issue(
            i_s,
            IssueType::TypeVarLikeTooFewArguments {
                class_name: "TypeVar",
            },
        );
        None
    }
}

#[derive(Debug)]
pub struct TypeVarTupleClass();

impl TypeVarTupleClass {
    pub fn execute(
        &self,
        i_s: &InferenceState,
        args: &dyn Arguments,
        result_context: &mut ResultContext,
        on_type_error: OnTypeError,
    ) -> Inferred {
        if let Some(t) = maybe_type_var_tuple(i_s, args, result_context) {
            Inferred::new_unsaved_complex(ComplexPoint::TypeVarLike(t))
        } else {
            Inferred::new_unknown()
        }
    }
}

fn maybe_type_var_tuple(
    i_s: &InferenceState,
    args: &dyn Arguments,
    result_context: &ResultContext,
) -> Option<TypeVarLike> {
    if !matches!(result_context, ResultContext::AssignmentNewDefinition) {
        args.as_node_ref()
            .add_issue(i_s, IssueType::UnexpectedTypeForTypeVar);
        return None;
    }
    let mut iterator = args.iter();
    if let Some(first_arg) = iterator.next() {
        let result = if let ArgumentKind::Positional { node_ref, .. } = first_arg.kind {
            node_ref
                .as_named_expression()
                .maybe_single_string_literal()
                .map(|py_string| (node_ref, py_string))
        } else {
            debug!("TODO type var tuple why does this not need an error?");
            None
        };
        let (name_node, py_string) = match result {
            Some(result) => result,
            None => {
                first_arg.as_node_ref().add_issue(
                    i_s,
                    IssueType::TypeVarLikeFirstArgMustBeString {
                        class_name: "TypeVarTuple",
                    },
                );
                return None;
            }
        };
        if let Some(name) = py_string.in_simple_assignment() {
            if name.as_code() != py_string.content() {
                name_node.add_issue(
                    i_s,
                    IssueType::TypeVarNameMismatch {
                        class_name: "TypeVarTuple",
                        string_name: Box::from(py_string.content()),
                        variable_name: Box::from(name.as_code()),
                    },
                );
            }
        } else {
            todo!()
        }

        let default = None;
        for arg in iterator {
            match arg.kind {
                ArgumentKind::Positional { node_ref, .. } => {
                    node_ref.add_issue(i_s, IssueType::TypeVarTupleTooManyArguments);
                    return None;
                }
                ArgumentKind::Keyword {
                    key,
                    node_ref,
                    expression,
                    ..
                } => match key {
                    "default" => {
                        if let Some(t) = node_ref
                            .file
                            .inference(i_s)
                            .compute_type_var_constraint(expression)
                        {
                            //default = Some(t);
                            todo!()
                        } else {
                            todo!()
                        }
                    }
                    _ => {
                        node_ref.add_issue(
                            i_s,
                            IssueType::UnexpectedArgument {
                                class_name: "TypeVarTuple",
                                argument_name: Box::from(key),
                            },
                        );
                        return None;
                    }
                },
                ArgumentKind::Comprehension { .. } => {
                    arg.as_node_ref()
                        .add_issue(i_s, IssueType::UnexpectedComprehension);
                    return None;
                }
                ArgumentKind::Inferred { .. }
                | ArgumentKind::SlicesTuple { .. }
                | ArgumentKind::Overridden { .. }
                | ArgumentKind::ParamSpec { .. } => unreachable!(),
            }
        }
        Some(TypeVarLike::TypeVarTuple(Rc::new(TypeVarTuple {
            name_string: PointLink {
                file: name_node.file_index(),
                node_index: py_string.index(),
            },
            default,
        })))
    } else {
        args.as_node_ref().add_issue(
            i_s,
            IssueType::TypeVarLikeTooFewArguments {
                class_name: "TypeVarTuple",
            },
        );
        None
    }
}

#[derive(Debug)]
pub struct ParamSpecClass();

impl ParamSpecClass {
    pub fn execute(
        &self,
        i_s: &InferenceState,
        args: &dyn Arguments,
        result_context: &mut ResultContext,
        on_type_error: OnTypeError,
    ) -> Inferred {
        if let Some(t) = maybe_param_spec(i_s, args, result_context) {
            Inferred::new_unsaved_complex(ComplexPoint::TypeVarLike(t))
        } else {
            Inferred::new_unknown()
        }
    }
}

fn maybe_param_spec(
    i_s: &InferenceState,
    args: &dyn Arguments,
    result_context: &ResultContext,
) -> Option<TypeVarLike> {
    if !matches!(result_context, ResultContext::AssignmentNewDefinition) {
        args.as_node_ref()
            .add_issue(i_s, IssueType::UnexpectedTypeForTypeVar);
        return None;
    }
    let mut iterator = args.iter();
    if let Some(first_arg) = iterator.next() {
        let result = if let ArgumentKind::Positional { node_ref, .. } = first_arg.kind {
            node_ref
                .as_named_expression()
                .maybe_single_string_literal()
                .map(|py_string| (node_ref, py_string))
        } else {
            debug!("TODO param spec why does this not need an error?");
            None
        };
        let (name_node, py_string) = match result {
            Some(result) => result,
            None => {
                first_arg.as_node_ref().add_issue(
                    i_s,
                    IssueType::TypeVarLikeFirstArgMustBeString {
                        class_name: "ParamSpec",
                    },
                );
                return None;
            }
        };
        if let Some(name) = py_string.in_simple_assignment() {
            if name.as_code() != py_string.content() {
                name_node.add_issue(
                    i_s,
                    IssueType::TypeVarNameMismatch {
                        class_name: "ParamSpec",
                        string_name: Box::from(py_string.content()),
                        variable_name: Box::from(name.as_code()),
                    },
                );
            }
        } else {
            todo!()
        }

        for arg in iterator {
            match arg.kind {
                ArgumentKind::Keyword {
                    key,
                    node_ref,
                    expression,
                    ..
                } if key == "default" => {
                    if let Some(t) = node_ref
                        .file
                        .inference(i_s)
                        .compute_type_var_constraint(expression)
                    {
                        todo!()
                    } else {
                        todo!()
                    }
                }
                ArgumentKind::Inferred { .. }
                | ArgumentKind::SlicesTuple { .. }
                | ArgumentKind::ParamSpec { .. } => unreachable!(),
                ArgumentKind::Positional { .. } => {
                    arg.as_node_ref().add_issue(
                        i_s,
                        IssueType::ArgumentIssue(
                            "Too many positional arguments for \"ParamSpec\"".into(),
                        ),
                    );
                    return None;
                }
                _ => {
                    arg.as_node_ref()
                        .add_issue(i_s, IssueType::ParamSpecTooManyKeywordArguments);
                    return None;
                }
            }
        }
        Some(TypeVarLike::ParamSpec(Rc::new(ParamSpec {
            name_string: PointLink {
                file: name_node.file_index(),
                node_index: py_string.index(),
            },
        })))
    } else {
        args.as_node_ref().add_issue(
            i_s,
            IssueType::TypeVarLikeTooFewArguments {
                class_name: "ParamSpec",
            },
        );
        None
    }
}

#[derive(Debug)]
pub struct NewTypeClass();

impl NewTypeClass {
    pub fn execute<'db>(
        &self,
        i_s: &InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
        result_context: &mut ResultContext,
        on_type_error: OnTypeError,
    ) -> Inferred {
        if let Some(n) = maybe_new_type(i_s, args) {
            Inferred::new_unsaved_complex(ComplexPoint::NewTypeDefinition(Rc::new(n)))
        } else {
            Inferred::new_unknown()
        }
    }
}

fn maybe_new_type<'db>(
    i_s: &InferenceState<'db, '_>,
    args: &dyn Arguments<'db>,
) -> Option<NewType> {
    let Some((first, second)) = args.maybe_two_positional_args(i_s.db) else {
        args.as_node_ref().add_issue(
            i_s,
            IssueType::ArgumentIssue(Box::from(
                    "NewType(...) expects exactly two positional arguments")),
        );
        return None
    };
    let result = first
        .as_named_expression()
        .maybe_single_string_literal()
        .map(|py_string| (first, py_string));
    let (name_node, py_string) = match result {
        Some(result) => result,
        None => {
            first.add_issue(
                i_s,
                IssueType::ArgumentIssue(Box::from(
                    "Argument 1 to NewType(...) must be a string literal",
                )),
            );
            return None;
        }
    };
    if let Some(name) = py_string.in_simple_assignment() {
        if name.as_code() != py_string.content() {
            name_node.add_issue(
                i_s,
                IssueType::TypeVarNameMismatch {
                    class_name: "NewType",
                    string_name: Box::from(py_string.content()),
                    variable_name: Box::from(name.as_code()),
                },
            );
        }
    } else {
        todo!()
    }
    let type_node_ref = NodeRef::new(
        second.file,
        second.as_named_expression().expression().index(),
    );
    Some(NewType::new(
        PointLink {
            file: name_node.file_index(),
            node_index: py_string.index(),
        },
        type_node_ref.as_link(),
    ))
}
