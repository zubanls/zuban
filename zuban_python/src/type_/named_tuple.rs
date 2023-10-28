use std::{cell::OnceCell, rc::Rc};

use parsa_python_ast::{AtomContent, CodeIndex, StarLikeExpression};

use crate::{
    arguments::{ArgumentIterator, ArgumentKind, Arguments},
    database::{ComplexPoint, Database},
    debug,
    diagnostics::IssueType,
    file::{File, TypeComputation, TypeComputationOrigin, TypeVarCallbackReturn},
    getitem::SliceType,
    inference_state::InferenceState,
    inferred::Inferred,
    matching::{FormatData, Generics, IteratorContent, LookupResult, OnTypeError, ResultContext},
    node_ref::NodeRef,
    type_helpers::{start_namedtuple_params, Module, Tuple},
    utils::join_with_commas,
};

use super::{
    CallableContent, CallableParam, CallableParams, FormatStyle, FunctionKind, ParamSpecific,
    RecursiveAlias, StringSlice, TupleContent, Type, TypeOrTypeVarTuple,
};

#[derive(Debug, PartialEq, Clone)]
pub struct NamedTuple {
    pub name: StringSlice,
    pub __new__: Rc<CallableContent>,
    tuple: OnceCell<Rc<TupleContent>>,
}

impl NamedTuple {
    pub fn new(name: StringSlice, __new__: CallableContent) -> Self {
        Self {
            name,
            __new__: Rc::new(__new__),
            tuple: OnceCell::new(),
        }
    }

    pub fn clone_with_new_init_class(&self, name: StringSlice) -> Rc<NamedTuple> {
        let mut nt = self.clone();
        let mut callable = nt.__new__.as_ref().clone();
        callable.name = Some(name);
        nt.__new__ = Rc::new(callable);
        Rc::new(nt)
    }

    pub fn params(&self) -> &[CallableParam] {
        // Namedtuple callables contain a first param `Type[Self]` that we should skip.
        &self.__new__.expect_simple_params()[1..]
    }

    pub fn search_param(&self, db: &Database, search_name: &str) -> Option<&CallableParam> {
        self.params()
            .iter()
            .find(|p| p.name.unwrap().as_str(db) == search_name)
    }

    pub fn name<'a>(&self, db: &'a Database) -> &'a str {
        self.name.as_str(db)
    }

    pub fn qualified_name(&self, db: &Database) -> String {
        let module = Module::from_file_index(db, self.name.file_index).qualified_name(db);
        format!("{module}.{}", self.name(db))
    }

    pub fn as_tuple(&self) -> Rc<TupleContent> {
        self.tuple
            .get_or_init(|| {
                Rc::new(TupleContent::new_fixed_length(
                    self.params()
                        .iter()
                        .map(|t| {
                            TypeOrTypeVarTuple::Type(
                                t.param_specific.expect_positional_type_as_ref().clone(),
                            )
                        })
                        .collect(),
                ))
            })
            .clone()
    }

    pub fn as_tuple_ref(&self) -> &TupleContent {
        self.as_tuple();
        self.tuple.get().unwrap()
    }

    pub fn format_with_name(
        &self,
        format_data: &FormatData,
        name: &str,
        generics: Generics,
    ) -> Box<str> {
        if format_data.style != FormatStyle::MypyRevealType {
            return Box::from(name);
        }
        let params = self.params();
        // We need to check recursions here, because for class definitions of named tuples can
        // recurse with their attributes.
        let rec = RecursiveAlias::new(self.__new__.defined_at, None);
        if format_data.has_already_seen_recursive_alias(&rec) {
            return Box::from(name);
        }
        let format_data = &format_data.with_seen_recursive_alias(&rec);
        let types = match params.is_empty() {
            true => "()".into(),
            false => join_with_commas(params.iter().map(|p| {
                let t = p.param_specific.expect_positional_type_as_ref();
                match generics {
                    Generics::NotDefinedYet | Generics::None => t.format(format_data),
                    _ => t
                        .replace_type_var_likes_and_self(
                            format_data.db,
                            &mut |usage| {
                                generics
                                    .nth_usage(format_data.db, &usage)
                                    .into_generic_item(format_data.db)
                            },
                            &|| todo!(),
                        )
                        .format(format_data),
                }
                .into()
            })),
        };
        format!("tuple[{types}, fallback={name}]",).into()
    }

    pub fn iter(&self, i_s: &InferenceState, from: NodeRef) -> IteratorContent {
        Tuple::new(&self.as_tuple()).iter(i_s, from)
    }

    pub fn get_item(
        &self,
        i_s: &InferenceState,
        slice_type: &SliceType,
        result_context: &mut ResultContext,
    ) -> Inferred {
        Tuple::new(&self.as_tuple()).get_item(i_s, slice_type, result_context)
    }

    pub fn lookup(&self, i_s: &InferenceState, name: &str) -> LookupResult {
        for p in self.params() {
            if name == p.name.unwrap().as_str(i_s.db) {
                return LookupResult::UnknownName(Inferred::from_type(
                    p.param_specific.expect_positional_type_as_ref().clone(),
                ));
            }
        }
        if name == "__new__" {
            return LookupResult::UnknownName(Inferred::from_type(Type::Callable(
                self.__new__.clone(),
            )));
        }
        debug!("TODO lookup of NamedTuple base classes");
        LookupResult::None
    }
}

pub fn execute_typing_named_tuple(i_s: &InferenceState, args: &dyn Arguments) -> Inferred {
    match new_typing_named_tuple(i_s, args, false) {
        Some(rc) => Inferred::new_unsaved_complex(ComplexPoint::NamedTupleDefinition(Rc::new(
            Type::NamedTuple(rc),
        ))),
        None => Inferred::new_any(),
    }
}

pub fn execute_collections_named_tuple<'db>(
    i_s: &InferenceState<'db, '_>,
    args: &dyn Arguments<'db>,
    result_context: &mut ResultContext,
    on_type_error: OnTypeError<'db, '_>,
) -> Inferred {
    i_s.db
        .python_state
        .collections_namedtuple_function()
        .execute(i_s, args, result_context, on_type_error);
    match new_collections_named_tuple(i_s, args) {
        Some(rc) => Inferred::new_unsaved_complex(ComplexPoint::NamedTupleDefinition(Rc::new(
            Type::NamedTuple(rc),
        ))),
        None => Inferred::new_any(),
    }
}

fn check_named_tuple_name<'x, 'y>(
    i_s: &InferenceState,
    executable_name: &'static str,
    args: &'y dyn Arguments<'x>,
) -> Option<(
    StringSlice,
    NodeRef<'y>,
    AtomContent<'y>,
    ArgumentIterator<'x, 'y>,
)> {
    let mut iterator = args.iter();
    let Some(first_arg) = iterator.next() else {
        todo!()
    };
    let ArgumentKind::Positional { node_ref, .. } = first_arg.kind else {
        first_arg.as_node_ref().add_issue(i_s, IssueType::UnexpectedArgumentsTo { name: "namedtuple" });
        return None
    };
    let expr = node_ref.as_named_expression().expression();
    let first = expr
        .maybe_single_string_literal()
        .map(|py_string| (node_ref, py_string));
    let Some(mut string_slice) = StringSlice::from_string_in_expression(node_ref.file_index(), expr) else {
        node_ref.add_issue(i_s, IssueType::NamedTupleExpectsStringLiteralAsFirstArg { name: executable_name });
        return None
    };
    let py_string = expr.maybe_single_string_literal()?;
    if let Some(name) = py_string.in_simple_assignment() {
        let should = name.as_code();
        let is = py_string.content();
        if should != is {
            node_ref.add_issue(
                i_s,
                IssueType::NamedTupleFirstArgumentMismatch {
                    should: should.into(),
                    is: is.into(),
                },
            );
            string_slice = StringSlice::from_name(node_ref.file_index(), name.name());
        }
    }
    let Some(second_arg) = iterator.next() else {
        if executable_name != "namedtuple" {
            // For namedtuple this is already handled by type checking.
            args.as_node_ref().add_issue(i_s, IssueType::TooFewArguments(r#" for "NamedTuple()""#.into()));
        }
        return None
    };
    let ArgumentKind::Positional { node_ref, .. } = second_arg.kind else {
        todo!()
    };
    let Some(atom_content) = node_ref.as_named_expression().expression().maybe_unpacked_atom() else {
        todo!()
    };
    Some((string_slice, node_ref, atom_content, iterator))
}

pub fn new_typing_named_tuple(
    i_s: &InferenceState,
    args: &dyn Arguments,
    in_type_definition: bool,
) -> Option<Rc<NamedTuple>> {
    let Some((name, second_node_ref, atom_content, mut iterator)) = check_named_tuple_name(i_s, "NamedTuple", args) else {
        return None
    };
    if iterator.next().is_some() {
        args.as_node_ref().add_issue(
            i_s,
            IssueType::TooManyArguments(" for \"NamedTuple()\"".into()),
        );
        return None;
    }
    let list_iterator = match atom_content {
        AtomContent::List(list) => list.unpack(),
        AtomContent::Tuple(tup) => tup.iter(),
        _ => {
            second_node_ref.add_issue(
                i_s,
                IssueType::InvalidSecondArgumentToNamedTuple { name: "NamedTuple" },
            );
            return None;
        }
    };
    let args_node_ref = args.as_node_ref();
    let on_type_var = &mut |i_s: &InferenceState, _: &_, _, _| TypeVarCallbackReturn::NotFound;
    let mut inference = args_node_ref.file.inference(i_s);
    let mut comp = TypeComputation::new(
        &mut inference,
        args.as_node_ref().as_link(),
        on_type_var,
        TypeComputationOrigin::Constraint,
    );
    if let Some(params) = comp.compute_named_tuple_initializer(args_node_ref, list_iterator) {
        check_named_tuple_has_no_fields_with_underscore(i_s, "NamedTuple", args, &params);
        let type_var_likes = comp.into_type_vars(|_, _| ());
        if in_type_definition && !type_var_likes.is_empty() {
            args.as_node_ref()
                .add_issue(i_s, IssueType::NamedTupleGenericInClassDefinition);
            return None;
        }
        let callable = CallableContent {
            name: Some(name),
            class_name: None,
            defined_at: args_node_ref.as_link(),
            kind: FunctionKind::Function {
                had_first_self_or_class_annotation: true,
            },
            type_vars: type_var_likes,
            params: CallableParams::Simple(Rc::from(params)),
            result_type: Type::Self_,
        };
        Some(Rc::new(NamedTuple::new(name, callable)))
    } else {
        None
    }
}

pub fn new_collections_named_tuple(
    i_s: &InferenceState,
    args: &dyn Arguments,
) -> Option<Rc<NamedTuple>> {
    let Some((name, second_node_ref, atom_content, _)) = check_named_tuple_name(i_s, "namedtuple", args) else {
        return None
    };
    let args_node_ref = args.as_node_ref();
    let mut params = start_namedtuple_params(i_s.db);

    let mut add_param = |name| {
        params.push(CallableParam {
            param_specific: ParamSpecific::PositionalOrKeyword(Type::Any),
            name: Some(name),
            has_default: false,
        })
    };

    let mut add_from_iterator = |iterator| {
        for element in iterator {
            let StarLikeExpression::NamedExpression(ne) = element else {
            todo!()
        };
            let Some(string_slice) = StringSlice::from_string_in_expression(args_node_ref.file.file_index(), ne.expression()) else {
                NodeRef::new(second_node_ref.file, ne.index())
                    .add_issue(i_s, IssueType::StringLiteralExpectedAsNamedTupleItem);
                continue
            };
            add_param(string_slice)
        }
    };
    match atom_content {
        AtomContent::List(list) => add_from_iterator(list.unpack()),
        AtomContent::Tuple(tup) => add_from_iterator(tup.iter()),
        AtomContent::Strings(s) => match s.maybe_single_string_literal() {
            Some(s) => {
                let (mut start, _) = s.content_start_and_end_in_literal();
                start += s.start();
                for part in s.content().split(&[',', ' ']) {
                    add_param(StringSlice::new(
                        args_node_ref.file_index(),
                        start,
                        start + part.len() as CodeIndex,
                    ));
                    start += part.len() as CodeIndex + 1;
                }
            }
            _ => todo!(),
        },
        _ => {
            second_node_ref.add_issue(
                i_s,
                IssueType::InvalidSecondArgumentToNamedTuple { name: "namedtuple" },
            );
            return None;
        }
    };
    check_named_tuple_has_no_fields_with_underscore(i_s, "namedtuple", args, &params);

    for arg in args.iter() {
        if let ArgumentKind::Keyword {
            key: "defaults",
            expression,
            ..
        } = arg.kind
        {
            let defaults_iterator = match expression.maybe_unpacked_atom() {
                Some(AtomContent::List(list)) => list.unpack(),
                Some(AtomContent::Tuple(tuple)) => tuple.iter(),
                _ => {
                    arg.as_node_ref()
                        .add_issue(i_s, IssueType::NamedTupleDefaultsShouldBeListOrTuple);
                    return None;
                }
            };
            let member_count = params.len() - 1;
            let defaults_count = defaults_iterator.count();
            let skip = if defaults_count > member_count {
                arg.as_node_ref()
                    .add_issue(i_s, IssueType::NamedTupleToManyDefaults);
                0
            } else {
                member_count - defaults_count
            };
            for param in params.iter_mut().skip(skip + 1) {
                param.has_default = true;
            }
            break;
        }
    }

    let callable = CallableContent {
        name: Some(name),
        class_name: None,
        defined_at: args_node_ref.as_link(),
        kind: FunctionKind::Function {
            had_first_self_or_class_annotation: true,
        },
        type_vars: i_s.db.python_state.empty_type_var_likes.clone(),
        params: CallableParams::Simple(Rc::from(params)),
        result_type: Type::Self_,
    };
    Some(Rc::new(NamedTuple::new(name, callable)))
}

fn check_named_tuple_has_no_fields_with_underscore(
    i_s: &InferenceState,
    name: &'static str,
    args: &dyn Arguments,
    params: &[CallableParam],
) {
    let field_names_with_underscore: Vec<_> = params
        .iter()
        .filter_map(|p| {
            p.name.and_then(|name| {
                let name_str = name.as_str(i_s.db);
                name_str.starts_with('_').then_some(name_str)
            })
        })
        .collect();
    if !field_names_with_underscore.is_empty() {
        args.as_node_ref().add_issue(
            i_s,
            IssueType::NamedTupleNamesCannotStartWithUnderscore {
                name,
                field_names: field_names_with_underscore.join(", ").into(),
            },
        );
    }
}
