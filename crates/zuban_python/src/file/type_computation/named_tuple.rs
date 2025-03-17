use std::rc::Rc;

use parsa_python_cst::{
    keywords_contain, Assignment, AtomContent, CodeIndex, StarLikeExpression,
    StarLikeExpressionIterator,
};

use crate::{
    arguments::{ArgIterator, ArgKind, Args, KeywordArg},
    database::{ComplexPoint, Database},
    diagnostics::IssueKind,
    file::name_resolution::NameResolution,
    getitem::SliceType,
    inference_state::InferenceState,
    inferred::Inferred,
    matching::ResultContext,
    node_ref::NodeRef,
    type_::{
        AnyCause, CallableContent, CallableParam, CallableParams, DbString, NamedTuple, ParamType,
        StringSlice, Type,
    },
};

use super::{TypeComputation, TypeComputationOrigin, TypeContent, TypeVarCallbackReturn};

impl<'db, 'file> NameResolution<'db, 'file, '_> {
    pub(crate) fn compute_collections_named_tuple(
        &self,
        assignment: Assignment,
        args: &dyn Args<'db>,
    ) -> Inferred {
        match new_collections_named_tuple(self.i_s, args) {
            Some(rc) => Inferred::new_unsaved_complex(ComplexPoint::NamedTupleDefinition(Rc::new(
                Type::NamedTuple(rc),
            ))),
            None => Inferred::new_invalid_type_definition(),
        }
    }
}

impl<'db: 'x + 'file, 'file, 'i_s, 'c, 'x> TypeComputation<'db, 'file, 'i_s, 'c> {
    pub fn compute_named_tuple_initializer(
        &mut self,
        list: StarLikeExpressionIterator,
    ) -> Option<Vec<CallableParam>> {
        // From NamedTuple('x', [('a', int)]) to a callable that matches those params

        let file_index = self.file.file_index;
        let mut params = start_namedtuple_params(self.i_s.db);
        for element in list {
            let StarLikeExpression::NamedExpression(ne) = element else {
                self.name_resolution
                    .add_issue(element.index(), IssueKind::TupleExpectedAsNamedTupleField);
                return None;
            };
            let mut parts = match ne.expression().maybe_unpacked_atom() {
                Some(AtomContent::Tuple(tup)) => tup.iter(),
                _ => {
                    self.name_resolution
                        .add_issue(ne.index(), IssueKind::TupleExpectedAsNamedTupleField);
                    return None;
                }
            };
            let Some(first) = parts.next() else {
                self.name_resolution.add_issue(
                    ne.index(),
                    IssueKind::NamedTupleFieldExpectsTupleOfStrAndType,
                );
                return None;
            };
            let Some(second) = parts.next() else {
                self.name_resolution.add_issue(
                    ne.index(),
                    IssueKind::NamedTupleFieldExpectsTupleOfStrAndType,
                );
                return None;
            };
            let StarLikeExpression::NamedExpression(name_expr) = first else {
                self.name_resolution
                    .add_issue(ne.index(), IssueKind::NamedTupleInvalidFieldName);
                return None;
            };
            let StarLikeExpression::NamedExpression(type_expr) = second else {
                self.name_resolution.add_issue(
                    name_expr.index(),
                    IssueKind::InvalidType("Star args are not supported".into()),
                );
                return None;
            };
            let Some(name) =
                StringSlice::from_string_in_expression(file_index, name_expr.expression())
            else {
                self.name_resolution
                    .add_issue(name_expr.index(), IssueKind::NamedTupleInvalidFieldName);
                return None;
            };
            let t = self.compute_named_expr_type(type_expr);
            add_named_tuple_param(
                "NamedTuple",
                self.i_s.db,
                &mut params,
                name,
                t,
                false,
                |issue| self.name_resolution.add_issue(ne.index(), issue),
            )
        }
        Some(params)
    }

    pub(super) fn compute_type_get_item_on_named_tuple(
        &mut self,
        named_tuple: Rc<NamedTuple>,
        slice_type: SliceType,
    ) -> TypeContent<'db, 'db> {
        let db = self.i_s.db;
        let mut generics = vec![];
        self.calculate_type_arguments(
            slice_type,
            &mut generics,
            slice_type.iter(),
            &named_tuple.__new__.type_vars,
            &|| named_tuple.name(db).into(),
            |slf: &mut Self, counts| {
                slf.add_issue(
                    slice_type.as_node_ref(),
                    IssueKind::TypeArgumentIssue {
                        class: named_tuple.name.as_str(db).into(),
                        counts,
                    },
                );
            },
        );
        let defined_at = named_tuple.__new__.defined_at;
        let nt = Type::NamedTuple(named_tuple);
        TypeContent::Type(
            nt.replace_type_var_likes(db, &mut |usage| {
                (usage.in_definition() == defined_at)
                    .then(|| generics[usage.index().as_usize()].clone())
            })
            .unwrap_or(nt),
        )
    }
}

fn check_named_tuple_name<'x, 'y>(
    i_s: &InferenceState<'_, 'y>,
    executable_name: &'static str,
    args: &'y dyn Args<'x>,
) -> Option<(
    StringSlice,
    NodeRef<'y>,
    AtomContent<'y>,
    ArgIterator<'x, 'y>,
)> {
    let too_few_args = || {
        // For namedtuple this is already handled by type checking.
        args.add_issue(
            i_s,
            IssueKind::TooFewArguments(format!(r#" for "{executable_name}()""#).into()),
        );
        None
    };
    let mut iterator = args.iter(i_s.mode);
    let Some(first_arg) = iterator.next() else {
        return too_few_args();
    };
    let ArgKind::Positional(pos) = first_arg.kind else {
        first_arg.add_issue(
            i_s,
            IssueKind::UnexpectedArgumentsTo {
                name: executable_name,
            },
        );
        return None;
    };
    let expr = pos.node_ref.as_named_expression().expression();
    let Some(mut string_slice) =
        StringSlice::from_string_in_expression(pos.node_ref.file_index(), expr)
    else {
        pos.node_ref.add_issue(
            i_s,
            IssueKind::NamedTupleExpectsStringLiteralAsFirstArg {
                name: executable_name,
            },
        );
        return None;
    };
    let py_string = expr.maybe_single_string_literal()?;
    if let Some(name) = py_string.in_simple_assignment() {
        let should = name.as_code();
        let is = py_string.content();
        if should != is {
            pos.node_ref.add_issue(
                i_s,
                IssueKind::NamedTupleFirstArgumentMismatch {
                    should: should.into(),
                    is: is.into(),
                },
            );
            string_slice = StringSlice::from_name(pos.node_ref.file_index(), name.name());
        }
    }
    let Some(second_arg) = iterator.next() else {
        return too_few_args();
    };
    let ArgKind::Positional(second) = second_arg.kind else {
        second_arg.add_issue(
            i_s,
            IssueKind::InvalidSecondArgumentToNamedTuple {
                name: executable_name,
            },
        );
        return None;
    };
    let Some(atom_content) = second
        .node_ref
        .as_named_expression()
        .expression()
        .maybe_unpacked_atom()
    else {
        second.node_ref.add_issue(
            i_s,
            IssueKind::InvalidSecondArgumentToNamedTuple {
                name: executable_name,
            },
        );
        return None;
    };
    Some((string_slice, second.node_ref, atom_content, iterator))
}

pub(crate) fn new_typing_named_tuple(
    i_s: &InferenceState,
    args: &dyn Args,
    in_type_definition: bool,
) -> Option<Rc<NamedTuple>> {
    let (_, second_node_ref, _, _) = check_named_tuple_name(i_s, "NamedTuple", args)?;
    let on_type_var = &mut |i_s: &InferenceState, _: &_, type_var_like, _| {
        i_s.find_parent_type_var(&type_var_like)
            .unwrap_or(TypeVarCallbackReturn::NotFound {
                allow_late_bound_callables: false,
            })
    };
    let mut comp = TypeComputation::new(
        i_s,
        second_node_ref.file,
        second_node_ref.as_link(),
        on_type_var,
        TypeComputationOrigin::NamedTupleMember,
    );
    let (name, params) = new_typing_named_tuple_internal(i_s, &mut comp, args)?;
    let type_var_likes = comp.into_type_vars(|_, _| ());
    if in_type_definition && !type_var_likes.is_empty() {
        args.add_issue(i_s, IssueKind::NamedTupleGenericInClassDefinition);
        return None;
    }
    Some(NamedTuple::from_params(
        second_node_ref.as_link(),
        name,
        type_var_likes,
        params,
    ))
}

pub(crate) fn new_typing_named_tuple_internal(
    i_s: &InferenceState,
    comp: &mut TypeComputation,
    args: &dyn Args,
) -> Option<(StringSlice, Vec<CallableParam>)> {
    let (name, second_node_ref, atom_content, mut iterator) =
        check_named_tuple_name(i_s, "NamedTuple", args)?;
    if iterator.next().is_some() {
        args.add_issue(
            i_s,
            IssueKind::TooManyArguments(" for \"NamedTuple()\"".into()),
        );
        return None;
    }
    let list_iterator = match atom_content {
        AtomContent::List(list) => list.unpack(),
        AtomContent::Tuple(tup) => tup.iter(),
        _ => {
            second_node_ref.add_issue(
                i_s,
                IssueKind::InvalidSecondArgumentToNamedTuple { name: "NamedTuple" },
            );
            return None;
        }
    };
    let params = comp.compute_named_tuple_initializer(list_iterator)?;
    check_named_tuple_has_no_fields_with_underscore(i_s, "NamedTuple", args, &params);
    Some((name, params))
}

pub(crate) fn new_collections_named_tuple<'db>(
    i_s: &InferenceState<'db, '_>,
    args: &dyn Args<'db>,
) -> Option<Rc<NamedTuple>> {
    let rename = args.iter(i_s.mode).any(|arg| {
        matches!(arg.keyword_name(i_s.db), Some("rename"))
            && arg.infer(&mut ResultContext::Unknown).is_true_literal(i_s)
    });
    let (name, second_node_ref, atom_content, _) = check_named_tuple_name(i_s, "namedtuple", args)?;
    let mut params = start_namedtuple_params(i_s.db);

    let mut add_param = |name| {
        add_named_tuple_param(
            "namedtuple",
            i_s.db,
            &mut params,
            name,
            Type::Any(AnyCause::Todo),
            rename,
            |issue| args.add_issue(i_s, issue),
        )
    };

    let mut add_from_iterator = |iterator| {
        for element in iterator {
            let StarLikeExpression::NamedExpression(ne) = element else {
                NodeRef::new(second_node_ref.file, element.index())
                    .add_issue(i_s, IssueKind::StringLiteralExpectedAsNamedTupleItem);
                continue;
            };
            let Some(string_slice) = StringSlice::from_string_in_expression(
                second_node_ref.file.file_index,
                ne.expression(),
            ) else {
                NodeRef::new(second_node_ref.file, ne.index())
                    .add_issue(i_s, IssueKind::StringLiteralExpectedAsNamedTupleItem);
                continue;
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
                    if !part.is_empty() {
                        add_param(StringSlice::new(
                            second_node_ref.file_index(),
                            start,
                            start + part.len() as CodeIndex,
                        ));
                    }
                    start += part.len() as CodeIndex + 1;
                }
            }
            _ => {
                second_node_ref.add_issue(
                    i_s,
                    IssueKind::InvalidSecondArgumentToNamedTuple { name: "namedtuple" },
                );
            }
        },
        _ => {
            second_node_ref.add_issue(
                i_s,
                IssueKind::InvalidSecondArgumentToNamedTuple { name: "namedtuple" },
            );
            return None;
        }
    };
    check_named_tuple_has_no_fields_with_underscore(i_s, "namedtuple", args, &params);

    for arg in args.iter(i_s.mode) {
        match &arg.kind {
            ArgKind::Keyword(KeywordArg {
                key: "defaults",
                expression,
                ..
            }) => {
                let defaults_iterator = match expression.maybe_unpacked_atom() {
                    Some(AtomContent::List(list)) => list.unpack(),
                    Some(AtomContent::Tuple(tuple)) => tuple.iter(),
                    _ => {
                        arg.add_issue(i_s, IssueKind::NamedTupleDefaultsShouldBeListOrTuple);
                        return None;
                    }
                };
                let member_count = params.len() - 1;
                let defaults_count = defaults_iterator.count();
                let skip = if defaults_count > member_count {
                    arg.add_issue(i_s, IssueKind::NamedTupleToManyDefaults);
                    0
                } else {
                    member_count - defaults_count
                };
                for param in params.iter_mut().skip(skip + 1) {
                    param.has_default = true;
                }
                break;
            }
            ArgKind::Keyword(kw) if kw.key != "rename" => {
                arg.add_issue(
                    i_s,
                    IssueKind::NamedTupleUnexpectedKeywordArgument {
                        keyword_name: kw.key.into(),
                    },
                );
            }
            _ => (), //todo!(),
        }
    }

    let callable = CallableContent::new_simple(
        Some(DbString::StringSlice(name)),
        None,
        second_node_ref.as_link(),
        i_s.db.python_state.empty_type_var_likes.clone(),
        CallableParams::new_simple(Rc::from(params)),
        Type::Self_,
    );
    Some(Rc::new(NamedTuple::new(name, callable)))
}

fn check_named_tuple_has_no_fields_with_underscore(
    _i_s: &InferenceState,
    _name: &'static str,
    _args: &dyn Args,
    params: &[CallableParam],
) {
    for param in params.iter() {
        if let Some(_param_name) = param.name.as_ref() {
            // TODO implement
        }
    }
}

fn is_identifier(s: &str) -> bool {
    let mut chars = s.chars();
    if !chars.next().is_some_and(|c| c.is_alphabetic() || c == '_') {
        return false;
    }
    chars.all(|c| c.is_alphanumeric() || c == '_')
}

pub fn add_named_tuple_param(
    named_tuple: &'static str,
    db: &Database,
    params: &mut Vec<CallableParam>,
    field_name: StringSlice,
    t: Type,
    rename: bool,
    add_issue: impl Fn(IssueKind),
) {
    let name_str = field_name.as_str(db);
    let mut field_name = field_name.into();
    let mut add_and_change = |issue| {
        field_name = DbString::RcStr(Rc::from(format!("_{}", params.len() - 1)));
        if !rename {
            add_issue(issue)
        }
    };
    if params.iter().any(|param| {
        param
            .name
            .as_ref()
            .is_some_and(|name| name.as_str(db) == name_str)
    }) {
        add_and_change(IssueKind::FunctionalNamedTupleDuplicateField {
            name: named_tuple,
            field_name: name_str.into(),
        })
    } else if !is_identifier(name_str) {
        add_and_change(IssueKind::FunctionalNamedTupleInvalidFieldName {
            name: named_tuple,
            field_name: name_str.into(),
        });
    } else if name_str.starts_with('_') {
        add_and_change(
            IssueKind::FunctionalNamedTupleNameCannotStartWithUnderscore {
                name: named_tuple,
                field_name: name_str.into(),
            },
        );
    } else if keywords_contain(name_str) {
        add_and_change(IssueKind::FunctionalNamedTupleNameUsedAKeyword {
            name: named_tuple,
            field_name: name_str.into(),
        });
    }
    params.push(CallableParam::new(
        field_name,
        ParamType::PositionalOrKeyword(t),
    ));
}

pub(super) fn start_namedtuple_params(db: &Database) -> Vec<CallableParam> {
    vec![CallableParam::new_anonymous(ParamType::PositionalOnly(
        db.python_state.type_of_self.clone(),
    ))]
}
