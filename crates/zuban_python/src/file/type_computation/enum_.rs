use std::sync::Arc;

use parsa_python_cst::{
    AtomContent, CodeIndex, DictElement, Expression, StarLikeExpression, StarLikeExpressionIterator,
};

use crate::{
    arguments::{ArgKind, Args},
    database::PointLink,
    diagnostics::IssueKind,
    file::name_resolution::NameResolution,
    inference_state::InferenceState,
    inferred::Inferred,
    node_ref::NodeRef,
    result_context::ResultContext,
    type_::{DbString, Enum, EnumMemberDefinition, Literal, LiteralKind, StringSlice, Type},
    type_helpers::Class,
};

impl<'db, 'file> NameResolution<'db, 'file, '_> {
    pub(crate) fn compute_functional_enum_definition(
        &self,
        class: Class,
        args: &dyn Args<'db>,
    ) -> Option<Inferred> {
        let mut name_infos = None;
        let mut fields_infos = None;
        for arg in args.iter(self.i_s.mode) {
            match arg.kind {
                ArgKind::Positional(positional) => {
                    let expr = positional.node_ref.expect_named_expression().expression();
                    if name_infos.is_none() {
                        name_infos = Some((
                            positional.node_ref,
                            positional.infer(&mut ResultContext::Unknown),
                            expr.in_simple_assignment(),
                        ));
                    } else if fields_infos.is_none() {
                        fields_infos = Some((positional.node_ref, expr));
                    } else {
                        args.add_issue(
                            self.i_s,
                            IssueKind::TooManyArguments(format!(" for {}()", class.name()).into()),
                        );
                        return None;
                    }
                }
                ArgKind::Keyword(kw) => match kw.key {
                    "value" => {
                        name_infos = Some((
                            kw.node_ref,
                            kw.infer(&mut ResultContext::Unknown),
                            kw.expression.in_simple_assignment(),
                        ))
                    }
                    "names" => fields_infos = Some((kw.node_ref, kw.expression)),
                    "module" | "qualname" | "type" | "start" | "boundary" => (), // TODO type check these
                    _ => {
                        kw.add_issue(
                            self.i_s,
                            IssueKind::ArgumentIssue(
                                format!(r#"Unexpected keyword argument "{}""#, kw.key).into(),
                            ),
                        );
                        return None;
                    }
                },
                _ => {
                    args.add_issue(
                        self.i_s,
                        IssueKind::EnumUnexpectedArguments {
                            name: class.name().into(),
                        },
                    );
                    return None;
                }
            }
        }
        let Some(name_infos) = name_infos else {
            args.add_issue(
                self.i_s,
                IssueKind::TooFewArguments(format!(" for {}()", class.name()).into()),
            );
            return None;
        };
        let Type::Literal(Literal {
            kind: LiteralKind::String(name),
            ..
        }) = name_infos.1.as_type(self.i_s)
        else {
            name_infos
                .0
                .add_issue(self.i_s, IssueKind::EnumFirstArgMustBeString);
            return None;
        };

        let Some(fields_infos) = fields_infos else {
            args.add_issue(
                self.i_s,
                IssueKind::TooFewArguments(format!(" for {}()", class.name()).into()),
            );
            return None;
        };

        if let Some(name_def) = name_infos.2 {
            let n = name.as_str(self.i_s.db);
            if name_def.as_code() != n {
                name_infos.0.add_issue(
                    self.i_s,
                    IssueKind::VarNameMismatch {
                        class_name: class.qualified_name(self.i_s.db).into(),
                        string_name: Box::from(n),
                        variable_name: Box::from(name_def.as_code()),
                    },
                );
            }
        }

        let members =
            gather_functional_enum_members(self.i_s, class, &name, fields_infos.0, fields_infos.1)?;
        if members.is_empty() {
            fields_infos.0.add_issue(
                self.i_s,
                IssueKind::EnumNeedsAtLeastOneItem {
                    name: class.name().into(),
                },
            );
            return None;
        }

        Some(Inferred::from_type(Type::Type(Arc::new(Type::Enum(
            Enum::new(
                name,
                class.node_ref.as_link(),
                name_infos.0.as_link(),
                self.i_s.as_parent_scope(),
                members,
                [].into(),
                class.has_customized_enum_new(self.i_s).into(),
            ),
        )))))
    }
}

#[derive(Default)]
struct EnumMembers(Vec<EnumMemberDefinition>);

impl EnumMembers {
    fn add_member(
        &mut self,
        i_s: &InferenceState,
        enum_name: &DbString,
        from: NodeRef,
        d: EnumMemberDefinition,
    ) {
        let member_name = d.name(i_s.db);
        if self.0.iter().any(|t| t.name(i_s.db) == member_name) {
            from.add_issue(
                i_s,
                IssueKind::EnumReusedMemberName {
                    enum_name: enum_name.as_str(i_s.db).into(),
                    member_name: member_name.into(),
                },
            );
        } else {
            self.0.push(d)
        }
    }

    fn into_boxed_slice(self) -> Box<[EnumMemberDefinition]> {
        self.0.into()
    }
}

fn gather_functional_enum_members(
    i_s: &InferenceState,
    class: Class,
    enum_name: &DbString,
    node_ref: NodeRef,
    expression: Expression,
) -> Option<Box<[EnumMemberDefinition]>> {
    let mut members = EnumMembers::default();

    let expects_string_pairs = || {
        NodeRef::new(node_ref.file, expression.index()).add_issue(
            i_s,
            IssueKind::EnumWithTupleOrListExpectsStringPairs {
                name: class.name().into(),
            },
        )
    };

    let get_tuple_like = |mut iterator: StarLikeExpressionIterator| -> Option<StringSlice> {
        let first = iterator.next()?;
        let second = iterator.next()?;
        if iterator.next().is_some() {
            return None;
        }
        let StarLikeExpression::NamedExpression(n) = first else {
            return None;
        };
        if !matches!(second, StarLikeExpression::NamedExpression(_)) {
            return None;
        };
        StringSlice::from_string_in_expression(node_ref.file.file_index, n.expression())
    };

    let mut add_from_iterator = |iterator| -> Option<()> {
        for element in iterator {
            let StarLikeExpression::NamedExpression(ne) = element else {
                return None;
            };
            let expression = ne.expression();
            let name = match expression.maybe_unpacked_atom() {
                // Enums can be defined like Enum("Foo", [('CYAN', 4), ('MAGENTA', 5)])
                Some(AtomContent::List(list)) => get_tuple_like(list.unpack())?,
                Some(AtomContent::Tuple(tup)) => get_tuple_like(tup.iter())?,
                _ => StringSlice::from_string_in_expression(node_ref.file.file_index, expression)?,
            };
            members.add_member(
                i_s,
                enum_name,
                NodeRef::new(node_ref.file, expression.index()),
                EnumMemberDefinition::new(name.into(), None),
            )
        }
        Some(())
    };

    let mut add_from_iterator_with_error = |iterator| -> Option<()> {
        if add_from_iterator(iterator).is_none() {
            expects_string_pairs();
            None
        } else {
            Some(())
        }
    };

    match expression.maybe_unpacked_atom() {
        Some(AtomContent::List(list)) => {
            add_from_iterator_with_error(list.unpack())?;
        }
        Some(AtomContent::Tuple(tup)) => {
            add_from_iterator_with_error(tup.iter())?;
        }
        Some(AtomContent::Strings(s)) => {
            match DbString::from_python_string(node_ref.file_index(), s.as_python_string()) {
                Some(s) => split_enum_members(
                    i_s,
                    enum_name,
                    NodeRef::new(node_ref.file, expression.index()),
                    &mut members,
                    &s,
                ),
                _ => {
                    node_ref.add_issue(
                        i_s,
                        IssueKind::EnumInvalidSecondArgument {
                            enum_name: class.name().into(),
                        },
                    );
                    return None;
                }
            }
        }
        Some(AtomContent::Dict(d)) => {
            for element in d.iter_elements() {
                let DictElement::KeyValue(kv) = element else {
                    node_ref.add_issue(
                        i_s,
                        IssueKind::EnumWithDictRequiresStringLiterals {
                            name: class.name().into(),
                        },
                    );
                    return None;
                };
                let key = kv.key();
                let Some(name) =
                    StringSlice::from_string_in_expression(node_ref.file.file_index, key)
                else {
                    node_ref.add_issue(
                        i_s,
                        IssueKind::EnumWithDictRequiresStringLiterals {
                            name: class.name().into(),
                        },
                    );
                    return None;
                };
                members.add_member(
                    i_s,
                    enum_name,
                    NodeRef::new(node_ref.file, key.index()),
                    EnumMemberDefinition::new(
                        name.into(),
                        Some(PointLink::new(node_ref.file.file_index, kv.value().index())),
                    ),
                );
            }
        }
        _ => {
            let inf = node_ref.file.inference(i_s).infer_expression(expression);
            if let Type::Literal(literal) = inf.as_cow_type(i_s).as_ref()
                && let LiteralKind::String(s) = &literal.kind
            {
                split_enum_members(
                    i_s,
                    enum_name,
                    NodeRef::new(node_ref.file, expression.index()),
                    &mut members,
                    s,
                );
                return Some(members.into_boxed_slice());
            }
            node_ref.add_issue(
                i_s,
                IssueKind::EnumInvalidSecondArgument {
                    enum_name: class.name().into(),
                },
            );
            return None;
        }
    };
    Some(members.into_boxed_slice())
}

fn split_enum_members(
    i_s: &InferenceState,
    enum_name: &DbString,
    from: NodeRef,
    members: &mut EnumMembers,
    s: &DbString,
) {
    let mut start = 0;
    for part in s.as_str(i_s.db).split(&[',', ' ']) {
        if part.is_empty() {
            start += 1;
            continue;
        }
        let name = match s {
            DbString::StringSlice(slice) => {
                let start = slice.start + start;
                StringSlice::new(slice.file_index, start, start + part.len() as CodeIndex).into()
            }
            _ => DbString::ArcStr(part.into()),
        };
        members.add_member(i_s, enum_name, from, EnumMemberDefinition::new(name, None));
        start += part.len() as CodeIndex + 1;
    }
}
