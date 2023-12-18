use std::rc::Rc;

use parsa_python_ast::{
    Dict, DictElement, DictElementIterator, Expression, Int, List, StarLikeExpression,
    StarLikeExpressionIterator,
};

use crate::{
    arguments::{unpack_star_star, Argument, Arguments},
    database::Database,
    debug,
    diagnostics::IssueType,
    file::{Inference, PythonFile},
    getitem::Simple,
    inference_state::InferenceState,
    inferred::UnionValue,
    matching::{ErrorTypes, FormatData, Matcher, MismatchReason, ResultContext},
    new_class,
    node_ref::NodeRef,
    type_::{
        check_typed_dict_call, infer_typed_dict_item, maybe_add_extra_keys_issue, AnyCause,
        Literal, LiteralKind, LiteralValue, Type, TypedDict, TypedDictGenerics,
    },
    Inferred,
};

impl<'db> Inference<'db, '_, '_> {
    pub fn create_list_or_set_generics<'x>(
        &mut self,
        elements: impl Iterator<Item = StarLikeExpression<'x>>,
    ) -> Type {
        let mut result: Option<Type> = None;
        for child in elements {
            let from_stars = |inferred: Inferred, from_index| {
                inferred
                    .iter(self.i_s, NodeRef::new(self.file, from_index))
                    .infer_all(self.i_s)
                    .as_type(self.i_s)
            };
            let t = match child {
                StarLikeExpression::NamedExpression(named_expr) => {
                    self.infer_named_expression(named_expr).as_type(self.i_s)
                }
                StarLikeExpression::StarNamedExpression(e) => {
                    from_stars(self.infer_expression_part(e.expression_part()), e.index())
                }
                StarLikeExpression::Expression(expr) => {
                    self.infer_expression(expr).as_type(self.i_s)
                }
                StarLikeExpression::StarExpression(star_expr) => from_stars(
                    self.infer_expression_part(star_expr.expression_part()),
                    star_expr.index(),
                ),
            };
            let t = t.avoid_implicit_literal(self.i_s.db);
            if let Some(r) = result.take() {
                result = Some(r.common_base_type(self.i_s, &t));
            } else {
                result = Some(t)
            }
        }
        // Just because we defined a final int somewhere, we should probably not infer that.
        result.unwrap_or(Type::Never)
    }

    pub fn infer_list_literal_from_context(
        &mut self,
        list: List,
        result_context: &mut ResultContext,
    ) -> Option<Inferred> {
        let i_s = self.i_s;
        result_context.on_unique_type_in_unpacked_union(
            i_s,
            i_s.db.python_state.list_node_ref(),
            |matcher, calculated_type_args| {
                let generic_t = calculated_type_args
                    .into_iter()
                    .next()
                    .unwrap()
                    .maybe_calculated_type(i_s.db)
                    .unwrap_or(Type::Any(AnyCause::Todo));
                let found = check_list_with_context(i_s, matcher, &generic_t, self.file, list);
                Inferred::from_type(found.unwrap_or_else(|| {
                    new_class!(
                        i_s.db.python_state.list_node_ref().as_link(),
                        generic_t.replace_type_var_likes(self.i_s.db, &mut |tv| {
                            tv.as_type_var_like().as_any_generic_item()
                        }),
                    )
                }))
            },
        )
    }

    // For {..}
    pub fn infer_dict_literal_from_context(
        &mut self,
        dict: Dict,
        result_context: &mut ResultContext,
    ) -> Option<Inferred> {
        let i_s = self.i_s;
        let typed_dict_result = result_context
            .with_type_if_exists(|type_, matcher| {
                let mut found = None;
                type_.on_any_typed_dict(i_s, matcher, &mut |matcher, td| {
                    found = self.check_typed_dict_literal_with_context(matcher, td, dict);
                    found.is_some()
                });
                // `found` might still be empty, because we matched Any.
                found.map(Inferred::from_type)
            })
            .flatten();
        if typed_dict_result.is_some() {
            return typed_dict_result;
        }

        infer_dict_like(i_s, result_context, |matcher, key_t, value_t| {
            self.check_dict_literal_with_context(matcher, &key_t, &value_t, dict)
        })
    }

    fn check_typed_dict_literal_with_context(
        &mut self,
        matcher: &mut Matcher,
        typed_dict: Rc<TypedDict>,
        dict: Dict,
    ) -> Option<Type> {
        let i_s = self.i_s;
        let mut extra_keys = vec![];
        let mut missing_keys: Vec<_> = typed_dict
            .members(i_s.db)
            .iter()
            .filter_map(|m| m.required.then(|| m.name.as_str(i_s.db)))
            .collect();
        for element in dict.iter_elements() {
            match element {
                DictElement::KeyValue(key_value) => {
                    let inf = self.infer_expression(key_value.key());
                    let node_ref = NodeRef::new(self.file, key_value.index());
                    match inf.maybe_string_literal(i_s) {
                        Some(literal) => {
                            let key = literal.as_str(i_s.db);
                            missing_keys.retain(|k| *k != key);
                            infer_typed_dict_item(
                                self.i_s,
                                &typed_dict,
                                matcher,
                                |issue| node_ref.add_issue(i_s, issue),
                                key,
                                &mut extra_keys,
                                |context| {
                                    self.infer_expression_with_context(key_value.value(), context)
                                },
                            );
                        }
                        None => {
                            missing_keys.clear(); // We do not want an error message anymore.
                            node_ref.add_issue(i_s, IssueType::TypedDictKeysMustBeStringLiteral);
                        }
                    }
                }
                DictElement::Star(dict_starred) => {
                    let inf = self.infer_expression_part(dict_starred.expression_part());
                    let node_ref = NodeRef::new(self.file, dict_starred.index());
                    match inf.as_cow_type(i_s).as_ref() {
                        Type::TypedDict(td) => {
                            for member in td.members(i_s.db).iter() {
                                let key = member.name.as_str(i_s.db);
                                if member.required {
                                    missing_keys.retain(|k| *k != key);
                                }
                                if i_s.db.project.flags.extra_checks {
                                    debug!("TODO need to implement --extra-checks");
                                }
                                infer_typed_dict_item(
                                    self.i_s,
                                    &typed_dict,
                                    matcher,
                                    |issue| node_ref.add_issue(i_s, issue),
                                    key,
                                    &mut extra_keys,
                                    |_| Inferred::from_type(member.type_.clone()),
                                );
                            }
                        }
                        t if is_any_dict(i_s.db, t) => (),
                        t => node_ref.add_issue(
                            i_s,
                            IssueType::TypedDictUnsupportedTypeInStarStar {
                                type_: t.format_short(i_s.db),
                            },
                        ),
                    }
                }
            }
        }
        let dict_node_ref = NodeRef::new(self.file, dict.index());
        maybe_add_extra_keys_issue(
            i_s.db,
            &typed_dict,
            |issue| dict_node_ref.add_issue(i_s, issue),
            extra_keys,
        );
        if !missing_keys.is_empty() {
            dict_node_ref.add_issue(
                i_s,
                IssueType::TypedDictMissingKeys {
                    typed_dict: typed_dict
                        .name_or_fallback(&FormatData::new_short(i_s.db))
                        .into(),
                    keys: missing_keys.iter().map(|k| Box::from(*k)).collect(),
                },
            )
        }
        Some(if matches!(&typed_dict.generics, TypedDictGenerics::None) {
            Type::TypedDict(typed_dict)
        } else {
            matcher
                .replace_type_var_likes_for_unknown_type_vars(i_s.db, &Type::TypedDict(typed_dict))
        })
    }

    fn check_dict_literal_with_context(
        &mut self,
        matcher: &mut Matcher,
        key_t: &Type,
        value_t: &Type,
        dict: Dict,
    ) -> Option<Type> {
        let mut new_key_context = ResultContext::Known(&key_t);
        let mut new_value_context = ResultContext::Known(&value_t);

        // Since it's a list, now check all the entries if they match the given
        // result generic;
        let mut had_error = false;
        let i_s = self.i_s;
        let mut inference = self.file.inference(i_s);
        for (i, key_value) in dict.iter_elements().enumerate() {
            match key_value {
                DictElement::KeyValue(key_value) => {
                    let key_inf = inference
                        .infer_expression_with_context(key_value.key(), &mut new_key_context);
                    let value_inf = inference
                        .infer_expression_with_context(key_value.value(), &mut new_value_context);
                    if !key_t
                        .is_super_type_of(i_s, matcher, &key_inf.as_cow_type(i_s))
                        .bool()
                        || !value_t
                            .is_super_type_of(i_s, matcher, &value_inf.as_cow_type(i_s))
                            .bool()
                    {
                        had_error = true;
                        NodeRef::new(self.file, key_value.index()).add_issue(
                            i_s,
                            IssueType::DictMemberMismatch {
                                item: i,
                                got_pair: format!(
                                    r#""{}": "{}""#,
                                    key_inf.format_short(i_s),
                                    value_inf.format_short(i_s)
                                )
                                .into(),
                                expected_pair: format!(
                                    r#""{}": "{}""#,
                                    key_t.format_short(i_s.db),
                                    value_t.format_short(i_s.db)
                                )
                                .into(),
                            },
                        );
                    }
                }
                DictElement::Star(starred) => {
                    let mapping = self.infer_expression_part(starred.expression_part());
                    if let Some((key, value)) = unpack_star_star(i_s, &mapping.as_cow_type(i_s)) {
                        if !key_t.is_super_type_of(i_s, matcher, &key).bool()
                            || !value_t.is_super_type_of(i_s, matcher, &value).bool()
                        {
                            had_error = true;
                            NodeRef::new(self.file, starred.index()).add_issue(
                                i_s,
                                IssueType::UnpackedDictMemberMismatch {
                                    item: i,
                                    got: mapping.format_short(i_s),
                                    expected: format!(
                                        "SupportsKeysAndGetItem[{}, {}]",
                                        key_t.format_short(i_s.db),
                                        value_t.format_short(i_s.db)
                                    )
                                    .into(),
                                },
                            )
                        }
                    } else {
                        todo!("inferred did not match")
                    }
                }
            }
        }
        (!had_error).then(|| {
            new_class!(
                i_s.db.python_state.dict_node_ref().as_link(),
                matcher.replace_type_var_likes_for_unknown_type_vars(i_s.db, &key_t),
                matcher.replace_type_var_likes_for_unknown_type_vars(i_s.db, &value_t),
            )
        })
    }

    // For dict(..)
    pub(crate) fn infer_dict_call_from_context(
        &mut self,
        args: &dyn Arguments<'db>,
        result_context: &mut ResultContext,
    ) -> Option<Inferred> {
        result_context
            .with_type_if_exists(|type_, matcher| {
                let mut found = None;
                type_.on_any_typed_dict(self.i_s, matcher, &mut |matcher, td| {
                    found = check_typed_dict_call(self.i_s, matcher, td, args);
                    found.is_some()
                });
                // `found` might still be empty, because we matched Any.
                found.map(Inferred::from_type)
            })
            .flatten()
    }

    pub fn dict_literal_without_context(&mut self, dict: Dict) -> Inferred {
        let dict_elements = dict.iter_elements();
        let i_s = self.i_s;
        if matches!(dict_elements, DictElementIterator::Empty) {
            return Inferred::from_type(new_class!(
                i_s.db.python_state.dict_node_ref().as_link(),
                Type::Any(AnyCause::Todo),
                Type::Any(AnyCause::Todo),
            ));
        }
        let mut values = Inferred::new_any(AnyCause::Todo);
        let keys = Inferred::gather_base_types(i_s, |gather_keys| {
            values = Inferred::gather_base_types(i_s, |gather_values| {
                for child in dict_elements {
                    match child {
                        DictElement::KeyValue(key_value) => {
                            gather_keys(self.infer_expression(key_value.key()));
                            gather_values(self.infer_expression(key_value.value()));
                        }
                        DictElement::Star(starred) => {
                            let mapping = self.infer_expression_part(starred.expression_part());
                            if let Some((key, value)) =
                                unpack_star_star(i_s, &mapping.as_cow_type(i_s))
                            {
                                gather_keys(Inferred::from_type(key));
                                gather_values(Inferred::from_type(value));
                            } else {
                                todo!("inferred did not match")
                            }
                        }
                    }
                }
            });
        });
        let keys = keys.as_type(i_s).avoid_implicit_literal(self.i_s.db);
        let values = values.as_type(i_s).avoid_implicit_literal(self.i_s.db);
        debug!(
            "Calculated generics for {}: dict[{}, {}]",
            dict.short_debug(),
            keys.format_short(i_s.db),
            values.format_short(i_s.db),
        );
        Inferred::from_type(new_class!(
            i_s.db.python_state.dict_node_ref().as_link(),
            keys,
            values,
        ))
    }

    pub fn parse_int(&mut self, int: Int, result_context: &mut ResultContext) -> Option<i64> {
        let result = int.parse();
        if result.is_none() {
            todo!("Add diagnostic?");
        }
        result
    }
}

fn is_any_dict(db: &Database, t: &Type) -> bool {
    match t {
        Type::Any(_) => true,
        Type::Class(c) => {
            c.link == db.python_state.dict_node_ref().as_link() && c.generics.all_any()
        }
        Type::Union(u) => u.iter().all(|t| is_any_dict(db, t)),
        _ => false,
    }
}

fn check_list_with_context<'db>(
    i_s: &InferenceState<'db, '_>,
    matcher: &mut Matcher,
    generic_t: &Type,
    file: &PythonFile,
    list: List,
) -> Option<Type> {
    let iterator = list.unpack();
    if matches!(iterator, StarLikeExpressionIterator::Empty) {
        return Some(new_class!(
            i_s.db.python_state.list_node_ref().as_link(),
            matcher.replace_type_var_likes_for_unknown_type_vars(i_s.db, &generic_t),
        ));
    }

    let mut new_result_context = ResultContext::Known(&generic_t);

    // Since it's a list, now check all the entries if they match the given
    // result generic;
    let mut had_error = false;
    for (item, element) in iterator.enumerate() {
        let mut check_item = |i_s: &InferenceState<'db, '_>, inferred: Inferred, index| {
            generic_t.error_if_not_matches_with_matcher(
                i_s,
                matcher,
                &inferred,
                |issue| NodeRef::new(file, index).add_issue(i_s, issue),
                |got, expected, _: &MismatchReason| {
                    had_error = true;
                    Some(IssueType::ListItemMismatch {
                        item,
                        got,
                        expected,
                    })
                },
            );
        };
        let mut inference = file.inference(i_s);
        match element {
            StarLikeExpression::NamedExpression(e) => {
                let inferred =
                    inference.infer_named_expression_with_context(e, &mut new_result_context);
                check_item(i_s, inferred, e.index())
            }
            StarLikeExpression::StarNamedExpression(starred) => {
                let inferred = inference.infer_expression_part(starred.expression_part());
                let from = NodeRef::new(file, starred.index());
                check_item(
                    i_s,
                    inferred.iter(i_s, from).infer_all(i_s),
                    starred.index(),
                )
            }
            StarLikeExpression::Expression(e) => unreachable!(),
            StarLikeExpression::StarExpression(e) => unreachable!(),
        };
    }
    (!had_error).then(|| {
        new_class!(
            i_s.db.python_state.list_node_ref().as_link(),
            matcher.replace_type_var_likes_for_unknown_type_vars(i_s.db, &generic_t),
        )
    })
}

pub fn on_argument_type_error(
    i_s: &InferenceState,
    error_text: &dyn Fn(&str) -> Option<Box<str>>,
    arg: &Argument,
    types: ErrorTypes,
) {
    let strings = types.as_boxed_strs(i_s);
    let got = match strings.got.as_ref() {
        "ModuleType" => "Module".to_string(),
        got => format!("\"{got}\""),
    };
    arg.add_issue(
        i_s,
        IssueType::ArgumentTypeIssue(
            format!(
                "Argument {}{} has incompatible type {got}; expected \"{}\"",
                arg.human_readable_index(i_s.db),
                error_text(" to ").as_deref().unwrap_or(""),
                strings.expected,
            )
            .into(),
        ),
    );
    types.add_mismatch_notes(|issue| arg.add_issue(i_s, issue))
}

pub fn infer_index(
    i_s: &InferenceState,
    file: &PythonFile,
    expr: Expression,
    callable: impl Fn(isize) -> Option<Inferred>,
) -> Option<Inferred> {
    file.inference(i_s)
        .infer_expression(expr)
        .run_on_int_literals(i_s, callable)
}

pub fn infer_string_index(
    i_s: &InferenceState,
    simple: Simple,
    callable: impl Fn(&str) -> Option<Inferred>,
    on_non_literal: impl Fn(),
) -> Inferred {
    let infer = |i_s: &InferenceState, literal: Literal| {
        if !matches!(literal.kind, LiteralKind::String(_)) {
            on_non_literal();
            return None;
        }
        let LiteralValue::String(s) = literal.value(i_s.db) else {
            unreachable!();
        };
        callable(s)
    };

    match simple
        .infer(i_s, &mut ResultContext::Unknown)
        .maybe_literal(i_s.db)
    {
        UnionValue::Single(literal) => infer(i_s, literal),
        UnionValue::Multiple(mut literals) => {
            literals
                .next()
                .and_then(|l| infer(i_s, l))
                .and_then(|mut inferred| {
                    for literal in literals {
                        if let Some(new_inf) = infer(i_s, literal) {
                            inferred = inferred.simplified_union(i_s, new_inf);
                        } else {
                            return None;
                        }
                    }
                    Some(inferred)
                })
        }
        UnionValue::Any => {
            on_non_literal();
            None
        }
    }
    .unwrap_or_else(|| Inferred::new_any(AnyCause::Todo))
}

pub fn infer_dict_like(
    i_s: &InferenceState,
    result_context: &mut ResultContext,
    infer_with_context: impl FnOnce(&mut Matcher, &Type, &Type) -> Option<Type>,
) -> Option<Inferred> {
    result_context.on_unique_type_in_unpacked_union(
        i_s,
        i_s.db.python_state.dict_node_ref(),
        |matcher, calculated_type_args| {
            let mut generics = calculated_type_args.into_iter();
            let key_t = generics
                .next()
                .unwrap()
                .maybe_calculated_type(i_s.db)
                .unwrap_or(Type::Any(AnyCause::Todo));
            let value_t = generics
                .next()
                .unwrap()
                .maybe_calculated_type(i_s.db)
                .unwrap_or(Type::Any(AnyCause::Todo));
            let found = infer_with_context(matcher, &key_t, &value_t);
            Inferred::from_type(found.unwrap_or_else(|| {
                new_class!(
                    i_s.db.python_state.dict_node_ref().as_link(),
                    key_t.replace_type_var_likes(i_s.db, &mut |tv| {
                        tv.as_type_var_like().as_any_generic_item()
                    }),
                    value_t.replace_type_var_likes(i_s.db, &mut |tv| {
                        tv.as_type_var_like().as_any_generic_item()
                    }),
                )
            }))
        },
    )
}
