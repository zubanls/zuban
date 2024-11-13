use std::rc::Rc;

use parsa_python_cst::{
    Dict, DictElement, DictElementIterator, DictStarred, Expression, FunctionDef, Int, NodeIndex,
    StarLikeExpression, StarLikeExpressionIterator, NAME_DEF_TO_NAME_DIFFERENCE,
};

use crate::{
    arguments::{unpack_star_star, Arg, Args},
    database::{Database, PointKind, Specific},
    debug,
    diagnostics::IssueKind,
    file::{Inference, PythonFile},
    format_data::FormatData,
    getitem::Simple,
    inference_state::InferenceState,
    inferred::UnionValue,
    matching::{ErrorStrs, ErrorTypes, GotType, Match, Matcher, MismatchReason, ResultContext},
    new_class,
    node_ref::NodeRef,
    type_::{
        check_typed_dict_call, infer_typed_dict_item, maybe_add_extra_keys_issue, AnyCause,
        Literal, LiteralKind, LiteralValue, NeverCause, Type, TypedDict, TypedDictGenerics,
    },
    Inferred,
};

impl<'db> Inference<'db, '_, '_> {
    pub fn create_list_or_set_generics<'x>(
        &self,
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
        result.unwrap_or(Type::Never(NeverCause::Other))
    }

    pub fn infer_list_or_set_literal_from_context(
        &self,
        elements: StarLikeExpressionIterator,
        result_context: &mut ResultContext,
        wanted_node_ref: NodeRef,
    ) -> Option<Inferred> {
        let i_s = self.i_s;
        result_context.on_unique_type_in_unpacked_union(
            i_s,
            wanted_node_ref,
            |matcher, cls_matcher| {
                let generic_t = cls_matcher
                    .into_type_arg_iterator_or_any(i_s.db)
                    .next()
                    .unwrap();

                let item = if matches!(elements, StarLikeExpressionIterator::Empty) {
                    matcher
                        .replace_type_var_likes_for_unknown_type_vars(i_s.db, &generic_t)
                        .into_owned()
                } else {
                    let found = check_elements_with_context(
                        i_s,
                        matcher,
                        &generic_t,
                        self.file,
                        elements,
                        wanted_node_ref,
                    );
                    found.unwrap_or_else(|| {
                        generic_t
                            .replace_type_var_likes(self.i_s.db, &mut |tv| {
                                Some(tv.as_any_generic_item())
                            })
                            .unwrap_or(generic_t)
                    })
                };
                Inferred::from_type(new_class!(wanted_node_ref.as_link(), item))
            },
        )
    }

    // For {..}
    pub fn infer_dict_literal_from_context(
        &self,
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
            self.check_dict_literal_with_context(matcher, key_t, value_t, dict)
        })
    }

    fn check_typed_dict_literal_with_context(
        &self,
        matcher: &mut Matcher,
        typed_dict: Rc<TypedDict>,
        dict: Dict,
    ) -> Option<Type> {
        let i_s = self.i_s;
        let mut extra_keys = vec![];
        let mut missing_keys: Vec<_> = typed_dict
            .members(i_s.db)
            .iter()
            .filter(|&m| m.required)
            .map(|m| m.name.as_str(i_s.db))
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
                            node_ref.add_issue(i_s, IssueKind::TypedDictKeysMustBeStringLiteral);
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
                                if self.flags().extra_checks {
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
                            IssueKind::TypedDictUnsupportedTypeInStarStar {
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
                IssueKind::TypedDictMissingKeys {
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
                .into_owned()
        })
    }

    fn check_dict_literal_with_context(
        &self,
        matcher: &mut Matcher,
        key_t: &Type,
        value_t: &Type,
        dict: Dict,
    ) -> Option<Type> {
        let mut new_key_context = ResultContext::new_known(key_t);
        let mut new_value_context = ResultContext::new_known(value_t);

        // Since it's a list, now check all the entries if they match the given
        // result generic;
        let mut had_error = false;
        let i_s = self.i_s;
        let inference = self.file.inference(i_s);
        for (i, key_value) in dict.iter_elements().enumerate() {
            match key_value {
                DictElement::KeyValue(key_value) => {
                    let key_inf = inference
                        .infer_expression_with_context(key_value.key(), &mut new_key_context);
                    let got_key_t = key_inf.as_cow_type(i_s);
                    let key_match = key_t.is_super_type_of(i_s, matcher, &got_key_t);

                    let value_inf = inference
                        .infer_expression_with_context(key_value.value(), &mut new_value_context);
                    let got_value_t = value_inf.as_cow_type(i_s);
                    let value_match = value_t.is_super_type_of(i_s, matcher, &got_value_t);

                    if !key_match.bool() || !value_match.bool() {
                        had_error = true;
                        let format_errors = |expected, got, match_| {
                            let error_types = ErrorTypes {
                                expected,
                                got: GotType::Type(got),
                                matcher: Some(matcher),
                                reason: &match match_ {
                                    Match::False { reason, .. } => reason,
                                    Match::True { .. } => MismatchReason::None,
                                },
                            };
                            let ErrorStrs { expected, got } = error_types.as_boxed_strs(i_s.db);
                            (expected, got)
                        };
                        let (expected_key, got_key) = format_errors(key_t, &got_key_t, key_match);
                        let (expected_value, got_value) =
                            format_errors(value_t, &got_value_t, value_match);
                        NodeRef::new(self.file, key_value.index()).add_issue(
                            i_s,
                            IssueKind::DictMemberMismatch {
                                item: i,
                                got_pair: format!(r#""{got_key}": "{got_value}""#).into(),
                                expected_pair: format!(r#""{expected_key}": "{expected_value}""#)
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
                        }
                    } else {
                        had_error = true;
                    }
                    if had_error {
                        self.add_unpacked_dict_member_issue(i, starred, mapping, key_t, value_t)
                    }
                }
            }
        }
        (!had_error).then(|| {
            new_class!(
                i_s.db.python_state.dict_node_ref().as_link(),
                matcher
                    .replace_type_var_likes_for_unknown_type_vars(i_s.db, key_t)
                    .into_owned(),
                matcher
                    .replace_type_var_likes_for_unknown_type_vars(i_s.db, value_t)
                    .into_owned(),
            )
        })
    }

    fn add_unpacked_dict_member_issue(
        &self,
        i: usize,
        starred: DictStarred,
        mapping: Inferred,
        key_t: &Type,
        value_t: &Type,
    ) {
        NodeRef::new(self.file, starred.index()).add_issue(
            self.i_s,
            IssueKind::UnpackedDictMemberMismatch {
                item: i,
                got: mapping.format_short(self.i_s),
                expected: format!(
                    "SupportsKeysAndGetItem[{}, {}]",
                    key_t.format_short(self.i_s.db),
                    value_t.format_short(self.i_s.db)
                )
                .into(),
            },
        )
    }

    // For dict(..)
    pub(crate) fn infer_dict_call_from_context(
        &self,
        args: &dyn Args<'db>,
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

    pub fn dict_literal_without_context(&self, dict: Dict) -> Inferred {
        let dict_elements = dict.iter_elements();
        let i_s = self.i_s;
        if matches!(dict_elements, DictElementIterator::Empty) {
            return Inferred::from_type(new_class!(
                i_s.db.python_state.dict_node_ref().as_link(),
                Type::Never(NeverCause::Inference),
                Type::Never(NeverCause::Inference),
            ));
        }
        let mut key_t = Type::Never(NeverCause::Inference);
        let mut value_t = Type::Never(NeverCause::Inference);
        for (i, child) in dict_elements.enumerate() {
            match child {
                DictElement::KeyValue(key_value) => {
                    key_t = key_t.common_base_type(
                        i_s,
                        &self.infer_expression(key_value.key()).as_cow_type(i_s),
                    );
                    value_t = value_t.common_base_type(
                        i_s,
                        &self.infer_expression(key_value.value()).as_cow_type(i_s),
                    );
                }
                DictElement::Star(starred) => {
                    let mapping = self.infer_expression_part(starred.expression_part());
                    if let Some((key, value)) = unpack_star_star(i_s, &mapping.as_cow_type(i_s)) {
                        key_t = key_t.common_base_type(i_s, &key);
                        value_t = value_t.common_base_type(i_s, &value);
                    } else {
                        self.add_unpacked_dict_member_issue(i, starred, mapping, &key_t, &value_t);
                        if key_t.is_never() {
                            key_t = Type::Any(AnyCause::FromError)
                        }
                        if value_t.is_never() {
                            value_t = Type::Any(AnyCause::FromError)
                        }
                    }
                }
            }
        }
        let key_t = key_t.avoid_implicit_literal(self.i_s.db);
        let value_t = value_t.avoid_implicit_literal(self.i_s.db);
        debug!(
            "Calculated generics for {}: dict[{}, {}]",
            dict.short_debug(),
            key_t.format_short(i_s.db),
            value_t.format_short(i_s.db),
        );
        Inferred::from_type(new_class!(
            i_s.db.python_state.dict_node_ref().as_link(),
            key_t,
            value_t,
        ))
    }

    pub fn parse_int(&self, int: Int, result_context: &mut ResultContext) -> Option<i64> {
        let result = int.parse();
        if result.is_none() {
            debug!("TODO Add diagnostic for unparsable ints?");
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

fn check_elements_with_context<'db>(
    i_s: &InferenceState<'db, '_>,
    matcher: &mut Matcher,
    generic_t: &Type,
    file: &PythonFile,
    elements: StarLikeExpressionIterator,
    wanted_node_ref: NodeRef,
) -> Option<Type> {
    // Since it's a list or a set, now check all the entries if they match the given
    // result generic;
    let mut had_error = false;
    for (item, element) in elements.enumerate() {
        let mut check_item = |i_s: &InferenceState<'db, '_>, matcher, inferred: Inferred, index| {
            generic_t.error_if_not_matches_with_matcher(
                i_s,
                matcher,
                &inferred,
                |issue| NodeRef::new(file, index).add_issue(i_s, issue),
                |error_types, _: &MismatchReason| {
                    let ErrorStrs { expected, got } = error_types.as_boxed_strs(i_s.db);
                    had_error = true;
                    if wanted_node_ref == i_s.db.python_state.list_node_ref() {
                        Some(IssueKind::ListItemMismatch {
                            item,
                            got,
                            expected,
                        })
                    } else {
                        Some(IssueKind::SetItemMismatch {
                            item,
                            got,
                            expected,
                        })
                    }
                },
            );
        };
        let inference = file.inference(i_s);
        match element {
            StarLikeExpression::NamedExpression(e) => {
                let mut new_result_context = ResultContext::WithMatcher {
                    matcher,
                    type_: generic_t,
                };
                let inferred =
                    inference.infer_named_expression_with_context(e, &mut new_result_context);
                check_item(i_s, matcher, inferred, e.index())
            }
            StarLikeExpression::StarNamedExpression(starred) => {
                let inferred = inference.infer_expression_part(starred.expression_part());
                let from = NodeRef::new(file, starred.index());
                check_item(
                    i_s,
                    matcher,
                    inferred.iter(i_s, from).infer_all(i_s),
                    starred.index(),
                )
            }
            StarLikeExpression::Expression(e) => unreachable!(),
            StarLikeExpression::StarExpression(e) => unreachable!(),
        };
    }
    (!had_error).then(|| {
        matcher
            .replace_type_var_likes_for_unknown_type_vars(i_s.db, generic_t)
            .into_owned()
    })
}

pub fn on_argument_type_error(
    i_s: &InferenceState,
    error_text: &dyn Fn(&str) -> Option<Box<str>>,
    arg: &Arg,
    types: ErrorTypes,
) {
    let strings = types.as_boxed_strs(i_s.db);
    let got = match strings.got.as_ref() {
        "ModuleType" => "Module".to_string(),
        got => format!("\"{got}\""),
    };
    arg.add_argument_issue(i_s, &got, &strings.expected, error_text);
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
        |matcher, cls_matcher| {
            let mut generics = cls_matcher.into_type_arg_iterator_or_any(i_s.db);
            let key_t = generics.next().unwrap();
            let value_t = generics.next().unwrap();
            let found = infer_with_context(matcher, &key_t, &value_t);
            Inferred::from_type(found.unwrap_or_else(|| {
                new_class!(
                    i_s.db.python_state.dict_node_ref().as_link(),
                    key_t
                        .replace_type_var_likes(i_s.db, &mut |tv| Some(tv.as_any_generic_item()))
                        .unwrap_or(key_t),
                    value_t
                        .replace_type_var_likes(i_s.db, &mut |tv| Some(tv.as_any_generic_item()))
                        .unwrap_or(value_t)
                )
            }))
        },
    )
}

pub(super) fn func_of_self_symbol(file: &PythonFile, self_symbol: NodeIndex) -> FunctionDef {
    // This is due to the fact that the nodes before <name> in self.<name> are
    // name_definition, `.` and then finally `self`.
    let self_index = self_symbol - NAME_DEF_TO_NAME_DIFFERENCE - 2;
    let self_point = file.points.get(self_index);
    debug_assert!(self_point.kind() == PointKind::Redirect);
    let param_name_node_ref = NodeRef::new(file, self_point.node_index());
    debug_assert_eq!(
        param_name_node_ref
            .add_to_node_index(-(NAME_DEF_TO_NAME_DIFFERENCE as i64))
            .point()
            .specific(),
        Specific::MaybeSelfParam
    );
    param_name_node_ref.as_name().expect_as_param_of_function()
}
