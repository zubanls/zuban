use std::sync::Arc;

use parsa_python_cst::{Expression, ExpressionContent, ExpressionPart, NamedExpression, NodeIndex};

use crate::{
    database::{ClassKind, ComplexPoint, Specific},
    debug,
    diagnostics::IssueKind,
    inference_state::InferenceState,
    type_::{ClassGenerics, TupleArgs, TupleUnpack, Type},
    utils::join_with_commas,
};

use super::inference::Inference;

impl Inference<'_, '_, '_> {
    pub fn check_isinstance_or_issubclass_type(
        &self,
        arg: NamedExpression,
        issubclass: bool,
    ) -> Option<Type> {
        let isinstance_type = IsinstanceInference {
            inference: self,
            add_issue: &|index, kind| self.add_issue(index, kind),
        }
        .isinstance_or_issubclass_type(arg.expression(), issubclass)?;
        for t in isinstance_type.iter_with_unpacked_unions(self.i_s.db) {
            let cannot_use_with = |with| {
                self.add_issue(
                    arg.index(),
                    IssueKind::CannotUseIsinstanceWith {
                        func: match issubclass {
                            false => "isinstance",
                            true => "issubclass",
                        },
                        with,
                    },
                );
            };
            match t {
                Type::TypedDict(_) => cannot_use_with("TypedDict"),
                Type::NewType(_) => cannot_use_with("NewType"),
                _ => (),
            }
        }
        Some(isinstance_type)
    }
}

struct IsinstanceInference<'db, 'file, 'i_s, 'a> {
    inference: &'a Inference<'db, 'file, 'i_s>,
    add_issue: &'a dyn Fn(NodeIndex, IssueKind) -> bool,
}

impl IsinstanceInference<'_, '_, '_, '_> {
    fn isinstance_or_issubclass_type(&self, expr: Expression, issubclass: bool) -> Option<Type> {
        // One might think that we could just use type computation here for isinstance types. This
        // is however not really working, because the types can also be inferred like
        //
        //     isinstance(foo, type(bar))

        match expr.unpack() {
            ExpressionContent::ExpressionPart(part) => {
                self.isinstance_or_issubclass_type_for_expr_part(part, issubclass, false)
            }
            _ => None,
        }
    }

    fn isinstance_or_issubclass_type_for_expr_part(
        &self,
        part: ExpressionPart,
        issubclass: bool,
        from_union: bool,
    ) -> Option<Type> {
        let cannot_use_with = |with| {
            (self.add_issue)(
                part.index(),
                IssueKind::CannotUseIsinstanceWith {
                    func: match issubclass {
                        false => "isinstance",
                        true => "issubclass",
                    },
                    with,
                },
            );
            Some(Type::ERROR)
        };
        match part {
            ExpressionPart::BitwiseOr(disjunction) => {
                let (first, second) = disjunction.unpack();
                let t1 =
                    self.isinstance_or_issubclass_type_for_expr_part(first, issubclass, true)?;
                let t2 =
                    self.isinstance_or_issubclass_type_for_expr_part(second, issubclass, true)?;
                Some(t1.union(t2))
            }
            _ => {
                let i_s = self.inference.i_s;
                let inf = self.inference.infer_expression_part(part);
                match inf.maybe_saved_specific(i_s.db) {
                    Some(Specific::TypingAny) => {
                        return cannot_use_with("Any");
                    }
                    Some(Specific::BuiltinsType) => {
                        if issubclass {
                            return Some(i_s.db.python_state.bare_type_type());
                        } else {
                            return Some(i_s.db.python_state.type_of_any.clone());
                        }
                    }
                    _ => (),
                }

                let t = inf.as_cow_type(i_s);
                if let Type::Class(c) = t.as_ref()
                    && Some(c.link) == i_s.db.python_state.union_type_link()
                {
                    debug!("Found a union type for isinstance, try to compute it");
                    let node_ref = inf.maybe_saved_node_ref(i_s.db)?;
                    let expr = node_ref.maybe_expression()?;
                    IsinstanceInference {
                        inference: &node_ref
                            .file
                            .inference(&InferenceState::new(i_s.db, node_ref.file)),
                        add_issue: &|_, kind| (self.add_issue)(part.index(), kind),
                    }
                    .isinstance_or_issubclass_type(expr, issubclass)
                } else if let Some(node_ref) = inf.maybe_saved_node_ref(i_s.db)
                    && let Some(ComplexPoint::TypeAlias(alias)) = node_ref.maybe_complex()
                {
                    debug!("Found a potential `: TypeAlias` union type, try to compute it");
                    self.process_isinstance_type(
                        part,
                        &Type::Type(Arc::new(alias.type_if_valid().clone())),
                        issubclass,
                        from_union,
                    )
                } else {
                    self.process_isinstance_type(part, &t, issubclass, from_union)
                }
            }
        }
    }

    fn process_isinstance_type(
        &self,
        part: ExpressionPart,
        t: &Type,
        issubclass: bool,
        from_union: bool,
    ) -> Option<Type> {
        let i_s = self.inference.i_s;
        match t {
            Type::Tuple(tup) => match &tup.args {
                TupleArgs::FixedLen(ts) => self.process_tuple_types(part, ts.iter(), issubclass),
                TupleArgs::ArbitraryLen(t) => {
                    self.process_isinstance_type(part, t, issubclass, false)
                }
                TupleArgs::WithUnpack(w) => match &w.unpack {
                    TupleUnpack::ArbitraryLen(t) => self.process_tuple_types(
                        part,
                        w.before
                            .iter()
                            .chain(w.after.iter())
                            .chain(std::iter::once(t)),
                        issubclass,
                    ),
                    TupleUnpack::TypeVarTuple(_) => None,
                },
            },
            Type::Type(t) => {
                if let Type::Class(cls) = t.as_ref() {
                    if !matches!(
                        &cls.generics,
                        ClassGenerics::NotDefinedYet | ClassGenerics::None { .. }
                    ) {
                        (self.add_issue)(
                            part.index(),
                            IssueKind::CannotUseIsinstanceWithParametrizedGenerics,
                        );
                        return Some(Type::ERROR);
                    }
                    let class = cls.class(i_s.db);
                    let class_infos = class.use_cached_class_infos(i_s.db);
                    if matches!(class_infos.kind, ClassKind::Protocol) {
                        if !class_infos.is_runtime_checkable {
                            (self.add_issue)(part.index(), IssueKind::ProtocolNotRuntimeCheckable);
                        }
                        if issubclass {
                            let non_method_protocol_members =
                                class.non_method_protocol_members(i_s.db);
                            if !non_method_protocol_members.is_empty() {
                                (self.add_issue)(
                                    part.index(),
                                    IssueKind::IssubcclassWithProtocolNonMethodMembers {
                                        protocol: class.name().into(),
                                        non_method_members: join_with_commas(
                                            non_method_protocol_members,
                                        )
                                        .into(),
                                    },
                                );
                            }
                        }
                    }
                }
                Some((**t).clone())
            }
            Type::Any(cause) => Some(Type::Any(*cause)),
            /*
            Type::Literal(l) => {
                cannot_use_with(self, "Literal")
            }
            */
            Type::None if from_union => Some(t.clone()),
            _ => {
                debug!("isinstance with bad type: {}", t.format_short(i_s.db));
                None
            }
        }
    }

    fn process_tuple_types<'x>(
        &self,
        part: ExpressionPart,
        types: impl Iterator<Item = &'x Type>,
        issubclass: bool,
    ) -> Option<Type> {
        let ts: Option<Vec<Type>> = types
            .map(|t| self.process_isinstance_type(part, t, issubclass, true))
            .collect();
        Some(Type::simplified_union_from_iterators(
            self.inference.i_s,
            ts?.iter(),
        ))
    }
}
