use parsa_python_cst::{
    ExpressionContent, ExpressionPart, NamedExpression, NamedExpressionContent,
};

use crate::{
    database::{ClassKind, Specific},
    debug,
    diagnostics::IssueKind,
    type_::{ClassGenerics, NeverCause, TupleArgs, TupleUnpack, Type},
    utils::join_with_commas,
};

use super::inference::Inference;

impl Inference<'_, '_, '_> {
    pub fn check_isinstance_or_issubclass_type(
        &self,
        arg: NamedExpression,
        issubclass: bool,
    ) -> Option<Type> {
        let isinstance_type = self.isinstance_or_issubclass_type(arg, issubclass)?;
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
                )
            };
            match t {
                Type::TypedDict(_) => cannot_use_with("TypedDict"),
                Type::NewType(_) => cannot_use_with("NewType"),
                _ => (),
            }
        }
        Some(isinstance_type)
    }

    fn isinstance_or_issubclass_type(
        &self,
        arg: NamedExpression,
        issubclass: bool,
    ) -> Option<Type> {
        let expr = match arg.unpack() {
            NamedExpressionContent::Expression(expr) => expr,
            NamedExpressionContent::Walrus(w) => w.expression(),
        };

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
            self.add_issue(
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
                let inf = self.infer_expression_part(part);
                match inf.maybe_saved_specific(self.i_s.db) {
                    Some(Specific::TypingAny) => {
                        return cannot_use_with("Any");
                    }
                    Some(Specific::BuiltinsType) => {
                        if issubclass {
                            return Some(self.i_s.db.python_state.bare_type_type());
                        } else {
                            return Some(self.i_s.db.python_state.type_of_any.clone());
                        }
                    }
                    _ => (),
                }

                self.process_isinstance_type(
                    part,
                    &inf.as_cow_type(self.i_s),
                    issubclass,
                    from_union,
                )
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
                        ClassGenerics::NotDefinedYet | ClassGenerics::None
                    ) {
                        self.add_issue(
                            part.index(),
                            IssueKind::CannotUseIsinstanceWithParametrizedGenerics,
                        );
                        return Some(Type::ERROR);
                    }
                    let class = cls.class(self.i_s.db);
                    let class_infos = class.use_cached_class_infos(self.i_s.db);
                    if matches!(class_infos.class_kind, ClassKind::Protocol) {
                        if !class_infos.is_runtime_checkable {
                            self.add_issue(part.index(), IssueKind::ProtocolNotRuntimeCheckable)
                        }
                        if issubclass {
                            let non_method_protocol_members =
                                class.non_method_protocol_members(self.i_s.db);
                            if !non_method_protocol_members.is_empty() {
                                self.add_issue(
                                    part.index(),
                                    IssueKind::IssubcclassWithProtocolNonMethodMembers {
                                        protocol: class.name().into(),
                                        non_method_members: join_with_commas(
                                            non_method_protocol_members.into_iter(),
                                        )
                                        .into(),
                                    },
                                )
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
                debug!("isinstance with bad type: {}", t.format_short(self.i_s.db));
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
        let ts = ts?;
        Some(match ts.len() {
            0 => Type::Never(NeverCause::Other),
            1 => ts.into_iter().next().unwrap(),
            _ => Type::simplified_union_from_iterators(self.i_s, ts.iter()),
        })
    }
}
