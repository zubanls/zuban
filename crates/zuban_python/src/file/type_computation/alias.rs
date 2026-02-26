use std::{borrow::Cow, sync::Arc};

use parsa_python_cst::{
    ArgOrComprehension, Argument, ArgumentsDetails, Assignment, AssignmentContent, Atom,
    AtomContent, Expression, ExpressionContent, ExpressionPart, Name, NameDef,
    NameOrPrimaryWithNames, NodeIndex, Primary, PrimaryContent, PrimaryOrAtom, PythonString,
    StarExpressionContent, Target, TypeLike,
};
use utils::{AlreadySeen, FastHashSet};

use super::{
    super::name_resolution::NameResolution, ClassNodeRef, InvalidVariableType, Lookup, TypeContent,
    TypeVarFinder, UnknownCause,
};
use crate::{
    arguments::{Args, SimpleArgs},
    database::{
        ClassKind, ComplexPoint, Database, Locality, Point, PointKind, PointLink, Specific,
        TypeAlias,
    },
    debug,
    diagnostics::IssueKind,
    file::{
        PythonFile, TypeVarCallbackReturn,
        name_resolution::PointResolution,
        type_computation::{
            TypeCommentState, TypeComputation, TypeComputationOrigin,
            named_tuple::new_typing_named_tuple_internal,
            typed_dict::new_typed_dict_with_execution_syntax,
        },
    },
    getitem::{SliceOrSimple, SliceType},
    inference_state::InferenceState,
    inferred::Inferred,
    node_ref::NodeRef,
    recoverable_error,
    type_::{
        AnyCause, GenericItem, NamedTuple, TupleArgs, TupleUnpack, Type, TypeVarLike, TypeVarLikes,
        TypeVarManager, TypedDict,
    },
    type_helpers::{Class, cache_class_name},
    utils::debug_indent,
};

const ASSIGNMENT_TYPE_CACHE_OFFSET: u32 = 1;
const ALIAS_TYPE_CACHE_OFFSET: u32 = 1;

impl<'db, 'file> NameResolution<'db, 'file, '_> {
    pub fn is_valid_type_assignment(&self, assignment: Assignment<'file>) -> bool {
        !matches!(
            self.compute_type_assignment(assignment),
            Lookup::T(TypeContent::InvalidVariable(_) | TypeContent::Unknown(_))
        )
    }

    pub(super) fn compute_type_assignment(
        &self,
        assignment: Assignment<'file>,
    ) -> Lookup<'file, 'file> {
        let mut cause = AliasCause::Implicit;
        if let AssignmentContent::WithAnnotation(target, annotation, _) = assignment.unpack() {
            // We have to ensure that if this assignment is used as an invalid type within the
            // annotation again that we don't get cycles. Therefore we add calculating to the
            // annotation if necessary. This is not normally done to annotations, but doesn't
            // matter, since calculating will just be overwritten.
            if let Target::Name(name_def) = target {
                let annotation_ref = NodeRef::new(self.file, annotation.index());
                let p = annotation_ref.point();
                if !p.calculated() {
                    if p.calculating() {
                        return Lookup::T(TypeContent::InvalidVariable(
                            InvalidVariableType::NameError {
                                name: name_def.as_code(),
                            },
                        ));
                    }
                    annotation_ref.set_point(Point::new_calculating());
                }
            }

            self.ensure_cached_annotation(annotation, true);
            match self.file.points.get(annotation.index()).maybe_specific() {
                Some(Specific::AnnotationTypeAlias) => cause = AliasCause::TypingTypeAlias,
                // Final/ClassVar may not have been calculated like x: Final = 1
                Some(
                    Specific::AnnotationOrTypeCommentFinal
                    | Specific::AnnotationOrTypeCommentClassVar,
                ) => (),
                _ => {
                    if let Type::Any(cause) = self.use_cached_annotation_type(annotation).as_ref() {
                        return Lookup::T(TypeContent::Unknown(UnknownCause::AnyCause(*cause)));
                    }
                }
            }
        }
        self.compute_type_assignment_internal(assignment, cause)
    }

    fn compute_type_assignment_internal(
        &self,
        assignment: Assignment,
        cause: AliasCause,
    ) -> Lookup<'file, 'file> {
        // Use the node star_targets or single_target, because they are not used otherwise.
        let file = self.file;
        let cached_type_node_ref = assignment_type_node_ref(file, assignment);
        let point = cached_type_node_ref.point();
        if point.calculated() {
            return load_cached_type(cached_type_node_ref);
        }
        let was_calculating = point.calculating();
        cached_type_node_ref.set_point(Point::new_calculating());

        if matches!(cause, AliasCause::Implicit) && !point.calculating() {
            // Only non-explicit TypeAliases are allowed here.
            if let Some(name_or_prim) = assignment.maybe_simple_type_reassignment() {
                // For very simple cases like `Foo = int`. Not sure yet if this going to stay.
                debug!(
                    "Found alias that could maybe just be redirected: {}",
                    assignment.as_code()
                );
                let _indent = debug_indent();
                let lookup = match name_or_prim {
                    NameOrPrimaryWithNames::Name(name) => Some(self.lookup_type_name(name)),
                    NameOrPrimaryWithNames::PrimaryWithNames(primary) => {
                        self.lookup_type_primary_if_only_names(primary)
                    }
                };
                match lookup {
                    Some(Lookup::T(TypeContent::SpecialCase(Specific::TypingAny))) => {
                        // This is a bit of a weird special case that was necessary to pass the test
                        // testDisallowAnyExplicitAlias
                        if self.flags().disallow_any_explicit {
                            NodeRef::new(file, name_or_prim.index())
                                .add_issue(self.i_s, IssueKind::DisallowedAnyExplicit);
                        }
                    }
                    // It seems like Mypy is handling these differently?
                    Some(Lookup::T(
                        TypeContent::SpecialCase(_) | TypeContent::TypedDictDefinition(_),
                    )) => (),
                    Some(lookup) => {
                        debug!("Alias can be redirected: {lookup:?}");
                        // We have to reset if the type was not calculated
                        if cached_type_node_ref.point().calculating() {
                            cached_type_node_ref.set_point(Point::new_uncalculated());
                        }
                        return lookup;
                    }
                    None => {
                        debug!("Alias can not be redirected");
                    }
                }
            }
        }
        if let Some((name_def, annotation, expr)) =
            assignment.maybe_simple_type_expression_assignment()
        {
            debug!("Started type alias calculation: {}", name_def.as_code());
            if let Some(type_comment) =
                self.check_for_type_comment_internal(assignment, || point.calculating())
            {
                // This case is a bit weird in Mypy, but it makes it possible to use a type
                // definition like:
                //
                //     Foo = 1  # type: Any
                if let TypeCommentState::Type(t) = &type_comment.type_
                    && let Type::Any(_) = t.as_ref()
                {
                    cached_type_node_ref
                        .set_point(Point::new_specific(Specific::AnyDueToError, Locality::Todo));
                    return self.compute_type_assignment_internal(assignment, cause);
                }
            }
            if matches!(cause, AliasCause::Implicit)
                && (expr.maybe_single_string_literal().is_some() || annotation.is_some())
            {
                return Lookup::T(TypeContent::InvalidVariable(InvalidVariableType::Variable(
                    NodeRef::new(file, name_def.index()),
                )));
            }

            let check_for_alias = |origin| {
                // We never want to have unfinished aliases in the class mro and we therefore make
                // sure that classes are initialized first.
                self.pre_calc_classes_in_expr(expr);
                if cached_type_node_ref.point().calculated() {
                    return load_cached_type(cached_type_node_ref);
                }
                self.check_for_alias(origin, cached_type_node_ref, name_def, expr, cause)
            };

            if !matches!(cause, AliasCause::Implicit) || was_calculating {
                return check_for_alias(CalculatingAliasType::Normal);
            }

            let result = self
                .compute_special_assignments(assignment, name_def, expr)
                .unwrap_or_else(check_for_alias);
            debug!("Finished type alias calculation: {}", name_def.as_code());
            result
        } else {
            if let AssignmentContent::WithAnnotation(target, annotation, right) =
                assignment.unpack()
            {
                let calculating = match target {
                    Target::Name(n) => {
                        file.points.get(n.index()).maybe_calculated_and_specific()
                            == Some(Specific::Cycle)
                    }
                    _ => false,
                };
                if calculating {
                    return Lookup::UNKNOWN_REPORTED;
                }
                self.ensure_cached_annotation(annotation, right.is_some());

                // Final/ClassVar may not have been calculated like x: Final = 1
                if !matches!(
                    self.file.points.get(annotation.index()).maybe_specific(),
                    Some(
                        Specific::AnnotationOrTypeCommentFinal
                            | Specific::AnnotationOrTypeCommentClassVar,
                    )
                ) && let Type::Any(cause) = self.use_cached_annotation_type(annotation).as_ref()
                {
                    return Lookup::T(TypeContent::Unknown(UnknownCause::AnyCause(*cause)));
                }
            }
            Lookup::T(TypeContent::InvalidVariable(InvalidVariableType::Other))
        }
    }

    fn compute_special_assignments<'x>(
        &self,
        assignment: Assignment,
        name_def: NameDef,
        expr: Expression<'x>,
    ) -> Result<Lookup<'file, 'file>, CalculatingAliasType<'x>> {
        // At this point we only take care of special assignments like TypeVars,
        // collection.namedtuple, etc.
        // This does not include NamedTuple, NewType and TypedDict executions, which are taken care
        // of in normal alias calculation, because they need access to type vars and can in general
        // create recursive types.
        let p = self.file.points.get(name_def.index());
        let cached_type_node_ref = assignment_type_node_ref(self.file, assignment);
        if p.calculated() {
            // The special assignment has been inferred with the normal inference and we simply set
            // the correct alias below.
            debug_assert!(
                self.file.points.get(assignment.index()).calculated()
                    // This happens when we are in an untyped context
                    || p.maybe_specific() == Some(Specific::AnyDueToError)
            );
            if p.maybe_specific() == Some(Specific::Cycle) {
                return Ok(Lookup::UNKNOWN_REPORTED);
            }
            // TODO why is this necessary? Simply explain why!
            self.maybe_special_assignment_execution(expr)?;
        } else {
            let special = self.maybe_special_assignment_execution(expr)?;
            let inf = match special {
                SpecialAssignmentKind::Enum(class, args) => self
                    .compute_functional_enum_definition(
                        class,
                        &SimpleArgs::new(*self.i_s, self.file, args.primary_index, args.details),
                    )
                    .unwrap_or_else(Inferred::new_invalid_type_definition),
                SpecialAssignmentKind::CollectionsNamedTuple(a) => self
                    .compute_collections_named_tuple(&SimpleArgs::new(
                        *self.i_s,
                        self.file,
                        a.primary_index,
                        a.details,
                    )),
                SpecialAssignmentKind::TypeVar(a) => self.compute_type_var_assignment(
                    &SimpleArgs::new(*self.i_s, self.file, a.primary_index, a.details),
                ),
                SpecialAssignmentKind::TypeVarTuple(a) => self.compute_type_var_tuple_assignment(
                    &SimpleArgs::new(*self.i_s, self.file, a.primary_index, a.details),
                ),
                SpecialAssignmentKind::ParamSpec(a) => self.compute_param_spec_assignment(
                    &SimpleArgs::new(*self.i_s, self.file, a.primary_index, a.details),
                ),
                SpecialAssignmentKind::TypeOf(args) => {
                    debug_assert!(cached_type_node_ref.point().calculating());
                    cached_type_node_ref.set_point(Point::new_uncalculated());
                    if let Some(ArgOrComprehension::Arg(Argument::Positional(arg))) =
                        args.details.iter().next()
                        && arg.expression().is_none_literal()
                    {
                        return Ok(Lookup::T(TypeContent::Type(Type::Type(Arc::new(
                            Type::None,
                        )))));
                    }
                    return Ok(Lookup::T(TypeContent::InvalidVariable(
                        InvalidVariableType::Variable(NodeRef::new(self.file, name_def.index())),
                    )));
                }
                SpecialAssignmentKind::Defaultdict => {
                    debug_assert!(cached_type_node_ref.point().calculating());
                    cached_type_node_ref.set_point(Point::new_uncalculated());
                    return Ok(Lookup::T(TypeContent::InvalidVariable(
                        InvalidVariableType::Variable(NodeRef::new(self.file, name_def.index())),
                    )));
                }
            };
            inf.save_redirect(self.i_s, self.file, name_def.index());
            // Since this sets the name def, we need to imitate the inference, which sets the name
            // def as well. (see Inference::cache_assignment)
            debug_assert!(!self.file.points.get(assignment.index()).calculated());
            self.file.points.set(
                assignment.index(),
                Point::new_specific(Specific::Analyzed, Locality::Todo),
            );
        };
        // In all cases we now have assigned to the name def and want to assign to the type cache
        // of the assignment to avoid checking this again and again.
        debug_assert!(
            !cached_type_node_ref.point().calculated(),
            "{cached_type_node_ref:?}"
        );
        cached_type_node_ref.set_point(Point::new_redirect(
            self.file.file_index,
            name_def.index(),
            Locality::Todo,
        ));
        Ok(self.compute_type_assignment_internal(assignment, AliasCause::Implicit))
    }

    pub(super) fn check_special_type_definition(node_ref: NodeRef) -> Option<Lookup> {
        Some(Lookup::T(match node_ref.maybe_complex()? {
            ComplexPoint::TypeVarLike(tv) => return Some(Lookup::TypeVarLike(tv.clone())),
            ComplexPoint::NamedTupleDefinition(t) => {
                let Type::NamedTuple(nt) = t.as_ref() else {
                    unreachable!()
                };
                TypeContent::NamedTuple(nt.clone())
            }
            ComplexPoint::TypedDictDefinition(tdd) => {
                let Type::TypedDict(td) = tdd.type_.as_ref() else {
                    unreachable!();
                };
                if td.calculating() {
                    debug_assert_eq!(node_ref.file_index(), td.defined_at.file);
                    TypeContent::RecursiveClass(ClassNodeRef::new(
                        node_ref.file,
                        td.defined_at.node_index,
                    ))
                } else {
                    TypeContent::TypedDictDefinition(td.clone())
                }
            }
            ComplexPoint::TypeInstance(Type::Type(t)) => match t.as_ref() {
                t @ Type::Enum(_) => TypeContent::Type(t.clone()),
                Type::None => TypeContent::Type(Type::None),
                _ => return None,
            },
            _ => return None,
        }))
    }

    pub(crate) fn compute_special_alias_assignment(
        &self,
        specific: Specific,
        assignment: Assignment,
    ) -> Inferred {
        debug_assert!(matches!(
            specific,
            Specific::TypingTypedDict | Specific::TypingNamedTuple | Specific::TypingNewType
        ));
        match self.compute_type_assignment(assignment) {
            Lookup::T(TypeContent::TypeAlias(ta)) => {
                if ta.is_valid() {
                    Inferred::from_type(Type::Type(Arc::new(ta.type_if_valid().clone())))
                } else {
                    Inferred::new_any_from_error()
                }
            }
            // Error should have been created, because it's an invalid alias.
            Lookup::T(TypeContent::InvalidVariable(_) | TypeContent::Unknown(_)) => {
                self.add_issue(
                    assignment.index(),
                    IssueKind::InvalidAssignmentForm {
                        class_name: match specific {
                            Specific::TypingTypedDict => "TypedDict",
                            Specific::TypingNamedTuple => "NamedTuple",
                            Specific::TypingNewType => "NewType",
                            _ => unreachable!(),
                        },
                    },
                );
                Inferred::new_any_from_error()
            }
            tnl => {
                recoverable_error!("Unexpected special type assignment result: {tnl:?}");
                Inferred::new_any_from_error()
            }
        }
    }

    fn maybe_special_assignment_execution<'x>(
        &self,
        expr: Expression<'x>,
    ) -> Result<SpecialAssignmentKind<'db, 'x>, CalculatingAliasType<'x>> {
        // For TypeVar, TypedDict, NewType and similar definitions
        let ExpressionContent::ExpressionPart(ExpressionPart::Primary(primary)) = expr.unpack()
        else {
            return Err(CalculatingAliasType::Normal);
        };
        let PrimaryContent::Execution(details) = primary.second() else {
            return Err(CalculatingAliasType::Normal);
        };
        match self.lookup_special_primary_or_atom_type(primary.first()) {
            Some(Lookup::T(TypeContent::SpecialCase(Specific::TypingTypeVarClass))) => Ok(
                SpecialAssignmentKind::TypeVar(ArgsContent::new(primary.index(), details)),
            ),
            Some(Lookup::T(TypeContent::SpecialCase(Specific::TypingTypeVarTupleClass))) => Ok(
                SpecialAssignmentKind::TypeVarTuple(ArgsContent::new(primary.index(), details)),
            ),
            Some(Lookup::T(TypeContent::SpecialCase(Specific::TypingParamSpecClass))) => Ok(
                SpecialAssignmentKind::ParamSpec(ArgsContent::new(primary.index(), details)),
            ),
            Some(Lookup::T(TypeContent::SpecialCase(Specific::TypingTypedDict))) => Err(
                CalculatingAliasType::TypedDict(ArgsContent::new(primary.index(), details)),
            ),
            Some(Lookup::T(TypeContent::SpecialCase(Specific::TypingNamedTuple))) => Err(
                CalculatingAliasType::NamedTuple(ArgsContent::new(primary.index(), details)),
            ),
            Some(Lookup::T(TypeContent::SpecialCase(Specific::TypingNewType))) => Err(
                CalculatingAliasType::NewType(ArgsContent::new(primary.index(), details)),
            ),
            Some(Lookup::T(TypeContent::SpecialCase(Specific::CollectionsNamedTuple))) => {
                Ok(SpecialAssignmentKind::CollectionsNamedTuple(
                    ArgsContent::new(primary.index(), details),
                ))
            }
            Some(Lookup::T(TypeContent::SpecialCase(Specific::BuiltinsType))) => Ok(
                SpecialAssignmentKind::TypeOf(ArgsContent::new(primary.index(), details)),
            ),
            Some(Lookup::T(TypeContent::Class { node_ref, .. }))
                if node_ref.use_cached_class_infos(self.i_s.db).kind == ClassKind::Enum =>
            {
                Ok({
                    let class = Class::with_self_generics(self.i_s.db, node_ref);
                    SpecialAssignmentKind::Enum(class, ArgsContent::new(primary.index(), details))
                })
            }
            Some(Lookup::T(TypeContent::Class { node_ref, .. }))
                if node_ref.as_link() == self.i_s.db.python_state.type_alias_type_link =>
            {
                Err(CalculatingAliasType::TypeAliasType(ArgsContent::new(
                    primary.index(),
                    details,
                )))
            }
            Some(Lookup::T(TypeContent::Class { node_ref, .. }))
                if node_ref.as_link() == self.i_s.db.python_state.defaultdict_link() =>
            {
                Ok(SpecialAssignmentKind::Defaultdict)
            }
            _ => Err(CalculatingAliasType::Normal),
        }
    }

    pub fn execute_type_alias_from_type_alias_type(
        &self,
        args: &dyn Args,
        assignment: Assignment,
    ) -> Option<Inferred> {
        // For X = TypeAliasType("X", int) assignments

        let Some(simple_args) = args.maybe_simple_args() else {
            debug!(
                "Found no simple args, but {args:?}, \
                   aborting TypeAliasType computation"
            );
            return None;
        };
        let cached_type_node_ref = assignment_type_node_ref(self.file, assignment);
        let Some((name_def, _, _)) = assignment.maybe_simple_type_expression_assignment() else {
            debug!(
                "Expected a simple assignment, but found {}, \
                   aborting TypeAliasType computation",
                assignment.as_code()
            );
            return None;
        };
        self.type_alias_from_type_alias_type(cached_type_node_ref, name_def, simple_args.details)?;
        Some(Inferred::from_type(
            self.i_s.db.python_state.type_alias_type_type(),
        ))
    }

    fn type_alias_from_type_alias_type(
        &self,
        cached_type_node_ref: NodeRef<'file>,
        name_def: NameDef,
        args: ArgumentsDetails,
    ) -> Option<Lookup<'file, 'file>> {
        // For `X = TypeAliasType('X', int)`. Errors return None and are checked by the type
        // checker in the normal way.
        let mut name = None;
        let mut value = None;
        let mut type_params = self.i_s.db.python_state.empty_type_var_likes.clone();
        for arg in args.iter() {
            match arg {
                ArgOrComprehension::Arg(Argument::Positional(n)) => {
                    if name.is_none() {
                        name = Some(n.expression());
                    } else if value.is_none() {
                        value = Some(n.expression());
                    } else {
                        debug!("Found an additional argument, aborting TypeAliasType computation");
                        return None;
                    }
                }
                ArgOrComprehension::Arg(Argument::Keyword(kw)) => {
                    let (key, val) = kw.unpack();
                    match key.as_code() {
                        "name" if name.is_none() => name = Some(val),
                        "value" if value.is_none() => value = Some(val),
                        "type_params" => {
                            let Some(tuple) = val.maybe_tuple() else {
                                self.add_type_issue(
                                    val.index(),
                                    IssueKind::TypeAliasTypeTypeParamsShouldBeTuple,
                                );
                                return None;
                            };
                            let mut type_var_manager = TypeVarManager::<PointLink>::default();
                            for entry in tuple.iter() {
                                match entry {
                                    parsa_python_cst::StarLikeExpression::NamedExpression(n) => {
                                        match self.lookup_type_expr_if_only_names(n.expression()) {
                                            Some(Lookup::TypeVarLike(tvl)) => {
                                                if type_var_manager.position(&tvl).is_some() {
                                                    self.add_type_issue(
                                                        n.index(),
                                                        IssueKind::DuplicateTypeVarInTypeAliasType {
                                                            name: tvl.name(self.i_s.db).into()
                                                        }
                                                    );
                                                } else if matches!(
                                                    tvl,
                                                    TypeVarLike::TypeVarTuple(_)
                                                ) && type_var_manager
                                                    .first_type_var_tuple()
                                                    .is_some()
                                                {
                                                    self.add_type_issue(
                                                        n.index(),
                                                        IssueKind::MultipleTypeVarTupleDisallowedInTypeParams {
                                                            in_type_alias_type: true,
                                                        }
                                                    );
                                                } else {
                                                    type_var_manager.add(
                                                        tvl,
                                                        None,
                                                        Some(n.index()),
                                                    );
                                                }
                                            }
                                            _ => {
                                                let c = n.as_code();
                                                self.add_type_issue(
                                                    n.index(),
                                                    IssueKind::FreeTypeVariableExpectInTypeAliasTypeTypeParams {
                                                    // TODO this is very imprecise
                                                    is_unpack: c.starts_with("Unpack[")
                                                    || c.starts_with("typing.Unpack[")
                                                });
                                            }
                                        };
                                    }
                                    parsa_python_cst::StarLikeExpression::StarNamedExpression(
                                        s,
                                    ) => {
                                        self.add_type_issue(
                                            s.index(),
                                            IssueKind::StarredExpressionOnlyNoTarget,
                                        );
                                    }
                                    _ => unreachable!(),
                                }
                            }
                            type_params = type_var_manager.into_type_vars();
                        }
                        key => {
                            debug!(
                                "Found an additional keyword \"{key}\" argument, \
                                    aborting TypeAliasType computation"
                            );
                            return None;
                        }
                    }
                }
                _ => {
                    debug!("Found a special keyword argument, aborting TypeAliasType computation");
                    return None;
                }
            }
        }
        if name.is_none() || value.is_none() {
            debug!("Missing a name or value, aborting TypeAliasType computation");
        }
        let name = name?;
        let value = value?;

        match name.maybe_single_string_literal() {
            Some(py_string) => {
                if name_def.as_code() != py_string.content() {
                    self.add_issue(
                        name.index(),
                        IssueKind::VarNameMismatch {
                            class_name: "TypeAliasType".into(),
                            string_name: Box::from(py_string.content()),
                            variable_name: Box::from(name_def.as_code()),
                        },
                    );
                }
            }
            None => {
                self.add_type_issue(
                    name.index(),
                    IssueKind::ArgumentIssue(Box::from(
                        "Argument 1 to TypeAliasType(...) must be a string literal",
                    )),
                );
            }
        };

        Some(self.check_for_alias_second_step(
            CalculatingAliasType::Normal,
            cached_type_node_ref,
            name_def,
            type_params,
            value,
            AliasCause::SyntaxOrTypeAliasType,
        ))
    }

    fn check_for_alias(
        &self,
        origin: CalculatingAliasType,
        cached_type_node_ref: NodeRef<'file>,
        name_def: NameDef,
        expr: Expression,
        cause: AliasCause,
    ) -> Lookup<'file, 'file> {
        // Here we avoid all late bound type var calculation for callable, which is how
        // mypy works. The default behavior without a type_var_callback would be to
        // just calculate all late bound type vars, but that would mean that something
        // like `Foo = Callable[[T], T]` could not be used like `Foo[int]`, which is
        // generally how type aliases work.
        let type_var_likes = match &origin {
            CalculatingAliasType::Normal => {
                TypeVarFinder::find_alias_type_vars(self.i_s, self.file, expr)
            }
            CalculatingAliasType::TypedDict(args) | CalculatingAliasType::NamedTuple(args) => {
                TypeVarFinder::find_named_tuple_or_typed_dict_assignment_type_vars(
                    self.i_s,
                    self.file,
                    args.details,
                )
            }
            CalculatingAliasType::NewType(_) => {
                self.i_s.db.python_state.empty_type_var_likes.clone()
            }
            CalculatingAliasType::TypeAliasType(args) => {
                return self
                    .type_alias_from_type_alias_type(cached_type_node_ref, name_def, args.details)
                    .unwrap_or_else(|| {
                        Lookup::T(TypeContent::InvalidVariable(InvalidVariableType::Variable(
                            NodeRef::new(self.file, name_def.index()),
                        )))
                    });
            }
        };
        self.check_for_alias_second_step(
            origin,
            cached_type_node_ref,
            name_def,
            type_var_likes,
            expr,
            cause,
        )
    }

    fn check_for_alias_second_step(
        &self,
        origin: CalculatingAliasType,
        cached_type_node_ref: NodeRef<'file>,
        name_def: NameDef,
        type_var_likes: TypeVarLikes,
        expr: Expression,
        cause: AliasCause,
    ) -> Lookup<'file, 'file> {
        let in_definition = cached_type_node_ref.as_link();
        let alias = TypeAlias::new(
            type_var_likes,
            in_definition,
            PointLink::new(self.file.file_index, name_def.name().index()),
            matches!(cause, AliasCause::SyntaxOrTypeAliasType),
        );
        save_alias(cached_type_node_ref, alias);
        let ComplexPoint::TypeAlias(alias) = cached_type_node_ref.maybe_complex().unwrap() else {
            unreachable!()
        };

        #[allow(clippy::mutable_key_type)]
        let mut unbound_type_vars = FastHashSet::default();
        let mut type_var_callback =
            |i_s: &InferenceState, _: &_, type_var_like: TypeVarLike, _, _: Name| {
                if let Some(result) = i_s.find_parent_type_var(&type_var_like) {
                    if let TypeVarCallbackReturn::TypeVarLike(_) = &result
                        && matches!(origin, CalculatingAliasType::Normal)
                        && (!matches!(cause, AliasCause::SyntaxOrTypeAliasType)
                            || i_s.db.mypy_compatible())
                    {
                        return TypeVarCallbackReturn::AddIssue(IssueKind::BoundTypeVarInAlias {
                            name: Box::from(type_var_like.name(i_s.db)),
                        });
                    }
                    return result;
                }
                if let Some(usage) = alias.type_vars.find(&type_var_like, alias.location) {
                    TypeVarCallbackReturn::TypeVarLike(usage)
                } else if let CalculatingAliasType::NewType(_) = &origin {
                    TypeVarCallbackReturn::UnboundTypeVar
                } else if matches!(cause, AliasCause::SyntaxOrTypeAliasType) {
                    unbound_type_vars.insert(type_var_like);
                    TypeVarCallbackReturn::AnyDueToError
                } else {
                    TypeVarCallbackReturn::NotFound {
                        allow_late_bound_callables: false,
                    }
                }
            };
        let p = self.file.points.get(expr.index());
        let mut comp = TypeComputation::new(
            self.i_s,
            self.file,
            in_definition,
            &mut type_var_callback,
            match &origin {
                CalculatingAliasType::Normal => TypeComputationOrigin::TypeAlias,
                CalculatingAliasType::TypedDict { .. } => TypeComputationOrigin::TypedDictMember,
                CalculatingAliasType::NamedTuple(_) => TypeComputationOrigin::NamedTupleMember,
                CalculatingAliasType::NewType(_) => TypeComputationOrigin::Other,
                CalculatingAliasType::TypeAliasType(_) => unreachable!(), // Remapped previously
            },
        );
        match &origin {
            CalculatingAliasType::Normal => {
                comp.errors_already_calculated = p.calculated();
                let tc = comp.compute_type(expr);
                let node_ref = NodeRef::new(self.file, expr.index());
                match tc {
                    TypeContent::InvalidVariable(_)
                    | TypeContent::Unknown(UnknownCause::UnknownName(_))
                        if matches!(cause, AliasCause::Implicit) =>
                    {
                        alias.set_invalid();
                    }
                    _ => {
                        let is_annotated = matches!(tc, TypeContent::Annotated(_));
                        let type_ = comp.as_type(tc, node_ref);
                        let is_recursive_alias = comp.is_recursive_alias;
                        let mut had_error = false;
                        if is_recursive_alias && self.i_s.current_function().is_some() {
                            node_ref.add_issue(
                                self.i_s,
                                IssueKind::RecursiveTypesNotAllowedInFunctionScope {
                                    alias_name: name_def.as_code().into(),
                                },
                            );
                            had_error = true;
                        }
                        if is_invalid_recursive_alias(
                            self.i_s.db,
                            &SeenRecursiveAliases::new(in_definition),
                            &type_,
                        ) {
                            node_ref.add_issue(
                                self.i_s,
                                IssueKind::InvalidRecursiveTypeAliasUnionOfItself {
                                    target: "union",
                                },
                            );
                            had_error = true;
                        }
                        // This is called detect_diverging_alias in Mypy as well.
                        if detect_diverging_alias(self.i_s.db, &alias.type_vars, &type_) {
                            node_ref.add_issue(
                                self.i_s,
                                IssueKind::InvalidRecursiveTypeAliasTypeVarNesting,
                            );
                            had_error = true;
                        }
                        if had_error {
                            alias.set_valid(Type::ERROR, false, is_annotated);
                        } else {
                            alias.set_valid(type_, is_recursive_alias, is_annotated);
                        }
                        if is_recursive_alias {
                            // Since the type aliases are not finished at the time of the type
                            // calculation, we need to recheck for Type[Type[...]]. It is however
                            // very important that this happens after setting the alias, otherwise
                            // something like X = Type[X] is not recognized.
                            check_for_and_replace_type_type_in_finished_alias(
                                self.i_s,
                                cached_type_node_ref,
                                alias,
                            );
                        }
                    }
                };
                if matches!(cause, AliasCause::SyntaxOrTypeAliasType) {
                    for type_var_like in unbound_type_vars.into_iter() {
                        node_ref.add_type_issue(
                            self.i_s.db,
                            IssueKind::TypeParametersShouldBeDeclared { type_var_like },
                        );
                    }
                }
            }
            CalculatingAliasType::TypedDict(args) => {
                match new_typed_dict_with_execution_syntax(
                    self.i_s,
                    &mut comp,
                    &SimpleArgs::new(*self.i_s, self.file, args.primary_index, args.details),
                ) {
                    Some((name, members)) => {
                        alias.set_valid(
                            Type::TypedDict(TypedDict::new_definition(
                                name,
                                members,
                                alias.location,
                                alias.type_vars.clone(),
                            )),
                            comp.is_recursive_alias,
                            false,
                        );
                    }
                    None => alias.set_valid(Type::ERROR, false, false),
                }
            }
            CalculatingAliasType::NamedTuple(args) => {
                match new_typing_named_tuple_internal(
                    self.i_s,
                    &mut comp,
                    &SimpleArgs::new(*self.i_s, self.file, args.primary_index, args.details),
                ) {
                    Some((name, params)) => {
                        alias.set_valid(
                            Type::NamedTuple(NamedTuple::from_params(
                                alias.location,
                                name,
                                alias.type_vars.clone(),
                                params,
                            )),
                            comp.is_recursive_alias,
                            false,
                        );
                    }
                    None => alias.set_valid(Type::ERROR, false, false),
                }
            }
            CalculatingAliasType::NewType(a) => match comp.compute_new_type_assignment(
                &SimpleArgs::new(*self.i_s, self.file, a.primary_index, a.details),
            ) {
                Some(new_type) => {
                    alias.set_valid(
                        Type::NewType(Arc::new(new_type)),
                        comp.is_recursive_alias,
                        false,
                    );
                }
                None => alias.set_valid(Type::ERROR, false, false),
            },
            CalculatingAliasType::TypeAliasType(_) => unreachable!(), // Remapped previously
        };
        debug!(
            "Alias {}={} on #{} is valid? {}",
            name_def.as_code(),
            expr.as_code(),
            NodeRef::new(self.file, expr.index()).line_one_based(self.i_s.db),
            alias.is_valid()
        );
        load_cached_type(cached_type_node_ref)
    }

    pub(crate) fn compute_explicit_type_assignment(&self, assignment: Assignment) -> Inferred {
        let name_lookup =
            self.compute_type_assignment_internal(assignment, AliasCause::TypingTypeAlias);
        if matches!(
            name_lookup,
            Lookup::T(TypeContent::Unknown(_) | TypeContent::InvalidVariable(_))
        ) {
            return Inferred::new_any(AnyCause::FromError);
        }
        Inferred::from_saved_node_ref(assignment_type_node_ref(self.file, assignment))
    }

    pub(super) fn compute_type_alias_syntax(
        &self,
        type_alias: parsa_python_cst::TypeAlias,
    ) -> Lookup<'file, 'file> {
        if self.i_s.current_function().is_some() && !self.i_s.db.mypy_compatible() {
            self.add_issue(type_alias.index(), IssueKind::TypeAliasSyntaxInFunction);
        }
        let (name_def, type_params, expr) = type_alias.unpack();
        let alias_type_ref = type_alias_type_node_ref(self.file, type_alias);
        if alias_type_ref.point().calculated() {
            return load_cached_type(alias_type_ref);
        }
        let scope = self.i_s.as_parent_scope();
        let type_var_likes = if let Some(type_params) = type_params {
            self.compute_type_params_definition(scope, type_params, false)
        } else {
            self.i_s.db.python_state.empty_type_var_likes.clone()
        };
        self.check_for_alias_second_step(
            CalculatingAliasType::Normal,
            alias_type_ref,
            name_def,
            type_var_likes,
            expr,
            AliasCause::SyntaxOrTypeAliasType,
        )
    }

    pub fn ensure_compute_type_alias_from_syntax(&self, type_alias: parsa_python_cst::TypeAlias) {
        self.compute_type_alias_syntax(type_alias);
    }

    // ------------------------------------------------------------------------
    // Here comes the class precalculation
    // ------------------------------------------------------------------------

    fn pre_calc_classes_in_slice_like(&self, slice_like: SliceOrSimple) {
        match slice_like {
            SliceOrSimple::Simple(s) => self.pre_calc_classes_in_expr(s.named_expr.expression()),
            SliceOrSimple::Slice(_) => (),
            SliceOrSimple::Starred(starred) => {
                self.pre_calc_classes_in_expr(starred.starred_expr.expression())
            }
        };
    }

    fn pre_calc_classes_in_expr(&self, expr: Expression) {
        if let ExpressionContent::ExpressionPart(n) = expr.unpack() {
            self.pre_calc_classes_in_expression_part(n);
        }
    }

    fn pre_calc_classes_point_resolution(
        &self,
        pr: PointResolution<'file>,
    ) -> PreClassCalculationLookup<'file> {
        match pr {
            PointResolution::NameDef { node_ref, .. } => {
                let name_def = node_ref.expect_name_def();
                match name_def.expect_type() {
                    TypeLike::ClassDef(class_def) => {
                        let class_node_ref = ClassNodeRef::new(node_ref.file, class_def.index());
                        cache_class_name(node_ref, class_def);
                        class_node_ref.ensure_cached_class_infos(&InferenceState::new(
                            self.i_s.db,
                            node_ref.file,
                        ));
                        return PreClassCalculationLookup::Class(class_node_ref);
                    }
                    TypeLike::ImportFromAsName(_) => {
                        // TODO this is probably not a good idea to match this by string
                        if name_def.as_code() == "Literal" {
                            return PreClassCalculationLookup::Literal;
                        }
                    }
                    _ => (),
                }
            }
            PointResolution::Inferred(inferred) => {
                if let Some(Specific::TypingLiteral) = inferred.maybe_saved_specific(self.i_s.db) {
                    return PreClassCalculationLookup::Literal;
                } else if let Some(ComplexPoint::Class(_)) =
                    inferred.maybe_complex_point(self.i_s.db)
                {
                    let cls = ClassNodeRef::from_node_ref(
                        inferred.maybe_saved_node_ref(self.i_s.db).unwrap(),
                    );
                    return PreClassCalculationLookup::Class(cls);
                }
                if let Some(f) = inferred.maybe_file(self.i_s.db) {
                    return PreClassCalculationLookup::Module(self.i_s.db.loaded_python_file(f));
                }
            }
            _ => (),
        }
        PreClassCalculationLookup::Other
    }

    fn pre_calc_classes_in_expression_part(&self, node: ExpressionPart) {
        match node {
            ExpressionPart::Atom(atom) => {
                self.pre_calc_classes_in_atom(atom);
            }
            ExpressionPart::Primary(primary) => {
                self.pre_calc_classes_in_primary(primary);
            }
            ExpressionPart::BitwiseOr(bitwise_or) => {
                let (a, b) = bitwise_or.unpack();
                self.pre_calc_classes_in_expression_part(a);
                self.pre_calc_classes_in_expression_part(b);
            }
            _ => (),
        }
    }

    fn pre_calc_classes_in_atom(&self, atom: Atom) -> PreClassCalculationLookup<'file> {
        let compute_forward_reference = |start, string: Cow<str>| {
            let file = self
                .file
                .ensure_forward_reference_file(self.i_s.db, start, string);

            let Some(star_exprs) = file.tree.maybe_star_expressions() else {
                return;
            };
            let StarExpressionContent::Expression(expr) = star_exprs.unpack() else {
                return;
            };
            file.name_resolution_for_types(self.i_s)
                .pre_calc_classes_in_expr(expr);
        };
        match atom.unpack() {
            AtomContent::Name(n) => {
                return self
                    .pre_calc_classes_point_resolution(self.resolve_name_without_narrowing(n));
            }
            AtomContent::Strings(s_o_b) => match s_o_b.as_python_string() {
                PythonString::Ref(start, s) => compute_forward_reference(start, Cow::Borrowed(s)),
                PythonString::String(start, s) => compute_forward_reference(start, Cow::Owned(s)),
                PythonString::FString => (),
            },
            _ => (),
        }
        PreClassCalculationLookup::Other
    }

    fn pre_calc_classes_in_primary(&self, primary: Primary) -> PreClassCalculationLookup<'file> {
        let base = match primary.first() {
            PrimaryOrAtom::Primary(primary) => self.pre_calc_classes_in_primary(primary),
            PrimaryOrAtom::Atom(atom) => self.pre_calc_classes_in_atom(atom),
        };
        match primary.second() {
            PrimaryContent::Attribute(name) => {
                return match base {
                    PreClassCalculationLookup::Module(f) => {
                        if let Some((resolved, _)) = f
                            .name_resolution_for_types(&InferenceState::new(self.i_s.db, f))
                            .resolve_module_access(name.as_str(), |k| {
                                self.add_issue(name.index(), k)
                            })
                        {
                            return self.pre_calc_classes_point_resolution(resolved);
                        }
                        PreClassCalculationLookup::Other
                    }
                    PreClassCalculationLookup::Class(_) => {
                        // TODO we would need to do class lookups
                        PreClassCalculationLookup::Other
                    }
                    _ => PreClassCalculationLookup::Other,
                };
            }
            PrimaryContent::Execution(_) => (),
            PrimaryContent::GetItem(slice_type) => {
                let s = SliceType::new(self.file, primary.index(), slice_type);
                match base {
                    PreClassCalculationLookup::Literal => (), // Literals can never contain type vars
                    _ => {
                        for slice_like in s.iter() {
                            self.pre_calc_classes_in_slice_like(slice_like)
                        }
                    }
                }
            }
        }
        PreClassCalculationLookup::Other
    }
}

#[derive(Debug)]
enum PreClassCalculationLookup<'file> {
    Module(&'file PythonFile),
    #[expect(dead_code)]
    Class(ClassNodeRef<'file>),
    Literal,
    Other,
}

fn load_cached_type(node_ref: NodeRef) -> Lookup {
    let p = node_ref.point();
    if p.kind() == PointKind::Redirect {
        debug_assert_eq!(p.file_index(), node_ref.file_index());
        // Some special assignments like TypeVars are defined on names, because they can also be
        // inferred.
        /*
        return self.point_resolution_to_type_name_lookup(
            self.resolve_point_without_narrowing(p.node_index())
                .unwrap(),
        );
        */
        let redirected_to = NodeRef::new(node_ref.file, p.node_index());
        if let Some(specific) = redirected_to.point().maybe_specific() {
            debug_assert!(
                matches!(
                    specific,
                    Specific::InvalidTypeDefinition | Specific::AnyDueToError
                ),
                "{specific:?}",
            );
            return Lookup::UNKNOWN_REPORTED;
        } else {
            if redirected_to.point().kind() == PointKind::Redirect {
                return load_cached_type(redirected_to);
            }
            return NameResolution::check_special_type_definition(redirected_to).unwrap_or_else(
                || Lookup::T(TypeContent::InvalidVariable(InvalidVariableType::Other)),
            );
        }
    }
    match node_ref.maybe_complex() {
        Some(ComplexPoint::TypeAlias(a)) => {
            if a.calculating() {
                debug!("Found a recursive type on alias");
                // This means it's a recursive type definition.
                Lookup::T(TypeContent::RecursiveAlias(node_ref.as_link()))
            } else if !a.is_valid() {
                let assignment = NodeRef::new(
                    node_ref.file,
                    node_ref.node_index - ASSIGNMENT_TYPE_CACHE_OFFSET,
                )
                .expect_assignment();
                let name_def = assignment
                    .maybe_simple_type_expression_assignment()
                    .unwrap()
                    .0;
                debug!("Found invalid type alias: {}", name_def.as_code());
                Lookup::T(TypeContent::InvalidVariable(InvalidVariableType::Variable(
                    NodeRef::new(node_ref.file, name_def.index()),
                )))
            } else {
                Lookup::T(TypeContent::TypeAlias(a))
            }
        }
        None => {
            debug_assert_eq!(node_ref.point().specific(), Specific::AnyDueToError);
            Lookup::UNKNOWN_REPORTED
        }
        Some(ComplexPoint::TypeInstance(_)) => {
            // This can happen for defaultdicts, which are NOT valid types
            Lookup::T(TypeContent::InvalidVariable(InvalidVariableType::Variable(
                node_ref,
            )))
        }
        _ => {
            recoverable_error!("Expected an Alias or TypeVarLike, but received something weird");
            Lookup::UNKNOWN_REPORTED
        }
    }
}

pub fn assignment_type_node_ref<'x>(file: &'x PythonFile, assignment: Assignment) -> NodeRef<'x> {
    NodeRef::new(file, assignment.index() + ASSIGNMENT_TYPE_CACHE_OFFSET)
}

fn type_alias_type_node_ref<'x>(
    file: &'x PythonFile,
    type_alias: parsa_python_cst::TypeAlias,
) -> NodeRef<'x> {
    NodeRef::new(file, type_alias.index() + ALIAS_TYPE_CACHE_OFFSET)
}

fn detect_diverging_alias(db: &Database, type_var_likes: &TypeVarLikes, t: &Type) -> bool {
    !type_var_likes.is_empty()
        && t.find_in_type(db, &mut |t| match t {
            Type::RecursiveType(rec) if rec.has_alias_origin(db) && rec.generics.is_some() => {
                rec.generics.as_ref().is_some_and(|generics| {
                    let has_direct_type_var_like = generics.iter().any(|g| match g {
                        GenericItem::TypeArg(t) => matches!(t, Type::TypeVar(_)),
                        GenericItem::TypeArgs(ts) => match &ts.args {
                            TupleArgs::WithUnpack(w) => {
                                matches!(w.unpack, TupleUnpack::TypeVarTuple(_))
                            }
                            _ => false,
                        },
                        GenericItem::ParamSpecArg(p) => p.params.maybe_param_spec().is_some(),
                    });
                    !has_direct_type_var_like && generics.has_type_vars()
                })
            }
            _ => false,
        })
}

type SeenRecursiveAliases<'a> = AlreadySeen<'a, PointLink>;

fn is_invalid_recursive_alias(db: &Database, seen: &SeenRecursiveAliases, t: &Type) -> bool {
    t.iter_with_unpacked_unions_without_unpacking_recursive_types()
        .any(|t| {
            if let Type::RecursiveType(rec) = t
                && rec.has_alias_origin(db)
            {
                let new_seen = seen.append(rec.link);
                return if let Some(t) = rec.calculated_type_if_ready(db) {
                    is_invalid_recursive_alias(db, &new_seen, t)
                } else {
                    new_seen.is_cycle()
                };
            }
            false
        })
}

#[derive(Debug)]
enum CalculatingAliasType<'tree> {
    Normal,
    TypedDict(ArgsContent<'tree>),
    NamedTuple(ArgsContent<'tree>),
    NewType(ArgsContent<'tree>),
    TypeAliasType(ArgsContent<'tree>), // e.g. X = TypeAliasType('X', int)
}

#[derive(Copy, Clone)]
enum AliasCause {
    TypingTypeAlias, // `X: typing.TypeAlias = int`
    Implicit,
    SyntaxOrTypeAliasType, // `type X = int` or `X = TypeAliasType('X', int)`
}

#[derive(Debug)]
enum SpecialAssignmentKind<'db, 'tree> {
    Enum(Class<'db>, ArgsContent<'tree>),
    CollectionsNamedTuple(ArgsContent<'tree>),
    TypeVar(ArgsContent<'tree>),
    TypeVarTuple(ArgsContent<'tree>),
    ParamSpec(ArgsContent<'tree>),
    TypeOf(ArgsContent<'tree>), // e.g. void = type(None)
    Defaultdict, // This is handled in inference but we need to make sure to not overwrite it
}

#[derive(Debug)]
struct ArgsContent<'tree> {
    primary_index: NodeIndex,
    details: ArgumentsDetails<'tree>,
}

impl<'x> ArgsContent<'x> {
    fn new(primary_index: NodeIndex, details: ArgumentsDetails<'x>) -> Self {
        Self {
            primary_index,
            details,
        }
    }
}

fn check_for_and_replace_type_type_in_finished_alias(
    i_s: &InferenceState,
    alias_origin: NodeRef,
    alias: &TypeAlias,
) {
    // TODO this is not complete now. This only properly checks aliases that are self-recursive.
    // Something like:
    //
    //     A = Type[B]
    //     B = List[Type[A]]
    //
    //  will probably just be ignored and should need additional logic to be recognized.
    //  see also the test type_type_alias_circular
    if alias
        .type_if_valid()
        .find_in_type(i_s.db, &mut |t| match t {
            Type::Type(t) => {
                t.iter_with_unpacked_unions_without_unpacking_recursive_types()
                    .any(|t| match t {
                        Type::RecursiveType(recursive_alias) => recursive_alias
                            .has_alias_origin(i_s.db)
                            && recursive_alias
                                .calculated_type_if_ready(i_s.db)
                                .is_some_and(|t| {
                                    t.iter_with_unpacked_unions_without_unpacking_recursive_types()
                                        .any(|t| matches!(t, Type::Type(_)))
                                }),
                        _ => false,
                    })
            }
            _ => false,
        })
    {
        alias_origin.add_issue(i_s, IssueKind::CannotContainType { name: "type" });
        let alias = TypeAlias::new(
            alias.type_vars.clone(),
            alias.location,
            alias.name,
            alias.from_type_syntax,
        );
        alias.set_valid(Type::ERROR, false, false);
        save_alias(alias_origin, alias)
    }
}

fn save_alias(alias_origin: NodeRef, alias: TypeAlias) {
    let complex = ComplexPoint::TypeAlias(Box::new(alias));
    alias_origin.insert_complex(complex, Locality::Todo);
}
