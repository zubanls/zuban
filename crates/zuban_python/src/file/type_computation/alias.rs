use std::rc::Rc;

use parsa_python_cst::{
    Argument, ArgumentsDetails, Assignment, AssignmentContent, Expression, ExpressionContent,
    ExpressionPart, NameDef, NameOrPrimaryWithNames, NodeIndex, PrimaryContent, Target,
};

use super::{
    super::name_resolution::NameResolution, InvalidVariableType, Lookup, TypeContent,
    TypeVarFinder, UnknownCause,
};
use crate::{
    arguments::SimpleArgs,
    database::{
        ClassKind, ComplexPoint, Database, Locality, Point, PointKind, PointLink, Specific,
        TypeAlias,
    },
    debug,
    diagnostics::IssueKind,
    file::{
        type_computation::{
            named_tuple::new_typing_named_tuple_internal,
            typed_dict::new_typed_dict_with_execution_syntax, TypeCommentState,
        },
        PythonFile, TypeComputation, TypeComputationOrigin, TypeVarCallbackReturn,
    },
    inference_state::InferenceState,
    inferred::Inferred,
    node_ref::NodeRef,
    recoverable_error,
    type_::{
        AnyCause, GenericItem, NamedTuple, TupleArgs, TupleUnpack, Type, TypeVarLike, TypeVarLikes,
        TypedDict,
    },
    type_helpers::Class,
    utils::{debug_indent, AlreadySeen},
};

const ASSIGNMENT_TYPE_CACHE_OFFSET: u32 = 1;

impl<'db, 'file> NameResolution<'db, 'file, '_> {
    pub(super) fn compute_type_assignment(&self, assignment: Assignment) -> Lookup<'file, 'file> {
        let is_explicit = match assignment.maybe_annotation() {
            Some(annotation) => {
                self.ensure_cached_annotation(annotation, true);
                self.file.points.get(annotation.index()).maybe_specific()
                    == Some(Specific::AnnotationTypeAlias)
            }
            None => false,
        };
        self.compute_type_assignment_internal(assignment, is_explicit)
    }

    fn compute_type_assignment_internal(
        &self,
        assignment: Assignment,
        is_explicit: bool,
    ) -> Lookup<'file, 'file> {
        // Use the node star_targets or single_target, because they are not used otherwise.
        let file = self.file;
        let cached_type_node_ref = assignment_type_node_ref(file, assignment);
        let point = cached_type_node_ref.point();
        if point.calculated() {
            return load_cached_type(cached_type_node_ref);
        }

        if !is_explicit {
            // Only non-explicit TypeAliases are allowed here.
            if let Some(name_or_prim) = assignment.maybe_simple_type_reassignment() {
                // For very simple cases like `Foo = int`. Not sure yet if this going to stay.
                debug!(
                    "Found alias that could maybe just be redirected: {}",
                    assignment.as_code()
                );
                let lookup = debug_indent(|| match name_or_prim {
                    NameOrPrimaryWithNames::Name(name) => Some(self.lookup_type_name(name)),
                    NameOrPrimaryWithNames::PrimaryWithNames(primary) => {
                        self.lookup_primary_names(primary)
                    }
                });
                match lookup {
                    Some(Lookup::T(TypeContent::SpecialCase(Specific::TypingAny))) => {
                        // This is a bit of a weird special case that was necessary to pass the test
                        // testDisallowAnyExplicitAlias
                        if self.flags().disallow_any_explicit {
                            NodeRef::new(file, name_or_prim.index())
                                .add_issue(self.i_s, IssueKind::DisallowedAnyExplicit)
                        }
                    }
                    // It seems like Mypy is ignoring this?
                    Some(Lookup::T(TypeContent::SpecialCase(_))) => (),
                    Some(lookup) => {
                        debug!("Alias can be redirected: {lookup:?}");
                        return lookup;
                    }
                    _ => {
                        debug!("Alias can not be redirected");
                    }
                }
            }
        }
        if let Some((name_def, annotation, expr)) =
            assignment.maybe_simple_type_expression_assignment()
        {
            debug!("Started type alias calculation: {}", name_def.as_code());
            if let Some(type_comment) = self.check_for_type_comment_internal(assignment, || {
                file.points
                    .get(name_def.index())
                    .maybe_calculated_and_specific()
                    == Some(Specific::Cycle)
            }) {
                // This case is a bit weird in Mypy, but it makes it possible to use a type
                // definition like:
                //
                //     Foo = 1  # type: Any
                if let TypeCommentState::Type(t) = &type_comment.type_ {
                    if let Type::Any(cause) = t.as_ref() {
                        return Lookup::T(TypeContent::Unknown(UnknownCause::AnyCause(*cause)));
                    }
                }
            }
            if !is_explicit
                && (expr.maybe_single_string_literal().is_some() || annotation.is_some())
            {
                return Lookup::T(TypeContent::InvalidVariable(InvalidVariableType::Variable(
                    NodeRef::new(file, name_def.index()),
                )));
            }

            let check_for_alias = |origin| {
                self.check_for_alias(origin, cached_type_node_ref, name_def, expr, is_explicit)
            };

            if is_explicit {
                return check_for_alias(CalculatingAliasType::Normal);
            }

            let result = self
                .compute_special_assignments(assignment, name_def, expr)
                .unwrap_or_else(|origin| check_for_alias(origin));
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
                if let Type::Any(cause) = self.use_cached_annotation_type(annotation).as_ref() {
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
        let special = self.maybe_special_assignment_execution(expr)?;
        // At this point we only take care of special assignments like TypeVars,
        // collection.namedtuple, etc.
        // This does not include NamedTuple, NewType and TypedDict executions, which are taken care
        // of in normal alias calculation, because they need access to type vars and can in general
        // create recursive types.
        if self.file.points.get(name_def.index()).calculated() {
            // The special assignment has been inferred with the normal inference and we simply set
            // the correct alias below.
            debug_assert!(self.file.points.get(assignment.index()).calculated());
        } else {
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
        let cached_type_node_ref = assignment_type_node_ref(self.file, assignment);
        debug_assert!(
            !cached_type_node_ref.point().calculated(),
            "{cached_type_node_ref:?}"
        );
        cached_type_node_ref.set_point(Point::new_redirect(
            self.file.file_index,
            name_def.index(),
            Locality::Todo,
        ));
        return Ok(self.compute_type_assignment_internal(assignment, false));
    }

    pub(super) fn check_special_type_definition(node_ref: NodeRef) -> Option<Lookup> {
        Some(Lookup::T(match node_ref.complex()? {
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
                TypeContent::TypedDictDefinition(td.clone())
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
                    Inferred::from_type(Type::Type(Rc::new(ta.type_if_valid().clone())))
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
            Some(Lookup::T(TypeContent::Class { node_ref, .. }))
                if node_ref.use_cached_class_infos(self.i_s.db).class_kind == ClassKind::Enum =>
            {
                Ok({
                    let class = Class::with_self_generics(self.i_s.db, node_ref);
                    SpecialAssignmentKind::Enum(class, ArgsContent::new(primary.index(), details))
                })
            }
            _ => Err(CalculatingAliasType::Normal),
        }
    }

    fn check_for_alias(
        &self,
        origin: CalculatingAliasType,
        cached_type_node_ref: NodeRef<'file>,
        name_def: NameDef,
        expr: Expression,
        is_explicit: bool,
    ) -> Lookup<'file, 'file> {
        cached_type_node_ref.set_point(Point::new_calculating());

        // Here we avoid all late bound type var calculation for callable, which is how
        // mypy works. The default behavior without a type_var_callback would be to
        // just calculate all late bound type vars, but that would mean that something
        // like `Foo = Callable[[T], T]` could not be used like `Foo[int]`, which is
        // generally how type aliases work.
        let find_type_var_likes = || match &origin {
            CalculatingAliasType::Normal => {
                TypeVarFinder::find_alias_type_vars(self.i_s, self.file, expr)
            }
            CalculatingAliasType::TypedDict(args)
            | CalculatingAliasType::NamedTuple(args)
            | CalculatingAliasType::NewType(args) => {
                if let ArgumentsDetails::Node(n) = args.details {
                    // Skip the name
                    if let Some(arg) = n.iter().nth(1) {
                        if let Argument::Positional(pos) = arg {
                            return TypeVarFinder::find_alias_type_vars(
                                self.i_s,
                                self.file,
                                pos.expression(),
                            );
                        }
                    }
                }
                self.i_s.db.python_state.empty_type_var_likes.clone()
            }
        };
        let type_var_likes = find_type_var_likes();

        let in_definition = cached_type_node_ref.as_link();
        let alias = TypeAlias::new(
            type_var_likes,
            in_definition,
            Some(PointLink::new(
                self.file.file_index,
                name_def.name().index(),
            )),
        );
        save_alias(cached_type_node_ref, alias);
        let ComplexPoint::TypeAlias(alias) = cached_type_node_ref.complex().unwrap() else {
            unreachable!()
        };

        let mut type_var_callback = |_: &InferenceState, _: &_, type_var_like: TypeVarLike, _| {
            if let Some(usage) = alias.type_vars.find(type_var_like, alias.location) {
                TypeVarCallbackReturn::TypeVarLike(usage)
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
            },
        );
        match origin {
            CalculatingAliasType::Normal => {
                comp.errors_already_calculated = p.calculated();
                let tc = comp.compute_type(expr);
                let node_ref = NodeRef::new(self.file, expr.index());
                match tc {
                    TypeContent::InvalidVariable(_)
                    | TypeContent::Unknown(UnknownCause::UnknownName(_))
                        if !is_explicit =>
                    {
                        alias.set_invalid();
                    }
                    _ => {
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
                            alias.set_valid(Type::ERROR, false);
                        } else {
                            alias.set_valid(type_, is_recursive_alias);
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
            }
            CalculatingAliasType::TypedDict(args) => {
                match new_typed_dict_with_execution_syntax(
                    self.i_s,
                    &mut comp,
                    &SimpleArgs::new(*self.i_s, self.file, args.primary_index, args.details),
                ) {
                    Some((name, members, _)) => {
                        alias.set_valid(
                            Type::TypedDict(TypedDict::new_definition(
                                name,
                                members,
                                alias.location,
                                alias.type_vars.clone(),
                            )),
                            comp.is_recursive_alias,
                        );
                    }
                    None => alias.set_valid(Type::ERROR, false),
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
                        );
                    }
                    None => alias.set_valid(Type::ERROR, false),
                }
            }
            CalculatingAliasType::NewType(a) => match comp.compute_new_type_assignment(
                &SimpleArgs::new(*self.i_s, self.file, a.primary_index, a.details),
            ) {
                Some(new_type) => {
                    alias.set_valid(Type::NewType(Rc::new(new_type)), comp.is_recursive_alias);
                }
                None => alias.set_valid(Type::ERROR, false),
            },
        };
        debug!(
            "Alias {}={} on #{} is valid? {}",
            name_def.as_code(),
            expr.as_code(),
            NodeRef::new(self.file, expr.index()).line(),
            alias.is_valid()
        );
        load_cached_type(cached_type_node_ref)
    }

    pub(crate) fn compute_explicit_type_assignment(&self, assignment: Assignment) -> Inferred {
        let name_lookup = self.compute_type_assignment_internal(assignment, true);
        if matches!(
            name_lookup,
            Lookup::T(TypeContent::Unknown(_) | TypeContent::InvalidVariable(_))
        ) {
            return Inferred::new_any(AnyCause::FromError);
        }
        Inferred::from_saved_node_ref(assignment_type_node_ref(self.file, assignment))
    }
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
            return NameResolution::check_special_type_definition(redirected_to)
                .unwrap_or_else(|| panic!("{redirected_to:?}"));
        }
    }
    match node_ref.complex().unwrap() {
        ComplexPoint::TypeAlias(a) => {
            if a.calculating() {
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
        _ => unreachable!("Expected an Alias or TypeVarLike, but received something weird"),
    }
}

fn assignment_type_node_ref<'x>(file: &'x PythonFile, assignment: Assignment) -> NodeRef<'x> {
    NodeRef::new(file, assignment.index() + ASSIGNMENT_TYPE_CACHE_OFFSET)
}

fn detect_diverging_alias(db: &Database, type_var_likes: &TypeVarLikes, t: &Type) -> bool {
    !type_var_likes.is_empty()
        && t.find_in_type(db, &mut |t| match t {
            Type::RecursiveType(rec) if rec.has_alias_origin(db) && rec.generics.is_some() => {
                if rec.calculating(db) {
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
                } else {
                    false
                }
            }
            _ => false,
        })
}

type SeenRecursiveAliases<'a> = AlreadySeen<'a, PointLink>;

fn is_invalid_recursive_alias(db: &Database, seen: &SeenRecursiveAliases, t: &Type) -> bool {
    t.iter_with_unpacked_unions_without_unpacking_recursive_types()
        .any(|t| {
            if let Type::RecursiveType(rec) = t {
                if rec.has_alias_origin(db) {
                    let new_seen = seen.append(rec.link);
                    return if rec.calculating(db) {
                        new_seen.is_cycle()
                    } else {
                        is_invalid_recursive_alias(db, &new_seen, rec.calculated_type(db))
                    };
                }
            }
            false
        })
}
enum CalculatingAliasType<'tree> {
    Normal,
    TypedDict(ArgsContent<'tree>),
    NamedTuple(ArgsContent<'tree>),
    NewType(ArgsContent<'tree>),
}

enum SpecialAssignmentKind<'db, 'tree> {
    Enum(Class<'db>, ArgsContent<'tree>),
    CollectionsNamedTuple(ArgsContent<'tree>),
    TypeVar(ArgsContent<'tree>),
    TypeVarTuple(ArgsContent<'tree>),
    ParamSpec(ArgsContent<'tree>),
}

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
            Type::Type(t) => t
                .iter_with_unpacked_unions_without_unpacking_recursive_types()
                .any(|t| match t {
                    Type::RecursiveType(recursive_alias) => {
                        !recursive_alias.calculating(i_s.db)
                            && recursive_alias.has_alias_origin(i_s.db)
                            && recursive_alias
                                .calculated_type(i_s.db)
                                .iter_with_unpacked_unions_without_unpacking_recursive_types()
                                .any(|t| matches!(t, Type::Type(_)))
                    }
                    _ => false,
                }),
            _ => false,
        })
    {
        alias_origin.add_issue(i_s, IssueKind::CannotContainType { name: "Type" });
        let alias = TypeAlias::new(alias.type_vars.clone(), alias.location, alias.name);
        alias.set_valid(Type::ERROR, false);
        save_alias(alias_origin, alias)
    }
}

fn save_alias(alias_origin: NodeRef, alias: TypeAlias) {
    let complex = ComplexPoint::TypeAlias(Box::new(alias));
    alias_origin.insert_complex(complex, Locality::Todo);
}
