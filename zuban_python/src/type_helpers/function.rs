use std::{borrow::Cow, cell::Cell, fmt, rc::Rc};

use parsa_python_cst::{
    BlockContent, Decorated, Decorator, ExpressionContent, ExpressionPart, FunctionDef,
    FunctionParent, NodeIndex, Param as CSTParam, ParamAnnotation, ParamIterator, ParamKind,
    PrimaryContent, PrimaryOrAtom, ReturnAnnotation, ReturnOrYield, SimpleStmt, SimpleStmtContent,
    StmtOrError,
};

use crate::{
    arguments::{Arg, Args, KnownArgs},
    database::{
        ComplexPoint, Database, Locality, OverloadDefinition, OverloadImplementation, Point,
        PointKind, PointLink, Specific,
    },
    debug,
    diagnostics::{Issue, IssueKind},
    file::{
        first_defined_name, first_defined_name_of_multi_def, use_cached_param_annotation_type,
        PythonFile, TypeComputation, TypeComputationOrigin, TypeVarCallbackReturn, FLOW_ANALYSIS,
    },
    format_data::FormatData,
    inference_state::InferenceState,
    inferred::Inferred,
    matching::{
        calculate_function_type_vars_and_return, maybe_class_usage,
        params::{InferrableParamIterator, Param, WrappedParamType, WrappedStar, WrappedStarStar},
        CalculatedTypeArgs, ErrorStrs, Generic, LookupResult, OnTypeError, ResultContext,
    },
    new_class,
    node_ref::NodeRef,
    python_state::NAME_TO_FUNCTION_DIFF,
    type_::{
        AnyCause, CallableContent, CallableLike, CallableParam, CallableParams, ClassGenerics,
        DbString, FunctionKind, FunctionOverload, GenericClass, GenericItem, ParamSpecUsage,
        ParamType, ReplaceSelf, StarParamType, StarStarParamType, StringSlice, TupleArgs, Type,
        TypeGuardInfo, TypeVar, TypeVarKind, TypeVarLike, TypeVarLikeUsage, TypeVarLikes,
        TypeVarManager, TypeVarName, TypeVarUsage, Variance, WrongPositionalCount,
    },
    type_helpers::Class,
    utils::{rc_slice_into_vec, rc_unwrap_or_clone},
};

#[derive(Clone, Copy)]
pub struct Function<'a, 'class> {
    pub node_ref: NodeRef<'a>,
    pub class: Option<Class<'class>>,
}

impl fmt::Debug for Function<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("Function")
            .field("file", self.node_ref.file)
            .field("node", &self.node())
            .field("class", &self.class)
            .finish()
    }
}

impl<'db: 'a + 'class, 'a, 'class> Function<'a, 'class> {
    // Functions use the following points:
    // - "def" to redirect to the first return/yield
    // - "function_def_parameters" to save calculated type vars
    // - "(" for decorator caching
    pub fn new(node_ref: NodeRef<'a>, class: Option<Class<'class>>) -> Self {
        if std::cfg!(debug_assertions) {
            debug_assert!(node_ref.maybe_function().is_some());
        }
        Self { node_ref, class }
    }

    pub fn node(&self) -> FunctionDef<'a> {
        FunctionDef::by_index(&self.node_ref.file.tree, self.node_ref.node_index)
    }

    pub fn return_annotation(&self) -> Option<ReturnAnnotation> {
        self.node().return_annotation()
    }

    pub fn expect_return_annotation_node_ref(&self) -> NodeRef {
        NodeRef::new(
            self.node_ref.file,
            self.return_annotation().unwrap().expression().index(),
        )
    }

    pub fn is_typed(&self) -> bool {
        self.node().is_typed()
    }

    pub fn generator_return(&self, i_s: &InferenceState) -> Option<GeneratorType> {
        self.return_annotation().and_then(|return_annotation| {
            let return_type = self
                .node_ref
                .file
                .inference(i_s)
                .use_cached_return_annotation_type(return_annotation);
            GeneratorType::from_type(i_s.db, return_type)
        })
    }

    fn iter_non_self_args(&self, i_s: &InferenceState) -> ParamIterator<'a> {
        let mut iterator = self.node().params().iter();
        if self.class.is_some() && self.kind() != FunctionKind::Staticmethod {
            // The param annotation is defined implicitly as Self or Type[Self]
            iterator.next();
        }
        iterator
    }

    pub fn is_missing_param_annotations(&self, i_s: &InferenceState) -> bool {
        self.iter_non_self_args(i_s)
            .any(|p| p.annotation().is_none())
    }

    pub fn might_be_missing_none_return_annotation(&self, i_s: &InferenceState) -> bool {
        self.iter_return_or_yield().next().is_none()
            && self.iter_non_self_args(i_s).next().is_none()
    }

    pub fn has_trivial_body(&self, i_s: &InferenceState) -> bool {
        // In Mypy this is called "is_trivial_body"
        let check_simple_stmt = |simple_stmt: Option<SimpleStmt>| {
            let Some(simple_stmt) = simple_stmt else {
                return false;
            };
            match simple_stmt.unpack() {
                SimpleStmtContent::PassStmt(_) => true,
                SimpleStmtContent::StarExpressions(star_exprs) => star_exprs
                    .maybe_simple_expression()
                    .is_some_and(|expr| expr.is_ellipsis_literal()),
                SimpleStmtContent::RaiseStmt(raise_stmt) => {
                    raise_stmt.unpack().is_some_and(|(expr, _)| {
                        match self
                            .node_ref
                            .file
                            .inference(i_s)
                            .infer_expression(expr)
                            .as_cow_type(i_s)
                            .as_ref()
                        {
                            Type::Class(cls) => {
                                cls.link == i_s.db.python_state.notimplementederror()
                            }
                            Type::Type(t) => match t.as_ref() {
                                Type::Class(cls) => {
                                    cls.link == i_s.db.python_state.notimplementederror()
                                }
                                _ => false,
                            },
                            _ => false,
                        }
                    })
                }
                _ => false,
            }
        };
        match self.node().body().unpack() {
            BlockContent::OneLine(simple_stmts) => {
                let simple_stmt = simple_stmts.maybe_single_simple_stmt();
                if simple_stmt.is_some_and(|simple_stmt| {
                    simple_stmt
                        .maybe_simple_expression()
                        .is_some_and(|expr| expr.maybe_single_string_literal().is_some())
                }) {
                    // Basically a docstring
                    return true;
                }
                check_simple_stmt(simple_stmt)
            }
            BlockContent::Indented(mut stmts) => {
                let StmtOrError::Stmt(mut first_stmt) = stmts.next().unwrap() else {
                    return false;
                };
                if first_stmt.maybe_single_string_literal().is_some() {
                    // Is a docstr, skip.
                    match stmts.next() {
                        Some(StmtOrError::Stmt(s)) => first_stmt = s,
                        Some(_) => return false,
                        None => return true,
                    }
                }
                if stmts.next().is_some() {
                    return false;
                }
                check_simple_stmt(first_stmt.maybe_single_simple_stmt())
            }
        }
    }

    pub fn iter_args_with_params<'b, AI: Iterator<Item = Arg<'db, 'b>>>(
        &self,
        db: &'db Database,
        args: AI,
        skip_first_param: bool,
    ) -> InferrableParamIterator<
        'db,
        'b,
        impl Iterator<Item = FunctionParam<'b>>,
        FunctionParam<'b>,
        AI,
    >
    where
        'a: 'b,
    {
        let mut params = self.iter_params();
        if skip_first_param {
            params.next();
        }
        InferrableParamIterator::new(db, params, args)
    }

    fn execute_without_annotation(
        &self,
        i_s: &InferenceState<'db, '_>,
        args: &dyn Args<'db>,
    ) -> Inferred {
        if self.node_ref.file.flags(i_s.db).mypy_compatible {
            return Inferred::new_any(AnyCause::Unannotated);
        }
        if self.is_generator() {
            todo!("Maybe not check here, because this could be precalculated and cached");
        }
        let inner_i_s = i_s.with_func_and_args(self, args);
        for return_or_yield in self.iter_return_or_yield() {
            match return_or_yield {
                ReturnOrYield::Return(ret) =>
                // TODO multiple returns, this is an early exit
                {
                    if let Some(star_expressions) = ret.star_expressions() {
                        return self
                            .node_ref
                            .file
                            .inference(&inner_i_s)
                            .infer_star_expressions(star_expressions, &mut ResultContext::Unknown)
                            .resolve_untyped_function_return(&inner_i_s);
                    } else {
                        todo!()
                    }
                }
                ReturnOrYield::Yield(yield_expr) => unreachable!(),
            }
        }
        Inferred::new_none()
    }

    pub fn iter_return_or_yield(&self) -> ReturnOrYieldIterator<'a> {
        let def_point = self.node_ref.file.points.get(self.node_ref.node_index + 1);
        let first_return_or_yield = def_point.node_index();
        ReturnOrYieldIterator {
            file: self.node_ref.file,
            next_node_index: first_return_or_yield,
        }
    }

    pub fn is_generator(&self) -> bool {
        for return_or_yield in self.iter_return_or_yield() {
            if let ReturnOrYield::Yield(_) = return_or_yield {
                return true;
            }
        }
        false
    }

    pub fn is_async(&self) -> bool {
        matches!(
            self.node().parent(),
            FunctionParent::Async | FunctionParent::DecoratedAsync(_)
        )
    }

    pub fn type_vars(&self, i_s: &InferenceState<'db, '_>) -> &'a TypeVarLikes {
        let type_var_reference = self.type_var_reference();
        if type_var_reference.point().calculated() {
            if let Some(complex) = type_var_reference.complex() {
                match complex {
                    ComplexPoint::TypeVarLikes(vars) => return vars,
                    _ => unreachable!(),
                }
            }
            &i_s.db.python_state.empty_type_var_likes
        } else {
            unreachable!()
        }
    }

    fn type_var_reference(&self) -> NodeRef<'a> {
        // To save the generics just use the ( operator's storage.
        // + 1 for def; + 2 for name + 1 for (...)
        self.node_ref
            .add_to_node_index(NAME_TO_FUNCTION_DIFF as i64 + 1)
    }

    fn avoid_invalid_typeguard_signatures(
        &self,
        i_s: &InferenceState,
        callable: &mut CallableContent,
    ) {
        if let Some(guard) = callable.guard.as_ref() {
            let mut param_iterator = self.node().params().iter();
            if self.class.is_some() && !matches!(callable.kind, FunctionKind::Staticmethod) {
                param_iterator.next();
            }
            let first_param = param_iterator.next();
            if !first_param.is_some_and(|p| {
                matches!(
                    p.kind(),
                    ParamKind::PositionalOnly | ParamKind::PositionalOrKeyword
                )
            }) {
                self.add_issue_for_declaration(
                    i_s,
                    IssueKind::TypeGuardFunctionsMustHaveArgument {
                        name: if guard.from_type_is {
                            "\"TypeIs\""
                        } else {
                            "TypeGuard"
                        },
                    },
                );
                callable.guard = None;
                return;
            }
            if guard.from_type_is {
                if let Some(param) = first_param {
                    if let Some(annotation) = param.annotation() {
                        let annotation_t = use_cached_param_annotation_type(
                            i_s.db,
                            self.node_ref.file,
                            annotation,
                        );
                        if !guard.type_.is_simple_sub_type_of(i_s, &annotation_t).bool() {
                            self.add_issue_for_declaration(
                                i_s,
                                IssueKind::TypeIsNarrowedTypeIsNotSubtypeOfInput {
                                    narrowed_t: guard.type_.format_short(i_s.db),
                                    input_t: annotation_t.format_short(i_s.db),
                                },
                            );
                        }
                    }
                }
            }
        }
    }

    pub fn ensure_cached_func(&self, i_s: &InferenceState<'db, '_>) {
        if self.node_ref.point().calculated() {
            return;
        }
        let maybe_decorated = self.node().maybe_decorated();
        if let Some(decorated) = maybe_decorated {
            if self
                .node_ref
                .file
                .inference(i_s)
                .is_no_type_check(decorated)
            {
                let mut callable_t = self.as_callable_content_internal(
                    i_s.db.python_state.empty_type_var_likes.clone(),
                    CallableParams::Any(AnyCause::Explicit),
                    false,
                    Type::Any(AnyCause::Explicit),
                );
                callable_t.no_type_check = true;
                self.node_ref.insert_complex(
                    ComplexPoint::TypeInstance(Type::Callable(Rc::new(callable_t))),
                    Locality::Todo,
                );
                return;
            }
        }

        let maybe_computed = self.ensure_cached_type_vars(i_s);
        if let Some(decorated) = maybe_decorated {
            if let Some(class) = self.class {
                let class = Class::with_self_generics(i_s.db, class.node_ref);
                Self::new(self.node_ref, Some(class)).decorated_to_be_saved(
                    &i_s.with_class_context(&class),
                    decorated,
                    maybe_computed,
                )
            } else {
                self.decorated_to_be_saved(i_s, decorated, maybe_computed)
            }
            .save_redirect(i_s, self.node_ref.file, self.node_ref.node_index);
        } else if let Some(mut callable_t) = maybe_computed {
            self.avoid_invalid_typeguard_signatures(i_s, &mut callable_t);
            self.node_ref.insert_complex(
                ComplexPoint::TypeInstance(Type::Callable(Rc::new(callable_t))),
                Locality::Todo,
            );
        } else {
            self.node_ref
                .set_point(Point::new_specific(Specific::Function, Locality::Todo));
        }
    }

    fn ensure_cached_type_vars(&self, i_s: &InferenceState<'db, '_>) -> Option<CallableContent> {
        let type_var_reference = self.type_var_reference();
        if type_var_reference.point().calculated() {
            return None; // TODO this feels wrong, because below we only sometimes calculate the callable
        }
        let (type_vars, type_guard, star_annotation) = self.cache_type_vars(i_s);
        match type_vars.len() {
            0 => type_var_reference.set_point(Point::new_node_analysis(Locality::Todo)),
            _ => type_var_reference
                .insert_complex(ComplexPoint::TypeVarLikes(type_vars), Locality::Todo),
        }
        debug_assert!(type_var_reference.point().calculated());

        let mut needs_callable = false;
        if let Some(annotation) = star_annotation {
            let t = use_cached_param_annotation_type(i_s.db, self.node_ref.file, annotation);
            if t.maybe_fixed_len_tuple().is_some() {
                // Save a callable, because we have something like `*foo: *tuple[int, str]`, which
                // basically means two mandatory positional only arguments. But this is not part of
                // the type system. Therefore just write a proper callable definition.
                needs_callable = true;
            }
        }
        if needs_callable || type_guard.is_some() {
            let options = AsCallableOptions {
                first_param: FirstParamProperties::None,
                return_type: match type_guard.as_ref() {
                    Some(guard) => Cow::Owned(i_s.db.python_state.bool_type()),
                    None => self.return_type(i_s),
                },
            };
            let mut callable = self.as_callable_with_options(i_s, options);
            callable.guard = type_guard;
            return Some(callable);
        }
        None
    }

    fn cache_type_vars(
        &self,
        i_s: &InferenceState<'db, '_>,
    ) -> (TypeVarLikes, Option<TypeGuardInfo>, Option<ParamAnnotation>) {
        let func_node = self.node();
        let implicit_optional = self.node_ref.file.flags(i_s.db).implicit_optional;
        let inference = self.node_ref.file.inference(i_s);
        let in_result_type = Cell::new(false);
        let mut unbound_type_vars = vec![];
        let mut on_type_var = |i_s: &InferenceState,
                               manager: &TypeVarManager<PointLink>,
                               type_var: TypeVarLike,
                               current_callable: Option<_>| {
            self.class
                .and_then(|class| {
                    class
                        .type_vars(i_s)
                        .find(type_var.clone(), class.node_ref.as_link())
                        .map(TypeVarCallbackReturn::TypeVarLike)
                })
                .or_else(|| i_s.find_parent_type_var(&type_var))
                .unwrap_or_else(|| {
                    if in_result_type.get()
                        && manager.position(&type_var).is_none()
                        && current_callable.is_none()
                    {
                        unbound_type_vars.push(type_var);
                    }
                    TypeVarCallbackReturn::NotFound
                })
        };
        let mut type_computation = TypeComputation::new(
            &inference,
            self.node_ref.as_link(),
            &mut on_type_var,
            TypeComputationOrigin::ParamTypeCommentOrAnnotation,
        );
        let mut star_annotation = None;
        for param in func_node.params().iter() {
            if let Some(annotation) = param.annotation() {
                let mut is_implicit_optional = false;
                if implicit_optional {
                    if let Some(default) = param.default() {
                        if default.as_code() == "None" {
                            is_implicit_optional = true;
                        }
                    }
                }
                let param_kind = param.kind();
                type_computation.cache_param_annotation(
                    annotation,
                    param_kind,
                    is_implicit_optional,
                );
                if param_kind == ParamKind::Star {
                    star_annotation = Some(annotation);
                }
            }
        }
        let type_guard = func_node.return_annotation().and_then(|return_annot| {
            in_result_type.set(true);
            type_computation.cache_return_annotation(return_annot)
        });
        let type_vars = type_computation.into_type_vars(|inf, recalculate_type_vars| {
            for param in func_node.params().iter() {
                if let Some(annotation) = param.annotation() {
                    inf.recalculate_annotation_type_vars(annotation.index(), recalculate_type_vars);
                }
            }
            if let Some(return_annot) = func_node.return_annotation() {
                inf.recalculate_annotation_type_vars(return_annot.index(), recalculate_type_vars);
            }
        });
        if !unbound_type_vars.is_empty() {
            if let Type::TypeVar(t) = self.return_type(i_s).as_ref() {
                if unbound_type_vars.contains(&TypeVarLike::TypeVar(t.type_var.clone())) {
                    let node_ref = self.expect_return_annotation_node_ref();
                    node_ref.add_issue(i_s, IssueKind::TypeVarInReturnButNotArgument);
                    if let TypeVarKind::Bound(bound) = &t.type_var.kind {
                        node_ref.add_issue(
                            i_s,
                            IssueKind::Note(
                                format!(
                                    "Consider using the upper bound \"{}\" instead",
                                    bound.format_short(i_s.db)
                                )
                                .into(),
                            ),
                        );
                    }
                }
            }
        }
        (type_vars, type_guard, star_annotation)
    }

    fn remap_param_spec(
        &self,
        i_s: &InferenceState,
        mut pre_params: Vec<CallableParam>,
        usage: &ParamSpecUsage,
    ) -> CallableParams {
        let into_types = |mut types: Vec<_>, pre_params: Vec<CallableParam>| {
            types.extend(
                pre_params
                    .into_iter()
                    .map(|p| p.type_.expect_positional_type()),
            );
            Rc::from(types)
        };
        match self.class {
            Some(c) if c.node_ref.as_link() == usage.in_definition => match c
                .generics()
                .nth_usage(i_s.db, &TypeVarLikeUsage::ParamSpec(usage.clone()))
            {
                Generic::ParamSpecArg(p) => match p.into_owned().params {
                    CallableParams::Any(cause) => CallableParams::Any(cause),
                    CallableParams::Simple(params) => {
                        pre_params.append(&mut rc_slice_into_vec(params));
                        CallableParams::Simple(Rc::from(pre_params))
                    }
                    CallableParams::WithParamSpec(pre, p) => {
                        let types = rc_slice_into_vec(pre);
                        CallableParams::WithParamSpec(into_types(types, pre_params), p)
                    }
                    CallableParams::Never(cause) => CallableParams::Never(cause),
                },
                _ => unreachable!(),
            },
            _ => {
                let types = vec![];
                CallableParams::WithParamSpec(into_types(types, pre_params), usage.clone())
            }
        }
    }

    pub fn cache_func(&self, i_s: &InferenceState) {
        self.cache_func_with_name_def(
            i_s,
            NodeRef::new(self.node_ref.file, self.node().name_definition().index()),
        )
    }

    pub fn cache_func_with_name_def(&self, i_s: &InferenceState, name_def: NodeRef) {
        if !name_def.point().calculated() {
            self.ensure_cached_func(i_s);
            name_def.set_point(Point::new_redirect(
                self.node_ref.file_index(),
                self.node_ref.node_index,
                Locality::Todo,
            ));
            if self.node_ref.point().maybe_specific() != Some(Specific::OverloadUnreachable) {
                if FLOW_ANALYSIS.with(|fa| fa.in_conditional()) {
                    self.check_conditional_function_definition(i_s)
                } else {
                    name_def
                        .file
                        .inference(i_s)
                        .check_for_redefinition(name_def, |issue| {
                            self.add_issue_onto_start_including_decorator(i_s, issue)
                        });
                }
            }
        }
    }

    fn check_conditional_function_definition(&self, i_s: &InferenceState) {
        let Some(first) =
            first_defined_name_of_multi_def(self.node_ref.file, self.node().name().index())
        else {
            return;
        };
        // At this point we know it's a conditional redefinition and not just a singular def in an
        // if.
        let original = self
            .node_ref
            .file
            .inference(i_s)
            .infer_name_of_definition_by_index(first);
        let original_t = original.as_cow_type(i_s);
        let redefinition = Inferred::from_saved_node_ref(self.node_ref);

        if self.node().maybe_decorated().is_none()
            && NodeRef::new(self.node_ref.file, first)
                .maybe_name_of_function()
                .is_some_and(|func| func.maybe_decorated().is_none())
        {
            let redefinition_t = redefinition.as_cow_type(i_s);
            if !original_t
                .is_simple_same_type(i_s, &redefinition_t)
                .non_any_match()
            {
                let Type::Callable(original) = original_t.as_ref() else {
                    unreachable!()
                };
                let Type::Callable(redefinition) = redefinition_t.as_ref() else {
                    unreachable!()
                };
                self.add_issue_for_declaration(
                    i_s,
                    IssueKind::IncompatibleConditionalFunctionSignaturePretty {
                        original: original.format_pretty(&FormatData::new_short(i_s.db)),
                        redefinition: redefinition.format_pretty(&FormatData::new_short(i_s.db)),
                    },
                )
            }
        } else {
            original_t.error_if_not_matches(
                i_s,
                &redefinition,
                |issue| self.add_issue_for_declaration(i_s, issue),
                |error_types| {
                    let ErrorStrs { expected, got } = error_types.as_boxed_strs(i_s.db);
                    Some(IssueKind::IncompatibleConditionalFunctionSignature {
                        original: expected,
                        redefinition: got,
                    })
                },
            )
        }
    }

    pub fn is_dunder_new(&self) -> bool {
        self.class.is_some() && self.name() == "__new__"
    }

    pub fn first_param_kind(&self, i_s: &InferenceState<'db, '_>) -> FirstParamKind {
        if self.is_dunder_new() {
            return FirstParamKind::ClassOfSelf;
        }
        match self.kind() {
            FunctionKind::Function { .. } | FunctionKind::Property { .. } => FirstParamKind::Self_,
            FunctionKind::Classmethod { .. } => FirstParamKind::ClassOfSelf,
            FunctionKind::Staticmethod => FirstParamKind::InStaticmethod,
        }
    }

    pub fn kind(&self) -> FunctionKind {
        let had_first_annotation = self.class.is_none()
            || self
                .node()
                .params()
                .iter()
                .next()
                .is_some_and(|p| p.annotation().is_some());
        match self.node_ref.complex() {
            Some(ComplexPoint::TypeInstance(Type::Callable(c))) => c.kind,
            Some(ComplexPoint::FunctionOverload(o)) => o.kind(),
            _ => {
                if self.node_ref.point().maybe_specific() == Some(Specific::OverloadUnreachable) {
                    let first = first_defined_name(self.node_ref.file, self.node().name().index());
                    let original_func =
                        NodeRef::new(self.node_ref.file, first - NAME_TO_FUNCTION_DIFF);
                    let point = original_func.point();
                    Function::new(original_func, self.class).kind()
                } else {
                    FunctionKind::Function {
                        had_first_self_or_class_annotation: had_first_annotation,
                    }
                }
            }
        }
    }

    fn decorated_to_be_saved(
        &self,
        i_s: &InferenceState<'db, '_>,
        decorated: Decorated,
        base_t: Option<CallableContent>,
    ) -> Inferred {
        let Some(details) = self.calculate_decorated_function_details(i_s, decorated, base_t)
        else {
            return Inferred::new_any_from_error();
        };

        let file = self.node_ref.file;
        if details.is_overload {
            return if let Some(overload) = self.calculate_next_overload_items(i_s, details) {
                Inferred::new_unsaved_complex(ComplexPoint::FunctionOverload(Box::new(overload)))
            } else {
                Inferred::new_any_from_error()
            };
        }
        match details.kind {
            FunctionKind::Property {
                had_first_self_or_class_annotation: had_first_annotation,
                ..
            } => {
                let Type::Callable(mut callable) = details.inferred.as_type(i_s) else {
                    unreachable!()
                };
                if let Some(wrong) = callable.has_exactly_one_positional_parameter() {
                    match wrong {
                        WrongPositionalCount::TooMany => {
                            NodeRef::new(file, self.expect_decorated_node().index())
                                .add_issue(i_s, IssueKind::TooManyArguments(" for property".into()))
                        }
                        // IssueType::MethodWithoutArguments will be checked and added later.
                        WrongPositionalCount::TooFew => (),
                    }
                    return Inferred::new_any_from_error();
                }
                // Make sure the old Rc count is decreased, so we can use it mutable without cloning.
                drop(details);
                self.calculate_property_setter_and_deleter(
                    i_s,
                    Rc::make_mut(&mut callable),
                    had_first_annotation,
                );
                Inferred::from_type(Type::Callable(callable))
            }
            _ => details.inferred,
        }
    }

    fn expect_decorated_node(&self) -> Decorated {
        self.node().maybe_decorated().unwrap()
    }

    fn calculate_decorated_function_details(
        &self,
        i_s: &InferenceState,
        decorated: Decorated,
        base_t: Option<CallableContent>,
    ) -> Option<FunctionDetails> {
        let used_with_a_non_method = |name| {
            NodeRef::new(self.node_ref.file, decorated.index())
                .add_issue(i_s, IssueKind::UsedWithANonMethod { name })
        };

        let mut inferred = Inferred::from_type(
            base_t
                .map(|c| Type::Callable(Rc::new(c)))
                .unwrap_or_else(|| self.as_type(i_s, FirstParamProperties::None)),
        );
        let had_first_annotation = self.class.is_none()
            || self
                .node()
                .params()
                .iter()
                .next()
                .is_some_and(|p| p.annotation().is_some());
        let mut kind = FunctionKind::Function {
            had_first_self_or_class_annotation: had_first_annotation,
        };
        let mut is_overload = false;
        let mut is_abstract = false;
        let mut is_final = false;
        for decorator in decorated.decorators().iter_reverse() {
            let inferred_dec =
                infer_decorator_details(i_s, self.node_ref.file, decorator, had_first_annotation);
            let nr = || NodeRef::new(self.node_ref.file, decorator.index());
            if matches!(kind, FunctionKind::Property { .. })
                && !matches!(
                    inferred_dec,
                    InferredDecorator::Final | InferredDecorator::Override
                )
            {
                nr().add_issue(i_s, IssueKind::DecoratorOnTopOfPropertyNotSupported);
                break;
            }

            match inferred_dec {
                InferredDecorator::FunctionKind {
                    kind: k,
                    is_abstract: dec_is_abstract,
                } => {
                    is_abstract |= dec_is_abstract;
                    match k {
                        FunctionKind::Property { .. } => {
                            if is_overload {
                                nr().add_issue(i_s, IssueKind::OverloadedPropertyNotSupported);
                                return None;
                            }
                            if self.class.is_none() {
                                used_with_a_non_method("property");
                                return None;
                            }
                            if !matches!(kind, FunctionKind::Function { .. }) {
                                nr().add_issue(
                                    i_s,
                                    IssueKind::OnlyInstanceMethodsCanBeDecoratedWithProperty,
                                );
                            }
                        }
                        FunctionKind::Classmethod { .. } => {
                            if kind == FunctionKind::Staticmethod {
                                nr().add_issue(i_s, IssueKind::InvalidClassmethodAndStaticmethod);
                                return None;
                            }
                            if self.class.is_none() {
                                used_with_a_non_method("classmethod");
                                return None;
                            }
                        }
                        FunctionKind::Staticmethod => {
                            if matches!(kind, FunctionKind::Classmethod { .. }) {
                                nr().add_issue(i_s, IssueKind::InvalidClassmethodAndStaticmethod)
                            }
                            if self.class.is_none() {
                                used_with_a_non_method("staticmethod");
                                return None;
                            }
                        }
                        // A decorator has no way to specify its a normal function.
                        FunctionKind::Function { .. } => unreachable!(),
                    }
                    kind = k
                }
                InferredDecorator::Inferred(dec_inf) => {
                    // TODO check if it's an function without a return annotation and
                    // abort in that case.
                    if self.node_ref.file.flags(i_s.db).disallow_untyped_decorators {
                        let is_typed = |inf: &Inferred, skip_first_param| {
                            let t = inf.as_cow_type(i_s);
                            if matches!(t.as_ref(), Type::Any(_)) {
                                return false;
                            }
                            t.maybe_callable(i_s)
                                .map(|c| c.is_typed(skip_first_param))
                                // A non-callable will raise errors later anyway
                                .unwrap_or(true)
                        };
                        if self.is_typed() && !is_typed(&dec_inf, false) {
                            nr().add_issue(
                                i_s,
                                IssueKind::UntypedDecorator {
                                    name: self.name().into(),
                                },
                            );
                        }
                    }
                    inferred = dec_inf.execute(i_s, &KnownArgs::new(&inferred, nr()));
                }
                InferredDecorator::Overload => is_overload = true,
                InferredDecorator::Abstractmethod => is_abstract = true,
                InferredDecorator::Final => {
                    if self.class.is_none() {
                        nr().add_issue(i_s, IssueKind::FinalCanOnlyBeUsedInMethods);
                    }
                    is_final = true
                }
                InferredDecorator::Override => (),
            }
        }
        if is_abstract && is_final {
            self.add_issue_onto_start_including_decorator(
                i_s,
                IssueKind::FinalMethodIsAbstract {
                    name: self.name().into(),
                },
            )
        }
        if is_abstract && self.class.is_none() {
            is_abstract = false;
            self.add_issue_onto_start_including_decorator(
                i_s,
                IssueKind::UsedWithANonMethod {
                    name: "abstractmethod",
                },
            )
        }
        let overwrite_callable = |inferred: &mut _, mut callable: CallableContent| {
            callable.name = Some(DbString::StringSlice(self.name_string_slice()));
            callable.class_name = self.class.map(|c| c.name_string_slice());
            callable.kind = kind;
            callable.is_abstract = is_abstract;
            callable.is_final = is_final;
            self.avoid_invalid_typeguard_signatures(i_s, &mut callable);
            *inferred = Inferred::from_type(Type::Callable(Rc::new(callable)));
        };
        if self.node_ref.file.flags(i_s.db).disallow_any_decorated {
            let t = inferred.as_cow_type(i_s);
            if t.has_any(i_s) {
                let got = (!matches!(t.as_ref(), Type::Any(_))).then(|| t.format_short(i_s.db));
                NodeRef::new(self.node_ref.file, self.node().name().index())
                    .add_issue(i_s, IssueKind::UntypedFunctionAfterDecorator { got })
            }
        }
        if matches!(
            kind,
            FunctionKind::Function { .. } | FunctionKind::Staticmethod
        ) {
            if let Type::Callable(c) = inferred.as_type(i_s) {
                overwrite_callable(&mut inferred, (*c).clone())
            }
        } else if let Some(CallableLike::Callable(c)) =
            inferred.as_cow_type(i_s).maybe_callable(i_s)
        {
            overwrite_callable(&mut inferred, (*c).clone())
        } else {
            self.add_issue_for_declaration(
                i_s,
                IssueKind::NotCallable {
                    type_: format!("\"{}\"", inferred.format_short(i_s)).into(),
                },
            );
            return None;
        }
        Some(FunctionDetails {
            inferred,
            kind,
            is_overload,
            has_decorator: true,
        })
    }

    fn calculate_property_setter_and_deleter(
        &self,
        i_s: &InferenceState,
        callable: &mut CallableContent,
        had_first_annotation: bool,
    ) {
        let is_property_modifier = |decorator: Decorator| {
            let ExpressionContent::ExpressionPart(ExpressionPart::Primary(primary)) =
                decorator.named_expression().expression().unpack()
            else {
                return PropertyModifier::JustADecorator;
            };
            let PrimaryOrAtom::Atom(first) = primary.first() else {
                return PropertyModifier::JustADecorator;
            };
            if first.as_code() != self.name() {
                return PropertyModifier::JustADecorator;
            }
            let PrimaryContent::Attribute(second) = primary.second() else {
                return PropertyModifier::JustADecorator;
            };
            match second.as_code() {
                "setter" => PropertyModifier::Setter,
                "deleter" => PropertyModifier::Deleter,
                _ => PropertyModifier::JustADecorator,
            }
        };
        let first_index = self.node().name().index();
        let mut current_name_index = first_index;
        let file = self.node_ref.file;
        loop {
            let point = file.points.get(current_name_index);
            if !point.calculated() {
                break;
            }
            debug_assert_eq!(point.kind(), PointKind::MultiDefinition);
            current_name_index = point.node_index();
            if current_name_index <= first_index {
                break;
            }
            let func_ref = NodeRef::new(file, current_name_index - NAME_TO_FUNCTION_DIFF);
            let Some(decorated) = func_ref.maybe_function().and_then(|f| f.maybe_decorated())
            else {
                func_ref.add_issue(
                    i_s,
                    IssueKind::UnexpectedDefinitionForProperty {
                        name: self.name().into(),
                    },
                );
                continue;
            };
            let next_func = Self::new(func_ref, self.class);
            let new_t = next_func.ensure_cached_type_vars(i_s);
            if new_t.is_some() {
                todo!()
            }

            // Make sure this is not calculated again.
            next_func.node_ref.set_point(Point::new_specific(
                Specific::OverloadUnreachable,
                Locality::File,
            ));

            let mut iterator = decorated.decorators().iter();
            let decorator = iterator.next().unwrap();
            match is_property_modifier(decorator) {
                PropertyModifier::JustADecorator => {
                    NodeRef::new(file, decorator.index()).add_issue(
                        i_s,
                        IssueKind::OnlySupportedTopDecoratorSetter {
                            name: self.name().into(),
                        },
                    );
                }
                PropertyModifier::Setter => {
                    callable.kind = FunctionKind::Property {
                        had_first_self_or_class_annotation: had_first_annotation,
                        writable: true,
                    };
                    continue;
                }
                PropertyModifier::Deleter => continue,
            };
        }
    }

    fn calculate_next_overload_items(
        &self,
        i_s: &InferenceState,
        details: FunctionDetails,
    ) -> Option<OverloadDefinition> {
        let first_index = self.node().name().index();
        let mut current_name_index = first_index;
        let file = self.node_ref.file;
        let mut functions = vec![];
        let in_stub = file.is_stub();

        let mut add_func = |func: &Function, inf: Inferred, is_first: bool| {
            if let Some(CallableLike::Callable(callable)) = inf.as_cow_type(i_s).maybe_callable(i_s)
            {
                if callable.is_final && !(in_stub && is_first) {
                    for decorator in func.node().maybe_decorated().unwrap().decorators().iter() {
                        if matches!(
                            infer_decorator_details(i_s, func.node_ref.file, decorator, true),
                            InferredDecorator::Final
                        ) {
                            NodeRef::new(func.node_ref.file, decorator.index()).add_issue(
                                i_s,
                                match in_stub {
                                    false => {
                                        IssueKind::FinalShouldBeAppliedOnlyToOverloadImplementation
                                    }
                                    true => IssueKind::FinalInStubMustBeAppliedToFirstOverload,
                                },
                            )
                        }
                    }
                }
                functions.push(callable)
            } else {
                todo!()
            }
        };
        let mut inconsistent_function_kind = None;
        add_func(self, details.inferred, true);
        let mut implementation: Option<OverloadImplementation> = None;
        let mut should_error_out = false;
        loop {
            let point = file.points.get(current_name_index);
            if !point.calculated() {
                break;
            }
            debug_assert_eq!(point.kind(), PointKind::MultiDefinition);
            current_name_index = point.node_index();
            if current_name_index <= first_index {
                break;
            }
            let func_ref = NodeRef::new(file, current_name_index - NAME_TO_FUNCTION_DIFF);
            let Some(next_func_def) = func_ref.maybe_function() else {
                todo!("probably just some other definition like foo = 3?")
            };
            let next_func = Self::new(func_ref, self.class);
            let new_t = next_func.ensure_cached_type_vars(i_s);
            let next_maybe_decorated = next_func_def.maybe_decorated();
            let next_details = match next_maybe_decorated.and_then(|decorated| {
                next_func.calculate_decorated_function_details(i_s, decorated, new_t)
            }) {
                Some(d) => d,
                None => {
                    if next_maybe_decorated.is_some() {
                        should_error_out = true;
                        next_func.node_ref.set_point(Point::new_specific(
                            Specific::OverloadUnreachable,
                            Locality::File,
                        ));
                        continue;
                    }
                    FunctionDetails {
                        inferred: Inferred::from_type(
                            next_func.as_type(i_s, FirstParamProperties::None),
                        ),
                        kind: FunctionKind::Function {
                            had_first_self_or_class_annotation: self
                                .node()
                                .params()
                                .iter()
                                .next()
                                .is_some_and(|p| p.annotation().is_some()),
                        },
                        is_overload: false,
                        has_decorator: false,
                    }
                }
            };
            if !details.kind.is_same_base_kind(next_details.kind) {
                if matches!(details.kind, FunctionKind::Function { .. }) {
                    inconsistent_function_kind = Some(next_details.kind)
                } else {
                    inconsistent_function_kind = Some(details.kind)
                }
            }
            // To make sure overloads aren't executed another time and to separate these
            // functions from the other ones, mark them unreachable here.
            next_func.node_ref.set_point(Point::new_specific(
                Specific::OverloadUnreachable,
                Locality::File,
            ));
            if next_details.is_overload {
                if let Some(implementation) = &implementation {
                    NodeRef::from_link(i_s.db, implementation.function_link)
                        .add_issue(i_s, IssueKind::OverloadImplementationNotLast)
                }
                add_func(&next_func, next_details.inferred, false)
            } else {
                // Check if the implementing function was already set
                if implementation.is_none() {
                    let t = next_details.inferred.as_cow_type(i_s);
                    if !next_details.has_decorator && !next_func.is_typed() || t.is_any() {
                        implementation = Some(OverloadImplementation {
                            function_link: func_ref.as_link(),
                            callable: CallableContent::new_any_with_defined_at(
                                i_s.db,
                                func_ref.as_link(),
                                AnyCause::Todo,
                            ),
                        });
                    } else if let Some(CallableLike::Callable(callable)) = t.maybe_callable(i_s) {
                        implementation = Some(OverloadImplementation {
                            function_link: func_ref.as_link(),
                            callable: rc_unwrap_or_clone(callable),
                        });
                    } else {
                        implementation = Some(OverloadImplementation {
                            function_link: func_ref.as_link(),
                            callable: CallableContent::new_any_with_defined_at(
                                i_s.db,
                                func_ref.as_link(),
                                AnyCause::FromError,
                            ),
                        });
                        NodeRef::new(func_ref.file, next_func.expect_decorated_node().index())
                            .add_issue(
                                i_s,
                                IssueKind::NotCallable {
                                    type_: format!("\"{}\"", t.format_short(i_s.db)).into(),
                                },
                            )
                    }
                } else {
                    todo!()
                }
            }
        }
        let name_def_node_ref = |link| {
            let node_ref = NodeRef::from_link(i_s.db, link);
            let name_def = node_ref.maybe_function().unwrap().name_definition();
            NodeRef::new(node_ref.file, name_def.index())
        };
        if let Some(kind) = inconsistent_function_kind {
            NodeRef::new(self.node_ref.file, self.expect_decorated_node().index())
                .add_issue(i_s, IssueKind::OverloadInconsistentKind { kind })
        }
        if functions.len() < 2 && !should_error_out {
            self.node_ref
                .add_issue(i_s, IssueKind::OverloadSingleNotAllowed);
        } else if implementation.is_none()
            && !in_stub
            && self.class.map(|c| !c.is_protocol(i_s.db)).unwrap_or(true)
        {
            name_def_node_ref(functions.last().unwrap().defined_at)
                .add_issue(i_s, IssueKind::OverloadImplementationNeeded);
        }
        if let Some(implementation) = &implementation {
            if in_stub {
                name_def_node_ref(implementation.function_link)
                    .add_issue(i_s, IssueKind::OverloadStubImplementationNotAllowed);
            }
        }

        let is_final = if in_stub {
            functions.first().unwrap().is_final
        } else {
            implementation
                .as_ref()
                .is_some_and(|implementation| implementation.callable.is_final)
        };

        debug_assert!(!functions.is_empty());
        (!should_error_out).then(|| OverloadDefinition {
            functions: FunctionOverload::new(functions.into_boxed_slice()),
            implementation,
            is_final,
        })
    }

    fn maybe_part_of_unreachable_overload(&self) -> Option<&OverloadDefinition> {
        let file = self.node_ref.file;
        if self.node_ref.point().maybe_specific() == Some(Specific::OverloadUnreachable) {
            if let Some(first_index) =
                first_defined_name_of_multi_def(file, self.node().name().index())
            {
                if let Some(func) = NodeRef::new(file, first_index).maybe_name_of_function() {
                    if let Some(ComplexPoint::FunctionOverload(o)) =
                        NodeRef::new(self.node_ref.file, func.index()).complex()
                    {
                        return Some(o);
                    }
                }
            }
        }
        None
    }

    pub fn is_overload_implementation(&self) -> bool {
        self.maybe_part_of_unreachable_overload()
            .and_then(|overload| overload.implementation.as_ref())
            .is_some_and(|link| link.function_link == self.node_ref.as_link())
    }

    pub fn is_abstract(&self) -> bool {
        match self.node_ref.complex() {
            Some(ComplexPoint::TypeInstance(Type::Callable(c))) => c.is_abstract,
            Some(ComplexPoint::FunctionOverload(o)) => o.functions.is_abstract(),
            _ => {
                if let Some(overload) = self.maybe_part_of_unreachable_overload() {
                    overload.functions.is_abstract()
                } else {
                    false
                }
            }
        }
    }

    pub fn is_final(&self) -> bool {
        match self.node_ref.complex() {
            Some(ComplexPoint::TypeInstance(Type::Callable(c))) => c.is_final,
            Some(ComplexPoint::FunctionOverload(o)) => o.is_final,
            _ => {
                if let Some(overload) = self.maybe_part_of_unreachable_overload() {
                    overload.is_final
                } else {
                    false
                }
            }
        }
    }

    pub(crate) fn add_issue_for_declaration(&self, i_s: &InferenceState, kind: IssueKind) {
        let node = self.node();
        self.node_ref.file.add_issue(
            i_s,
            Issue {
                kind,
                start_position: node.start(),
                end_position: node.end_position_of_colon(),
            },
        )
    }

    pub(crate) fn add_issue_onto_start_including_decorator(
        &self,
        i_s: &InferenceState,
        kind: IssueKind,
    ) {
        let node = self.node();
        if let Some(decorated) = node.maybe_decorated() {
            NodeRef::new(self.node_ref.file, decorated.index()).add_issue(i_s, kind)
        } else {
            self.add_issue_for_declaration(i_s, kind)
        }
    }

    pub fn as_callable(
        &self,
        i_s: &InferenceState,
        first_param: FirstParamProperties,
    ) -> CallableContent {
        self.as_callable_with_options(
            i_s,
            AsCallableOptions {
                first_param,
                return_type: self.return_type(i_s),
            },
        )
    }

    pub fn as_callable_with_options(
        &self,
        i_s: &InferenceState,
        options: AsCallableOptions,
    ) -> CallableContent {
        let mut params = self.iter_params().peekable();
        let mut self_type_var_usage = None;
        let defined_at = self.node_ref.as_link();
        let mut type_vars = self.type_vars(i_s).as_vec();
        match options.first_param {
            FirstParamProperties::MethodAccessedOnClass => {
                let mut needs_self_type_variable = self.return_type(i_s).has_self_type(i_s.db);
                for param in self.iter_params().skip(1) {
                    if let Some(t) = param.annotation(i_s.db) {
                        needs_self_type_variable |= t.has_self_type(i_s.db);
                    }
                }
                if needs_self_type_variable {
                    let self_type_var = Rc::new(TypeVar {
                        name_string: TypeVarName::Self_,
                        kind: TypeVarKind::Bound(self.class.unwrap().as_type(i_s.db)),
                        variance: Variance::Invariant,
                        default: None,
                    });
                    self_type_var_usage = Some(TypeVarUsage::new(
                        self_type_var.clone(),
                        defined_at,
                        0.into(),
                    ));
                    type_vars.insert(0, TypeVarLike::TypeVar(self_type_var));
                }
            }
            FirstParamProperties::Skip { .. } => {
                params.next();
            }
            FirstParamProperties::None => (),
        }
        let self_type_var_usage = self_type_var_usage.as_ref();

        let as_type = |t: &Type| {
            if matches!(options.first_param, FirstParamProperties::None) {
                return t.clone();
            }
            let Some(func_class) = self.class else {
                return t.clone();
            };
            t.replace_type_var_likes_and_self(
                i_s.db,
                &mut |mut usage| {
                    let in_definition = usage.in_definition();
                    if let Some(result) = maybe_class_usage(i_s.db, &func_class, &usage) {
                        result
                    } else if in_definition == defined_at {
                        if self_type_var_usage.is_some() {
                            usage.add_to_index(1);
                        }
                        usage.into_generic_item()
                    } else {
                        // This can happen for example if the return value is a Callable with its
                        // own type vars.
                        usage.into_generic_item()
                    }
                },
                &|| {
                    if let Some(self_type_var_usage) = self_type_var_usage {
                        Type::TypeVar(self_type_var_usage.clone())
                    } else if let FirstParamProperties::Skip { to_self_instance } =
                        options.first_param
                    {
                        to_self_instance()
                    } else {
                        Type::Self_
                    }
                },
            )
        };
        let return_type = as_type(&options.return_type);
        let mut callable =
            self.internal_as_type(i_s, params, self_type_var_usage, as_type, return_type);
        callable.type_vars = TypeVarLikes::from_vec(type_vars);
        if matches!(options.first_param, FirstParamProperties::Skip { .. }) {
            // Now the first param was removed, so everything is considered as having an
            // annotation (even if it's an implicit Any).
            callable
                .kind
                .update_had_first_self_or_class_annotation(true);
        }
        callable
    }

    pub fn as_type(&self, i_s: &InferenceState, first: FirstParamProperties) -> Type {
        Type::Callable(Rc::new(self.as_callable(i_s, first)))
    }

    fn internal_as_type(
        &self,
        i_s: &InferenceState,
        params: impl Iterator<Item = FunctionParam<'a>>,
        self_type_var_usage: Option<&TypeVarUsage>,
        mut as_type: impl FnMut(&Type) -> Type,
        mut return_type: Type,
    ) -> CallableContent {
        let mut params = params.peekable();
        let had_first_annotation = self.class.is_none()
            || params
                .peek()
                .is_some_and(|p| p.annotation(i_s.db).is_some());
        let kind = if let Some(decorated) = self.node().maybe_decorated() {
            kind_of_decorators(i_s, self.node_ref.file, decorated, had_first_annotation)
        } else {
            FunctionKind::Function {
                had_first_self_or_class_annotation: had_first_annotation,
            }
        };
        if self.is_async() && !self.is_generator() {
            return_type = new_class!(
                i_s.db.python_state.coroutine_link(),
                Type::Any(AnyCause::Todo),
                Type::Any(AnyCause::Todo),
                return_type,
            );
        }

        let return_result = |params| {
            self.as_callable_content_internal(
                i_s.db.python_state.empty_type_var_likes.clone(),
                params,
                had_first_annotation,
                return_type,
            )
        };

        let mut new_params = vec![];
        let mut had_param_spec_args = false;
        let file_index = self.node_ref.file_index();
        while let Some(p) = params.next() {
            if p.param.kind() == ParamKind::Star {
                if let Some(ts) = p
                    .annotation(i_s.db)
                    .as_ref()
                    .and_then(|t| t.maybe_fixed_len_tuple())
                {
                    // e.g. `*foo: *tuple[int, str]`, needs to be treated separtely, because this
                    // implies two mandatory positional only arguments. But this is not part of the
                    // type system.
                    for t in ts {
                        new_params.push(CallableParam::new_anonymous(ParamType::PositionalOnly(
                            t.clone(),
                        )));
                    }
                    continue;
                }
            }
            let specific = p.specific(i_s.db);
            let mut as_t = |t: Option<Cow<_>>| {
                t.map(|t| as_type(&t)).unwrap_or({
                    let name_ref =
                        NodeRef::new(self.node_ref.file, p.param.name_definition().index());
                    if name_ref.point().maybe_specific() == Some(Specific::MaybeSelfParam) {
                        if self.is_dunder_new() {
                            if let Some(type_var_usage) = self_type_var_usage {
                                Type::Type(Rc::new(Type::TypeVar(type_var_usage.clone())))
                            } else {
                                self.class.unwrap().as_type_type(i_s)
                            }
                        } else if let Some(type_var_usage) = self_type_var_usage {
                            Type::TypeVar(type_var_usage.clone())
                        } else {
                            match kind {
                                FunctionKind::Function { .. } | FunctionKind::Property { .. } => {
                                    self.class.unwrap().as_type(i_s.db)
                                }
                                FunctionKind::Classmethod { .. } => {
                                    Type::Any(AnyCause::Unannotated)
                                }
                                FunctionKind::Staticmethod => Type::Any(AnyCause::Unannotated),
                            }
                        }
                    } else {
                        Type::Any(AnyCause::Unannotated)
                    }
                })
            };
            let param_specific = match specific {
                WrappedParamType::PositionalOnly(t) => ParamType::PositionalOnly(as_t(t)),
                WrappedParamType::PositionalOrKeyword(t) => ParamType::PositionalOrKeyword(as_t(t)),
                WrappedParamType::KeywordOnly(t) => ParamType::KeywordOnly(as_t(t)),
                WrappedParamType::Star(WrappedStar::ArbitraryLen(t)) => {
                    ParamType::Star(StarParamType::ArbitraryLen(as_t(t)))
                }
                WrappedParamType::Star(WrappedStar::UnpackedTuple(t)) => {
                    let Type::Tuple(tup) = as_type(&Type::Tuple(t)) else {
                        unreachable!()
                    };
                    ParamType::Star(match &tup.args {
                        TupleArgs::ArbitraryLen(_) => {
                            let TupleArgs::ArbitraryLen(t) = rc_unwrap_or_clone(tup).args else {
                                unreachable!()
                            };
                            StarParamType::ArbitraryLen(*t)
                        }
                        _ => StarParamType::UnpackedTuple(tup),
                    })
                }
                WrappedParamType::Star(WrappedStar::ParamSpecArgs(u1)) => {
                    match params.peek().map(|p| p.specific(i_s.db)) {
                        Some(WrappedParamType::StarStar(WrappedStarStar::ParamSpecKwargs(u2)))
                            if u1 == u2 =>
                        {
                            had_param_spec_args = true;
                            continue;
                        }
                        _ => todo!(),
                    }
                }
                WrappedParamType::StarStar(WrappedStarStar::ValueType(t)) => {
                    ParamType::StarStar(StarStarParamType::ValueType(as_t(t)))
                }
                WrappedParamType::StarStar(WrappedStarStar::UnpackTypedDict(u)) => {
                    ParamType::StarStar(StarStarParamType::UnpackTypedDict(u))
                }
                WrappedParamType::StarStar(WrappedStarStar::ParamSpecKwargs(u)) => {
                    if !had_param_spec_args {
                        todo!()
                    }
                    return return_result(self.remap_param_spec(i_s, new_params, u));
                }
            };
            new_params.push(CallableParam {
                type_: param_specific,
                has_default: p.has_default(),
                name: Some({
                    let n = p.param.name_definition();
                    StringSlice::new(file_index, n.start(), n.end()).into()
                }),
            });
        }
        return_result(CallableParams::Simple(Rc::from(new_params)))
    }

    fn as_callable_content_internal(
        &self,
        type_vars: TypeVarLikes,
        params: CallableParams,
        had_first_self_or_class_annotation: bool,
        return_type: Type,
    ) -> CallableContent {
        CallableContent {
            name: Some(DbString::StringSlice(self.name_string_slice())),
            class_name: self.class.map(|c| c.name_string_slice()),
            defined_at: self.node_ref.as_link(),
            // The actual kind is set by using the decorated() function.
            kind: FunctionKind::Function {
                had_first_self_or_class_annotation,
            },
            guard: None,
            is_abstract: false,
            is_final: false,
            params,
            type_vars,
            return_type,
            no_type_check: false,
        }
    }

    pub fn name_string_slice(&self) -> StringSlice {
        let name = self.node().name();
        StringSlice::new(self.node_ref.file_index(), name.start(), name.end())
    }

    pub fn iter_params(&self) -> impl Iterator<Item = FunctionParam<'a>> {
        self.node().params().iter().map(|param| FunctionParam {
            file: self.node_ref.file,
            param,
        })
    }

    pub fn first_param_annotation_type(&self, i_s: &InferenceState<'db, '_>) -> Option<Cow<Type>> {
        self.iter_params().next().and_then(|p| p.annotation(i_s.db))
    }

    pub(super) fn execute_internal(
        &self,
        i_s: &InferenceState<'db, '_>,
        args: &dyn Args<'db>,
        skip_first_argument: bool,
        on_type_error: OnTypeError,
        replace_self_type: ReplaceSelf,
        result_context: &mut ResultContext,
    ) -> Inferred {
        let return_annotation = self.return_annotation();
        let calculated_type_vars = calculate_function_type_vars_and_return(
            i_s,
            *self,
            args.iter(),
            |issue| args.add_issue(i_s, issue),
            skip_first_argument,
            self.type_vars(i_s),
            self.node_ref.as_link(),
            replace_self_type,
            result_context,
            Some(on_type_error),
        );
        let result = if let Some(return_annotation) = return_annotation {
            self.apply_type_args_in_return_annotation_and_maybe_mark_unreachable(
                i_s,
                calculated_type_vars,
                replace_self_type,
                return_annotation,
                args,
                result_context,
            )
        } else {
            if args
                .as_node_ref()
                .is_some_and(|n| n.file.flags(i_s.db).disallow_untyped_calls)
                && !self.is_typed()
            {
                args.add_issue(
                    i_s,
                    IssueKind::CallToUntypedFunction {
                        name: self.name().into(),
                    },
                )
            }
            self.execute_without_annotation(i_s, args)
        };
        if self.is_async() && !self.is_generator() {
            return Inferred::from_type(new_class!(
                i_s.db.python_state.coroutine_link(),
                Type::Any(AnyCause::Todo),
                Type::Any(AnyCause::Todo),
                result.as_type(i_s),
            ));
        }
        result
    }

    fn apply_type_args_in_return_annotation_and_maybe_mark_unreachable(
        &self,
        i_s: &InferenceState<'db, '_>,
        calculated_type_vars: CalculatedTypeArgs,
        replace_self_type: ReplaceSelf,
        return_annotation: ReturnAnnotation,
        args: &dyn Args<'db>,
        result_context: &mut ResultContext,
    ) -> Inferred {
        let return_type = self
            .node_ref
            .file
            .inference(i_s)
            .use_cached_return_annotation_type(return_annotation);

        if matches!(return_type.as_ref(), Type::Never(_)) && !self.is_async() {
            FLOW_ANALYSIS.with(|fa| fa.mark_current_frame_unreachable())
        }

        if result_context.expect_not_none(i_s)
            && matches!(return_type.as_ref(), Type::None)
            && !self.is_async()
        {
            args.add_issue(
                i_s,
                IssueKind::DoesNotReturnAValue(self.diagnostic_string().into()),
            );
            return Inferred::new_any_from_error();
        }
        // We check first if type vars are involved, because if they aren't we can reuse the
        // annotation expression cache instead of recalculating.
        if NodeRef::new(self.node_ref.file, return_annotation.index())
            .point()
            .maybe_specific()
            == Some(Specific::AnnotationOrTypeCommentWithTypeVars)
        {
            debug!(
                "Inferring generics for {}{}",
                self.class
                    .map(|c| format!("{}.", c.format_short(i_s.db)))
                    .unwrap_or_else(|| "".to_owned()),
                self.name()
            );
            calculated_type_vars.into_return_type(
                i_s,
                &return_type,
                self.class.as_ref(),
                replace_self_type,
            )
        } else {
            self.node_ref
                .file
                .inference(i_s)
                .use_cached_return_annotation(return_annotation)
        }
    }

    pub fn diagnostic_string(&self) -> String {
        let name = self.name();
        match self.class {
            Some(class) => {
                format!("{:?} of {:?}", name, class.name())
            }
            None => format!("{:?}", name),
        }
    }

    pub fn return_type(&self, i_s: &InferenceState<'db, '_>) -> Cow<'a, Type> {
        self.return_annotation()
            .map(|a| {
                self.node_ref
                    .file
                    .inference(i_s)
                    .use_cached_return_annotation_type(a)
            })
            .unwrap_or_else(|| Cow::Borrowed(&Type::Any(AnyCause::Unannotated)))
    }

    pub fn expected_return_type_for_return_stmt(
        &self,
        i_s: &InferenceState<'db, '_>,
    ) -> Cow<'a, Type> {
        let mut t = self.return_type(i_s);
        if self.is_generator() {
            t = Cow::Owned(
                GeneratorType::from_type(i_s.db, t)
                    .map(|g| g.return_type.unwrap_or(Type::None))
                    .unwrap_or(Type::Any(AnyCause::Todo)),
            );
        }
        t
    }

    pub(crate) fn execute(
        &self,
        i_s: &InferenceState<'db, '_>,
        args: &dyn Args<'db>,
        result_context: &mut ResultContext,
        on_type_error: OnTypeError,
    ) -> Inferred {
        if let Some(class) = &self.class {
            self.execute_internal(
                &i_s.with_class_context(class),
                args,
                false,
                on_type_error,
                &|| class.as_type(i_s.db),
                result_context,
            )
        } else {
            self.execute_internal(
                i_s,
                args,
                false,
                on_type_error,
                &|| Type::Self_,
                result_context,
            )
        }
    }

    pub fn lookup(
        &self,
        i_s: &InferenceState,
        node_ref: Option<NodeRef>,
        name: &str,
    ) -> LookupResult {
        debug!("TODO Function lookup");
        LookupResult::None
    }

    pub fn qualified_name(&self, db: &'a Database) -> String {
        format!("{}.{}", self.node_ref.file.qualified_name(db), self.name())
    }

    pub fn name(&self) -> &str {
        let func = FunctionDef::by_index(&self.node_ref.file.tree, self.node_ref.node_index);
        func.name().as_str()
    }
}

#[derive(Copy, Clone)]
pub enum FirstParamProperties<'a> {
    Skip {
        to_self_instance: &'a dyn Fn() -> Type,
    },
    MethodAccessedOnClass,
    None,
}

pub struct AsCallableOptions<'a> {
    first_param: FirstParamProperties<'a>,
    return_type: Cow<'a, Type>,
}

pub struct ReturnOrYieldIterator<'a> {
    file: &'a PythonFile,
    next_node_index: NodeIndex,
}

impl<'a> Iterator for ReturnOrYieldIterator<'a> {
    type Item = ReturnOrYield<'a>;
    fn next(&mut self) -> Option<Self::Item> {
        if self.next_node_index == 0 {
            None
        } else {
            let point = self.file.points.get(self.next_node_index);
            let index = self.next_node_index;
            self.next_node_index = point.node_index();
            // - 1 because the index points to the next yield/return literal. The parent of those
            // literals are then `return_stmt` and `yield_expr` terminals.
            Some(ReturnOrYield::by_index(&self.file.tree, index - 1))
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct FunctionParam<'x> {
    file: &'x PythonFile,
    param: CSTParam<'x>,
}

impl<'db: 'x, 'x> FunctionParam<'x> {
    fn annotation(&self, db: &'db Database) -> Option<Cow<'x, Type>> {
        self.param
            .annotation()
            .map(|annotation| use_cached_param_annotation_type(db, self.file, annotation))
    }

    pub fn has_default_or_stars(&self, db: &Database) -> bool {
        self.has_default() || matches!(self.kind(db), ParamKind::Star | ParamKind::StarStar)
    }
}

impl<'x> Param<'x> for FunctionParam<'x> {
    fn has_default(&self) -> bool {
        self.param.default().is_some()
    }

    fn name(&self, db: &'x Database) -> Option<&str> {
        Some(self.param.name_definition().as_code())
    }

    fn specific<'db: 'x>(&self, db: &'db Database) -> WrappedParamType<'x> {
        let t = self.annotation(db);

        fn expect_borrowed<'a>(t: &Cow<'a, Type>) -> &'a Type {
            let Cow::Borrowed(t) = t else {
                unreachable!();
            };
            t
        }

        fn dbt<'a>(t: Option<&Cow<'a, Type>>) -> Option<&'a Type> {
            t.map(|t| expect_borrowed(t))
        }

        match self.kind(db) {
            ParamKind::PositionalOnly => WrappedParamType::PositionalOnly(t),
            ParamKind::PositionalOrKeyword => WrappedParamType::PositionalOrKeyword(t),
            ParamKind::KeywordOnly => WrappedParamType::KeywordOnly(t),
            ParamKind::Star => WrappedParamType::Star(match dbt(t.as_ref()) {
                Some(Type::ParamSpecArgs(ref param_spec_usage)) => {
                    WrappedStar::ParamSpecArgs(param_spec_usage)
                }
                _ => match t {
                    Some(t) => {
                        let Type::Tuple(tup) = expect_borrowed(&t) else {
                            unreachable!()
                        };
                        match &tup.args {
                            // This case is handled earlier and functions should also be changed to
                            // callables in that case.
                            TupleArgs::FixedLen(..) => unreachable!(),
                            TupleArgs::ArbitraryLen(t) => {
                                WrappedStar::ArbitraryLen(Some(Cow::Borrowed(t.as_ref())))
                            }
                            TupleArgs::WithUnpack(_) => WrappedStar::UnpackedTuple(tup.clone()),
                        }
                    }
                    None => WrappedStar::ArbitraryLen(None),
                },
            }),
            ParamKind::StarStar => WrappedParamType::StarStar(match dbt(t.as_ref()) {
                Some(Type::ParamSpecKwargs(param_spec_usage)) => {
                    WrappedStarStar::ParamSpecKwargs(param_spec_usage)
                }
                _ => t
                    .map(|t| match expect_borrowed(&t) {
                        Type::Class(GenericClass {
                            link,
                            generics: ClassGenerics::List(generics),
                        }) => {
                            debug_assert_eq!(*link, db.python_state.dict_node_ref().as_link());
                            let GenericItem::TypeArg(t) = &generics[1.into()] else {
                                unreachable!();
                            };
                            WrappedStarStar::ValueType(Some(Cow::Borrowed(t)))
                        }
                        Type::TypedDict(td) => WrappedStarStar::UnpackTypedDict(td.clone()),
                        _ => unreachable!(),
                    })
                    .unwrap_or(WrappedStarStar::ValueType(None)),
            }),
        }
    }

    fn kind(&self, db: &Database) -> ParamKind {
        let mut t = self.param.kind();
        if t == ParamKind::PositionalOrKeyword
            && self.file.flags(db).mypy_compatible
            && is_private(self.param.name_definition().as_code())
        {
            // Mypy treats __ params as positional only
            t = ParamKind::PositionalOnly
        }
        t
    }
}

pub fn is_private(name: &str) -> bool {
    name.starts_with("__") && !name.ends_with("__")
}

fn kind_of_decorators(
    i_s: &InferenceState,
    file: &PythonFile,
    decorated: Decorated,
    had_first_annotation: bool,
) -> FunctionKind {
    for decorator in decorated.decorators().iter() {
        if let InferredDecorator::FunctionKind { kind, .. } =
            infer_decorator_details(i_s, file, decorator, had_first_annotation)
        {
            return kind;
        }
    }
    FunctionKind::Function {
        had_first_self_or_class_annotation: false,
    }
}

fn infer_decorator_details(
    i_s: &InferenceState,
    file: &PythonFile,
    decorator: Decorator,
    had_first_annotation: bool,
) -> InferredDecorator {
    let redirect = file.inference(i_s).infer_decorator(decorator);
    if let Some(saved_link) = redirect.maybe_saved_link() {
        let node_ref = NodeRef::from_link(i_s.db, saved_link);
        if saved_link == i_s.db.python_state.overload_link() {
            return InferredDecorator::Overload;
        }
        if saved_link == i_s.db.python_state.typing_final().as_link() {
            return InferredDecorator::Final;
        }
        if i_s
            .db
            .python_state
            .typing_override()
            .is_some_and(|o| saved_link == o.as_link())
        {
            return InferredDecorator::Override;
        }
        if saved_link == i_s.db.python_state.abstractmethod_link() {
            return InferredDecorator::Abstractmethod;
        }
        // All these cases are classes.
        if let Some(class_def) = node_ref.maybe_class() {
            if saved_link == i_s.db.python_state.classmethod_node_ref().as_link() {
                return InferredDecorator::FunctionKind {
                    kind: FunctionKind::Classmethod {
                        had_first_self_or_class_annotation: had_first_annotation,
                    },
                    is_abstract: false,
                };
            }
            if saved_link == i_s.db.python_state.staticmethod_node_ref().as_link() {
                return InferredDecorator::FunctionKind {
                    kind: FunctionKind::Staticmethod,
                    is_abstract: false,
                };
            }
            let class = Class::from_non_generic_link(i_s.db, saved_link);
            class.node_ref.ensure_cached_class_infos(i_s);
            let is_abstract_property = saved_link == i_s.db.python_state.abstractproperty_link();
            if is_abstract_property
                || class
                    .class_link_in_mro(i_s.db, i_s.db.python_state.property_node_ref().as_link())
            {
                return InferredDecorator::FunctionKind {
                    kind: FunctionKind::Property {
                        had_first_self_or_class_annotation: had_first_annotation,
                        writable: false,
                    },
                    is_abstract: is_abstract_property,
                };
            }
            if class.class_link_in_mro(i_s.db, i_s.db.python_state.cached_property_link()) {
                return InferredDecorator::FunctionKind {
                    kind: FunctionKind::Property {
                        had_first_self_or_class_annotation: had_first_annotation,
                        writable: true,
                    },
                    is_abstract: false,
                };
            }
        }
    }
    InferredDecorator::Inferred(redirect)
}

#[derive(Debug)]
enum InferredDecorator {
    FunctionKind {
        kind: FunctionKind,
        is_abstract: bool,
    },
    Inferred(Inferred),
    Overload,
    Abstractmethod,
    Override,
    Final,
}

struct FunctionDetails {
    inferred: Inferred,
    kind: FunctionKind,
    is_overload: bool,
    has_decorator: bool,
}

enum PropertyModifier {
    JustADecorator,
    Setter,
    Deleter,
}

pub enum FirstParamKind {
    Self_,
    ClassOfSelf,
    InStaticmethod,
}

pub struct GeneratorType {
    pub yield_type: Type,
    pub send_type: Option<Type>,
    pub return_type: Option<Type>,
}

impl GeneratorType {
    pub fn from_type(db: &Database, t: Cow<Type>) -> Option<Self> {
        match t.as_ref() {
            Type::Class(c)
                if c.link == db.python_state.iterator_link()
                    || c.link == db.python_state.iterable_link()
                    || c.link == db.python_state.async_iterator_link()
                    || c.link == db.python_state.async_iterable_link() =>
            {
                Some(GeneratorType {
                    yield_type: c.class(db).nth_type_argument(db, 0),
                    send_type: None,
                    return_type: None,
                })
            }
            Type::Class(c) if c.link == db.python_state.generator_link() => {
                let cls = c.class(db);
                Some(GeneratorType {
                    yield_type: cls.nth_type_argument(db, 0),
                    send_type: Some(cls.nth_type_argument(db, 1)),
                    return_type: Some(cls.nth_type_argument(db, 2)),
                })
            }
            Type::Class(c) if c.link == db.python_state.async_generator_link() => {
                let cls = c.class(db);
                Some(GeneratorType {
                    yield_type: cls.nth_type_argument(db, 0),
                    send_type: Some(cls.nth_type_argument(db, 1)),
                    return_type: None,
                })
            }
            Type::Union(union) => union.iter().fold(None, |a, b| {
                if let Some(b) = Self::from_type(db, Cow::Borrowed(b)) {
                    if let Some(a) = a {
                        let optional_union = |t1: Option<Type>, t2: Option<Type>| {
                            if let Some(t1) = t1 {
                                if let Some(t2) = t2 {
                                    Some(t1.union(t2))
                                } else {
                                    Some(t1)
                                }
                            } else {
                                t2
                            }
                        };
                        Some(Self {
                            yield_type: a.yield_type.union(b.yield_type),
                            // TODO is taking the Union here correct, since its contravariant?
                            send_type: optional_union(a.send_type, b.send_type),
                            return_type: if a.return_type.is_none() && b.return_type.is_none() {
                                None
                            } else {
                                Some(
                                    a.return_type
                                        .unwrap_or(Type::None)
                                        .union(b.return_type.unwrap_or(Type::None)),
                                )
                            },
                        })
                    } else {
                        Some(b)
                    }
                } else {
                    a
                }
            }),
            _ => None,
        }
    }
}
