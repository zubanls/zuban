use std::{borrow::Cow, cell::Cell, fmt, sync::Arc};

use parsa_python_cst::{
    Decorated, Decorator, ExpressionContent, ExpressionPart, Param as CSTParam, ParamIterator,
    ParamKind, PrimaryContent, PrimaryOrAtom, ReturnAnnotation, ReturnOrYield, TrivialBodyState,
    YieldExprContent,
};

use crate::{
    arguments::{Arg, Args, KnownArgs, KnownArgsWithCustomAddIssue},
    database::{
        ComplexPoint, Database, Locality, OverloadDefinition, OverloadImplementation, Point,
        PointLink, Specific,
    },
    debug,
    diagnostics::IssueKind,
    file::{
        DecoratorState, FLOW_ANALYSIS, FuncNodeRef, FuncParent, OtherDefinitionIterator,
        PythonFile, RedefinitionResult, TypeVarCallbackReturn, first_defined_name_of_multi_def,
        on_argument_type_error, use_cached_param_annotation_type,
    },
    format_data::FormatData,
    inference_state::{InferenceState, Mode},
    inferred::Inferred,
    matching::{
        CalculatedTypeArgs, ErrorStrs, OnTypeError, ReplaceSelfInMatcher, calc_func_type_vars,
        calc_untyped_func_type_vars, maybe_class_usage,
    },
    new_class,
    node_ref::NodeRef,
    params::{
        InferrableParamIterator, Param, WrappedParamType, WrappedStar, WrappedStarStar,
        params_have_self_type_after_self,
    },
    python_state::NAME_TO_FUNCTION_DIFF,
    recoverable_error,
    result_context::ResultContext,
    type_::{
        AnyCause, CallableContent, CallableLike, CallableParam, CallableParams, ClassGenerics,
        DataclassTransformObj, DbString, FunctionKind, FunctionOverload, GenericClass, GenericItem,
        NeverCause, ParamType, PropertySetter, PropertySetterType, ReplaceSelf,
        ReplaceTypeVarLikes, StarParamType, StarStarParamType, StringSlice, TupleArgs, Type,
        TypeVarLike, TypeVarLikes, WrongPositionalCount, replace_param_spec,
    },
    type_helpers::Class,
    utils::{debug_indent, is_magic_method},
};

use super::callable::FuncLike;

#[derive(Clone, Copy)]
pub(crate) struct Function<'a, 'class> {
    pub node_ref: FuncNodeRef<'a>,
    pub class: Option<Class<'class>>,
}

impl<'a> std::ops::Deref for Function<'a, '_> {
    type Target = FuncNodeRef<'a>;

    fn deref(&self) -> &Self::Target {
        &self.node_ref
    }
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
    pub fn new(node_ref: NodeRef<'a>, class: Option<Class<'class>>) -> Self {
        Self {
            node_ref: FuncNodeRef::from_node_ref(node_ref),
            class,
        }
    }

    pub fn new_with_unknown_parent(db: &'db Database, node_ref: NodeRef<'a>) -> Self {
        let func_node_ref = FuncNodeRef::from_node_ref(node_ref);
        let class = match func_node_ref.parent(db) {
            FuncParent::Class(c) => Some(c),
            _ => None,
        };
        Self {
            node_ref: func_node_ref,
            class,
        }
    }

    pub fn generator_return(&self, i_s: &InferenceState) -> Option<GeneratorType> {
        self.return_annotation().and_then(|return_annotation| {
            let return_type = self
                .node_ref
                .file
                .name_resolution_for_types(i_s)
                .use_cached_return_annotation_type(return_annotation);
            GeneratorType::from_type(i_s.db, return_type)
        })
    }

    pub fn iter_non_self_args(&self, i_s: &InferenceState) -> ParamIterator<'a> {
        let mut iterator = self.node().params().iter();
        if self.class.is_some() && self.kind(i_s) != FunctionKind::Staticmethod {
            // The param annotation is defined implicitly as Self or Type[Self]
            iterator.next();
        }
        iterator
    }

    pub fn has_param_annotations(&self, i_s: &InferenceState) -> bool {
        self.iter_non_self_args(i_s)
            .any(|p| p.annotation().is_some())
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
        match self.node().trivial_body_state() {
            TrivialBodyState::Known(known) => known,
            TrivialBodyState::RaiseExpr(expr) => {
                match self
                    .node_ref
                    .file
                    .inference(i_s)
                    .infer_expression(expr)
                    .as_cow_type(i_s)
                    .as_ref()
                {
                    Type::Class(cls) => cls.link == i_s.db.python_state.notimplementederror_link(),
                    Type::Type(t) => match t.as_ref() {
                        Type::Class(cls) => {
                            cls.link == i_s.db.python_state.notimplementederror_link()
                        }
                        _ => false,
                    },
                    _ => false,
                }
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

    fn return_without_annotation(
        &self,
        i_s: &InferenceState<'db, '_>,
        return_inf: Inferred,
        calculated: CalculatedTypeArgs,
        replace_self_type: Option<ReplaceSelfInMatcher>,
    ) -> Inferred {
        let ret_t = return_inf.as_cow_type(i_s);
        if ret_t.has_type_vars() || ret_t.has_self_type(i_s.db) {
            calculated.into_return_type(i_s, ret_t.as_ref(), self.class.as_ref(), &|| {
                replace_self_type.map(|replace_self| replace_self())
            })
        } else {
            // If there are no type vars we can just pass the result on.
            return_inf
        }
    }

    fn ensure_cached_untyped_return(&self, i_s: &InferenceState) -> Inferred {
        let had_error = &Cell::new(false);
        let inner_i_s = &i_s
            .with_func_context(self)
            .with_mode(Mode::AvoidErrors { had_error });
        let reference = self.unannotated_return_reference();
        let p = reference.point();
        if p.calculated() {
            return reference.maybe_inferred(inner_i_s).unwrap();
        }
        if p.calculating() {
            return Inferred::new_any_from_error();
        }
        reference.set_point(Point::new_calculating());
        let body_node_ref = NodeRef::new(self.file, self.node().body().index());
        if body_node_ref.point().calculating() {
            // This would also recurse, because we are already calculating the function's results
            return Inferred::new_any_from_error();
        }
        let _indent = debug_indent();
        debug!("Ensure cached untyped return for func {}", self.name());
        let result = self
            .node_ref
            .file
            .inference(&InferenceState::new(i_s.db, self.node_ref.file))
            .ensure_calculated_function_body(*self);
        debug_assert!(result.is_ok());

        debug!("Checking cached untyped return for func {}", self.name());
        let inference = self.node_ref.file.inference(inner_i_s);
        let mut generator: Option<Inferred> = None;
        let mut result: Option<Inferred> = None;
        for return_or_yield in self.iter_return_or_yield() {
            match return_or_yield {
                ReturnOrYield::Return(ret) => {
                    let inf = if let Some(star_expressions) = ret.star_expressions() {
                        inference.infer_star_expressions(
                            star_expressions,
                            &mut ResultContext::ValueExpected,
                        )
                    } else {
                        Inferred::new_none()
                    };
                    result = Some(if let Some(r) = result {
                        inf.simplified_union(inner_i_s, r)
                    } else {
                        inf
                    });
                }
                ReturnOrYield::Yield(yield_expr) => {
                    let inf = match yield_expr.unpack() {
                        YieldExprContent::StarExpressions(s) => {
                            inference.infer_star_expressions(s, &mut ResultContext::ValueExpected)
                        }
                        YieldExprContent::YieldFrom(yield_from) => {
                            inference.infer_yield_from_expr(yield_from)
                        }
                        YieldExprContent::None => Inferred::new_none(),
                    };
                    generator = Some(if let Some(g) = generator {
                        inf.simplified_union(inner_i_s, g)
                    } else {
                        inf
                    });
                }
            }
        }
        if let Some(result) = &mut result {
            let t = result.as_cow_type(i_s);
            if matches!(t.as_ref(), Type::None) && self.class.is_some() {
                // When an untyped method returns None, it typically means that a subclass will
                // return None | Any.
                *result = Inferred::from_type(Type::ERROR.union(Type::None))
            } else if body_node_ref.point().specific() != Specific::FunctionEndIsUnreachable {
                // None can be an implicit return
                *result = Inferred::from_type(result.as_type(i_s).union(Type::None))
            }
        }
        let needs_async_remap = if let Some(generator) = generator {
            let t = generator
                .as_type(i_s)
                .make_generator_type(i_s.db, self.is_async(), || {
                    if let Some(result) = result {
                        result
                            .as_type(i_s)
                            .simplified_union(i_s, &Type::Any(AnyCause::Todo))
                    } else {
                        Type::Any(AnyCause::Todo)
                    }
                });
            result = Some(Inferred::from_type(t));
            false
        } else {
            self.is_async()
        };

        if let Some(result) = &mut result {
            let t = result.as_cow_type(i_s);
            if let Some(new) = t.replace_any_with_unknown_type_params_with_any() {
                *result = Inferred::from_type(new)
            }
        }

        let mut result = result
            .unwrap_or_else(|| {
                if body_node_ref.point().specific() == Specific::FunctionEndIsUnreachable {
                    if self.class.is_some() {
                        // Untyped methods may be overwritten in subclasses, it is very common to
                        // return raise NotImplemented in some super classes.
                        Inferred::new_any_from_error()
                    } else {
                        Inferred::new_never(NeverCause::Other)
                    }
                } else {
                    Inferred::new_none()
                }
            })
            .into_proper_type(i_s);
        if needs_async_remap {
            result = Inferred::from_type(new_class!(
                i_s.db.python_state.coroutine_link(),
                Type::Any(AnyCause::Todo),
                Type::Any(AnyCause::Todo),
                result.as_type(i_s),
            ))
        }
        result.save_redirect(i_s, reference.file, reference.node_index)
    }

    pub fn parent_class(&self, db: &'db Database) -> Option<Class<'class>> {
        if let Some(cls) = self.class {
            return Some(cls);
        }
        match self.parent(db) {
            FuncParent::Module => None,
            FuncParent::Function(func) => func.parent_class(db),
            FuncParent::Class(_) => {
                // Handled above
                recoverable_error!("The class of the func is not set");
                None
            }
        }
    }

    pub(crate) fn find_type_var_like_including_ancestors(
        &self,
        db: &Database,
        type_var: &TypeVarLike,
        class_seen: bool,
    ) -> Option<TypeVarCallbackReturn> {
        if let Some(tvl) = self.type_vars(db).find(type_var, self.node_ref.as_link()) {
            return Some(TypeVarCallbackReturn::TypeVarLike(tvl));
        }
        match self.parent(db) {
            FuncParent::Module => None,
            FuncParent::Function(func) => {
                func.find_type_var_like_including_ancestors(db, type_var, class_seen)
            }
            FuncParent::Class(c) => {
                c.find_type_var_like_including_ancestors(db, type_var, class_seen)
            }
        }
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
            if guard.from_type_is
                && let Some(param) = first_param
                && let Some(annotation) = param.annotation()
            {
                let annotation_t =
                    use_cached_param_annotation_type(i_s.db, self.node_ref.file, annotation);
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

    pub fn ensure_cached_func(&self, i_s: &InferenceState<'db, '_>) {
        if self.node_ref.point().calculated() {
            return;
        }
        let maybe_decorated = self.node().maybe_decorated();
        let mut no_type_check = false;
        if let Some(decorated) = maybe_decorated {
            no_type_check = self
                .node_ref
                .file
                .inference(i_s)
                .is_no_type_check(decorated);
        }
        if self.node_ref.point().calculated() {
            return;
        }
        let maybe_computed = if no_type_check {
            None
        } else {
            self.ensure_cached_type_vars(i_s)
        };
        if let Some(decorated) = maybe_decorated {
            if let Some(class) = self.class {
                let class = Class::with_self_generics(i_s.db, class.node_ref);
                Self::new(self.node_ref.into(), Some(class)).decorated_to_be_saved(
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
            self.node_ref
                .insert_type(Type::Callable(Arc::new(callable_t)));
        } else {
            self.node_ref
                .set_point(Point::new_specific(Specific::Function, Locality::Todo));
        }
    }

    fn ensure_cached_type_vars(&self, i_s: &InferenceState<'db, '_>) -> Option<CallableContent> {
        let (type_guard, star_annotation) = self
            .node_ref
            .ensure_cached_type_vars(i_s, self.class.map(|c| c.node_ref))?;
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

        // Make sure the callable is created for private names, because they are a bit special.
        needs_callable |= self
            .node()
            .params()
            .iter()
            .any(|param| is_private(param.name_def().as_code()));

        if needs_callable || type_guard.is_some() {
            let options = AsCallableOptions {
                first_param: FirstParamProperties::None,
                return_type: match type_guard.as_ref() {
                    Some(_) => Cow::Owned(i_s.db.python_state.bool_type()),
                    None => self.node_ref.return_type(i_s),
                },
            };
            let mut callable = self.as_callable_with_options(i_s, options);
            callable.guard = type_guard;
            return Some(callable);
        }
        None
    }

    pub fn cache_func_from_diagnostics(&self, i_s: &InferenceState) {
        self.cache_func_with_name_def(
            i_s,
            NodeRef::new(self.node_ref.file, self.node().name_def().index()),
            true,
        )
    }

    pub fn cache_func_with_name_def(
        &self,
        i_s: &InferenceState,
        name_def: NodeRef,
        from_diagnostics: bool,
    ) {
        if !name_def.point().calculated() {
            name_def.set_point(Point::new_calculating());
            if !from_diagnostics && self.needs_flow_analysis_for_decorators(i_s) {
                name_def.set_point(Point::new_uncalculated());
                let result = self.file.ensure_module_symbols_flow_analysis(i_s.db);
                // Some cycle
                if result.is_err() {
                    name_def.set_point(Point::new_calculating());
                }
            }
            self.ensure_cached_func(i_s);
            if name_def.point().calculated() {
                // This can happen with recursions while calculating the decorators
                return;
            }
            name_def.set_point(Point::new_redirect(
                self.node_ref.file_index(),
                self.node_ref.node_index,
                Locality::Todo,
            ));
            if self.node_ref.point().maybe_specific() != Some(Specific::OverloadUnreachable) {
                let inference = name_def.file.inference(i_s);
                if inference.in_conditional() {
                    self.check_conditional_function_definition(i_s)
                } else if first_defined_name_of_multi_def(
                    self.node_ref.file,
                    name_def.name_ref_of_name_def().node_index,
                )
                .is_some()
                {
                    inference.check_for_redefinition(name_def, |issue| {
                        self.add_issue_onto_start_including_decorator(i_s, issue)
                    });
                } else {
                    inference.add_initial_name_definition(name_def.expect_name_def())
                }
            }
        }
    }

    fn needs_flow_analysis_for_decorators(&self, i_s: &InferenceState) -> bool {
        let node = self.node();
        let Some(decorated) = node.maybe_decorated() else {
            return false;
        };
        for dec in decorated.decorators().iter() {
            match self
                .file
                .name_resolution_for_types(i_s)
                .decorator_without_need_for_flow_analysis(dec)
            {
                Some(DecoratorState::NodeRef(node_ref)) => {
                    if !node_ref.point().calculated() {
                        NodeRef::new(self.file, dec.index()).set_point(Point::new_redirect(
                            node_ref.file_index(),
                            node_ref.node_index,
                            Locality::Todo,
                        ))
                    }
                }
                Some(DecoratorState::Calculating) => return false,
                None => return true,
            }
        }
        let current_index = node.name().index();
        let p = NodeRef::new(self.file, current_index).point();
        debug_assert!(matches!(
            p.specific(),
            Specific::FirstNameOfNameDef | Specific::NameOfNameDef
        ));
        let next_index = p.node_index();
        if next_index > current_index
            && let Some(next_func) = NodeRef::new(self.file, next_index).maybe_name_of_function()
        {
            Self::new(NodeRef::new(self.file, next_func.index()), self.class)
                .needs_flow_analysis_for_decorators(i_s)
        } else {
            false
        }
    }

    fn check_conditional_function_definition(&self, i_s: &InferenceState) {
        let node = self.node();
        let Some(first) = first_defined_name_of_multi_def(self.node_ref.file, node.name().index())
        else {
            return;
        };
        // At this point we know it's a conditional redefinition and not just a singular def in an
        // if.
        let inference = self.node_ref.file.inference(i_s);
        let original = inference.infer_name_of_definition_by_index(first);
        let original_t = original.as_cow_type(i_s);
        let redefinition = inference
            .check_point_cache(self.node_ref.node_index)
            .unwrap();

        let redefinition_t = redefinition.as_cow_type(i_s);
        inference.narrow_or_widen_name_target(
            PointLink::new(self.node_ref.file_index(), first),
            &original_t,
            &redefinition_t,
            // This checks whether there is an error or not
            || {
                let mut had_error = false;
                if node.maybe_decorated().is_none()
                    && NodeRef::new(self.node_ref.file, first)
                        .maybe_name_of_function()
                        .is_some_and(|func| func.maybe_decorated().is_none())
                {
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
                        had_error = true;
                        self.add_issue_for_declaration(
                            i_s,
                            IssueKind::IncompatibleConditionalFunctionSignaturePretty {
                                original: original.format_pretty(&FormatData::new_short(i_s.db)),
                                redefinition: redefinition
                                    .format_pretty(&FormatData::new_short(i_s.db)),
                            },
                        );
                    }
                } else {
                    original_t.error_if_not_matches(
                        i_s,
                        &Inferred::from_type(redefinition_t.as_ref().clone()),
                        |issue| self.add_issue_for_declaration(i_s, issue),
                        |error_types| {
                            had_error = true;
                            let ErrorStrs { expected, got } = error_types.as_boxed_strs(i_s.db);
                            Some(IssueKind::IncompatibleConditionalFunctionSignature {
                                original: expected,
                                redefinition: got,
                            })
                        },
                    )
                }
                RedefinitionResult::TypeMismatch(had_error)
            },
        );
    }

    pub fn is_dunder_new(&self) -> bool {
        self.class.is_some() && self.name() == "__new__"
    }

    pub fn first_param_kind(&self, i_s: &InferenceState) -> FirstParamKind {
        if self.class.is_some()
            && ["__new__", "__init_subclass__", "__class_getitem__"].contains(&self.name())
        {
            return FirstParamKind::ClassOfSelf;
        }
        if self.node_ref.point().calculated() {
            match self.kind(i_s) {
                FunctionKind::Function { .. } | FunctionKind::Property { .. } => {
                    FirstParamKind::Self_
                }
                FunctionKind::Classmethod { .. } => FirstParamKind::ClassOfSelf,
                FunctionKind::Staticmethod => FirstParamKind::InStaticmethod,
            }
        } else {
            // When inferring params while inferring the return type, the function might not yet
            // be defined. In that case simply check for static/classmethods
            if self.class.is_some()
                && let Some(decorated) = self.node().maybe_decorated()
            {
                for decorator in decorated.decorators().iter() {
                    let inf = self.file.inference(i_s).infer_decorator(decorator);
                    if let Some(saved_link) = inf.maybe_saved_link() {
                        if saved_link == i_s.db.python_state.classmethod_node_ref().as_link() {
                            return FirstParamKind::ClassOfSelf;
                        }
                        if saved_link == i_s.db.python_state.staticmethod_node_ref().as_link() {
                            return FirstParamKind::InStaticmethod;
                        }
                    }
                }
            }
            FirstParamKind::Self_
        }
    }

    pub fn kind(&self, i_s: &InferenceState) -> FunctionKind {
        if self.class.is_none() {
            return FunctionKind::Function {
                had_first_self_or_class_annotation: true,
            };
        }
        let node = self.node();
        let had_first_self_or_class_annotation = node
            .params()
            .iter()
            .next()
            .is_some_and(|p| p.annotation().is_some());

        match self.node_ref.maybe_complex() {
            Some(ComplexPoint::TypeInstance(Type::Callable(c))) => c.kind.clone(),
            Some(ComplexPoint::FunctionOverload(o)) => o.kind().clone(),
            Some(_) => {
                // We have a type, probably an instance and we need to recheck if it was mapped by
                // a classmethod or not.
                if let Some(decorated) = self.node().maybe_decorated() {
                    for dec in decorated.decorators().iter() {
                        if let InferredDecorator::FunctionKind { kind, .. } =
                            infer_decorator_details(
                                i_s,
                                self.node_ref.file,
                                dec,
                                had_first_self_or_class_annotation,
                            )
                        {
                            return kind;
                        }
                    }
                }
                FunctionKind::Function {
                    had_first_self_or_class_annotation,
                }
            }
            _ => {
                if let Some(original_func) = self.original_func_for_overload() {
                    if let Some(ComplexPoint::FunctionOverload(o)) = original_func.maybe_complex() {
                        for c in o.functions.iter_functions() {
                            if c.defined_at == self.node_ref.as_link() {
                                return c.kind.clone();
                            }
                        }
                        if let Some(implementation) = &o.implementation
                            && implementation.callable.defined_at == self.node_ref.as_link()
                        {
                            return implementation.callable.kind.clone();
                        }
                    }
                    Function::new(original_func, self.class).kind(i_s)
                } else {
                    FunctionKind::Function {
                        had_first_self_or_class_annotation,
                    }
                }
            }
        }
    }

    pub fn original_func_for_overload(&self) -> Option<NodeRef<'a>> {
        let is_ov_unreachable =
            |p: Point| p.maybe_specific() == Some(Specific::OverloadUnreachable);
        if is_ov_unreachable(self.node_ref.point()) {
            let mut pre_unreachable = self.node_ref.node_index;
            let current_index = pre_unreachable + NAME_TO_FUNCTION_DIFF;
            let file = self.node_ref.file;
            // Find the method before the unreachable method
            // Previously we just used the first name, but that might just be a different
            // definition.
            for n in OtherDefinitionIterator::new(&file.points, current_index) {
                let n_def = n - NAME_TO_FUNCTION_DIFF;
                let new_p = file.points.get(n_def);
                if new_p.calculated() && !is_ov_unreachable(new_p) {
                    pre_unreachable = n_def;
                }
            }
            debug_assert_ne!(pre_unreachable, current_index - NAME_TO_FUNCTION_DIFF);
            Some(NodeRef::new(self.node_ref.file, pre_unreachable))
        } else {
            None
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
                        WrongPositionalCount::TooMany => self
                            .add_issue_onto_start_including_decorator(
                                i_s,
                                IssueKind::TooManyArguments(" for property".into()),
                            ),
                        // IssueType::MethodWithoutArguments will be checked and added later.
                        WrongPositionalCount::TooFew => (),
                    }
                    return Inferred::new_any_from_error();
                }
                // Make sure the old Arc count is decreased, so we can use it mutable without cloning.
                drop(details);
                self.calculate_property_setter_and_deleter(
                    i_s,
                    Arc::make_mut(&mut callable),
                    had_first_annotation,
                );
                Inferred::from_type(Type::Callable(callable))
            }
            _ => details.inferred,
        }
    }

    fn calculate_decorated_function_details(
        &self,
        i_s: &InferenceState,
        decorated: Decorated,
        base_t: Option<CallableContent>,
    ) -> Option<FunctionDetails> {
        let used_with_a_non_method = |name| {
            self.add_issue_onto_start_including_decorator(
                i_s,
                IssueKind::UsedWithANonMethod { name },
            )
        };

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
        let mut is_override = false;
        let mut no_type_check = false;
        let mut deprecated = None;
        let mut dataclass_transform = None;
        let mut inferred_decs = vec![];
        let mut return_any_because_untyped = false;
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
                    if self.node_ref.file.flags(i_s.db).disallow_untyped_decorators {
                        let is_typed = |inf: &Inferred, skip_first_param| {
                            let t = inf.as_cow_type(i_s);
                            if matches!(t.as_ref(), Type::Any(_)) {
                                return false;
                            }
                            t.maybe_callable(i_s)
                                .map(|c| {
                                    if i_s.db.mypy_compatible() {
                                        c.is_typed(skip_first_param)
                                    } else {
                                        // Decorators that don't have a return annotation are
                                        // not really typed and we should report that as
                                        // an error.
                                        c.is_typed_and_annotated_result(i_s.db)
                                    }
                                })
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
                    inferred_decs.push((decorator.index(), dec_inf));
                }
                InferredDecorator::UntypedDecorator => {
                    if self.is_typed() {
                        nr().add_issue(
                            i_s,
                            IssueKind::UntypedDecorator {
                                name: self.name().into(),
                            },
                        );
                    }
                    return_any_because_untyped = true;
                }
                InferredDecorator::Overload => is_overload = true,
                InferredDecorator::Abstractmethod => is_abstract = true,
                InferredDecorator::Final => {
                    if self.class.is_none() {
                        nr().add_issue(i_s, IssueKind::FinalCanOnlyBeUsedInMethods);
                    }
                    is_final = true
                }
                InferredDecorator::Override => {
                    is_override = true;
                    if self.class.is_none() {
                        used_with_a_non_method("override")
                    }
                }
                InferredDecorator::DataclassTransform(transform) => {
                    dataclass_transform = Some(transform);
                }
                InferredDecorator::NoTypeCheck => no_type_check = true,
                InferredDecorator::Deprecated(reason) => deprecated = Some(reason),
            }
        }
        let mut c = base_t.map(|c| c).unwrap_or_else(|| {
            if no_type_check {
                self.as_no_type_check_callable(i_s.db)
            } else if is_overload {
                self.as_callable_without_inferring_return_type(i_s, FirstParamProperties::None)
            } else {
                if return_any_because_untyped {
                    self.as_callable_with_options(
                        i_s,
                        AsCallableOptions {
                            first_param: FirstParamProperties::None,
                            return_type: self.inferred_return_type(i_s),
                        },
                    )
                } else {
                    self.as_callable(i_s, FirstParamProperties::None)
                }
            }
        });
        if return_any_because_untyped {
            c.return_type = Type::Any(AnyCause::Unannotated)
        }
        let mut inferred = Inferred::from_type(Type::Callable(Arc::new(c)));
        if !return_any_because_untyped {
            for (decorator_index, inferred_dec) in inferred_decs {
                let nr = NodeRef::new(self.node_ref.file, decorator_index);
                inferred = inferred_dec.execute_with_details(
                    i_s,
                    &KnownArgs::new(&inferred, nr),
                    &mut ResultContext::Unknown,
                    OnTypeError::new(&on_argument_type_error),
                );
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
            used_with_a_non_method("abstractmethod")
        }
        let overwrite_callable = |inferred: &mut _, mut callable: CallableContent| {
            callable.name = Some(DbString::StringSlice(self.name_string_slice()));
            callable.class_name = self.class.map(|c| c.name_string_slice());
            callable.kind = kind.clone();
            callable.is_abstract = is_abstract;
            callable.is_final = is_final;
            callable.deprecated_reason = deprecated;
            if no_type_check {
                callable.set_all_types_to_any_for_no_type_check(AnyCause::Explicit);
            }
            self.avoid_invalid_typeguard_signatures(i_s, &mut callable);
            *inferred = Inferred::from_type(Type::Callable(Arc::new(callable)));
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
            is_override,
            dataclass_transform,
            has_decorator: true,
        })
    }

    fn calculate_property_setter_and_deleter(
        &self,
        i_s: &InferenceState,
        callable: &mut CallableContent,
        had_first_annotation: bool,
    ) {
        let is_property_modifier = |decorator: Decorator, next_func: Self| {
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
                "setter" => {
                    let setter = if let Some(first_non_self_param) = next_func.iter_params().nth(1)
                    {
                        first_non_self_param.annotation_or_any(i_s.db).into_owned()
                    } else {
                        next_func.add_issue_for_declaration(
                            i_s,
                            IssueKind::InvalidPropertySetterSignature,
                        );
                        Type::ERROR
                    };
                    PropertyModifier::Setter(Arc::new(PropertySetter {
                        type_: PropertySetterType::OtherType(setter),
                        deprecated_reason: None,
                    }))
                }
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
            debug_assert!(point.is_name_of_name_def_like(), "{point:?}");
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
            next_func.ensure_cached_type_vars(i_s);

            // Make sure this is not calculated again.
            next_func.node_ref.set_point(Point::new_specific(
                Specific::OverloadUnreachable,
                Locality::File,
            ));

            let mut iterator = decorated.decorators().iter();
            let decorator = iterator.next().unwrap();
            match is_property_modifier(decorator, next_func) {
                PropertyModifier::JustADecorator => {
                    NodeRef::new(file, decorator.index()).add_issue(
                        i_s,
                        IssueKind::OnlySupportedTopDecoratorSetter {
                            name: self.name().into(),
                        },
                    );
                }
                PropertyModifier::Setter(mut setter_type) => {
                    for dec in iterator {
                        if let InferredDecorator::Deprecated(deprecated_reason) =
                            infer_decorator_details(i_s, file, dec, true)
                        {
                            setter_type = Arc::new(PropertySetter {
                                deprecated_reason: Some(deprecated_reason),
                                ..setter_type.as_ref().clone()
                            });
                        }
                    }
                    callable.kind = FunctionKind::Property {
                        had_first_self_or_class_annotation: had_first_annotation,
                        setter_type: Some(setter_type),
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

        let mut has_abstract = false;
        let mut has_non_abstract = false;
        let mut is_override = details.is_override;
        let mut dataclass_transform = details.dataclass_transform;
        let should_error_out = Cell::new(false);
        let add_issue_for_decorators_in_wrong_positions = |func: &Function, is_first: bool| {
            if !(in_stub && is_first) {
                for decorator in func.node().maybe_decorated().unwrap().decorators().iter() {
                    let add = |kind| {
                        NodeRef::new(func.node_ref.file, decorator.index()).add_issue(
                            i_s,
                            match in_stub {
                                false => {
                                    IssueKind::ShouldBeAppliedOnlyToOverloadImplementation { kind }
                                }
                                true => IssueKind::InStubMustBeAppliedToFirstOverload { kind },
                            },
                        )
                    };
                    match infer_decorator_details(i_s, func.node_ref.file, decorator, true) {
                        InferredDecorator::Final => add("final"),
                        InferredDecorator::Override if !i_s.db.mypy_compatible() => add("override"),
                        _ => (),
                    }
                }
            }
        };
        let mut add_func = |func: &Function, inf: Inferred, is_first: bool, is_override| {
            let base = inf.as_cow_type(i_s);
            if let Some(CallableLike::Callable(callable)) = base.maybe_callable(i_s) {
                if callable.is_final || is_override {
                    add_issue_for_decorators_in_wrong_positions(func, is_first)
                }
                if callable.is_abstract {
                    has_abstract = true;
                } else {
                    has_non_abstract = true;
                }
                functions.push(callable)
            } else {
                func.add_issue_onto_start_including_decorator(
                    i_s,
                    IssueKind::NotCallable {
                        type_: format!("\"{}\"", base.format_short(i_s.db)).into(),
                    },
                );
                should_error_out.set(true);
            }
        };
        let mut inconsistent_function_kind = None;
        add_func(self, details.inferred, true, details.is_override);
        let mut implementation: Option<OverloadImplementation> = None;
        loop {
            let point = file.points.get(current_name_index);
            if !point.calculated() {
                break;
            }
            debug_assert!(point.is_name_of_name_def_like(), "{point:?}");
            current_name_index = point.node_index();
            if current_name_index <= first_index {
                break;
            }
            let func_ref = NodeRef::new(file, current_name_index - NAME_TO_FUNCTION_DIFF);
            let Some(next_func_def) = func_ref.maybe_function() else {
                // This is a statement like foo = 3, which is essentially a redefinition of the
                // overload as an int
                break;
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
                        should_error_out.set(true);
                        next_func.node_ref.set_point(Point::new_specific(
                            Specific::OverloadUnreachable,
                            Locality::File,
                        ));
                        continue;
                    }
                    FunctionDetails {
                        inferred: Inferred::from_type(
                            next_func.as_type_without_inferring_return_type(
                                i_s,
                                FirstParamProperties::None,
                            ),
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
                        is_override: false,
                        dataclass_transform: None,
                        has_decorator: false,
                    }
                }
            };
            is_override |= next_details.is_override;

            if !details.kind.is_same_base_kind(&next_details.kind) {
                if matches!(details.kind, FunctionKind::Function { .. }) {
                    inconsistent_function_kind = Some(next_details.kind.clone())
                } else {
                    inconsistent_function_kind = Some(details.kind.clone())
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
                add_func(
                    &next_func,
                    next_details.inferred,
                    false,
                    next_details.is_override,
                )
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
                            callable: Arc::unwrap_or_clone(callable),
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
                        next_func.add_issue_onto_start_including_decorator(
                            i_s,
                            IssueKind::NotCallable {
                                type_: format!("\"{}\"", t.format_short(i_s.db)).into(),
                            },
                        )
                    }
                }
            }
            if next_details.dataclass_transform.is_some() {
                // TODO PEP 681 says: If the function has overloads, the dataclass_transform decorator
                // can be applied to the implementation of the function or any one, but not more than
                // one, of the overloads.
                // We whould therefore add an error here
                dataclass_transform = next_details.dataclass_transform;
            }
        }
        let name_def_node_ref = |link| {
            let node_ref = NodeRef::from_link(i_s.db, link);
            let name_def = node_ref.maybe_function().unwrap().name_def();
            NodeRef::new(node_ref.file, name_def.index())
        };
        if let Some(kind) = inconsistent_function_kind {
            let kind = match kind {
                FunctionKind::Classmethod { .. } => "classmethod",
                FunctionKind::Staticmethod => "staticmethod",
                FunctionKind::Property { .. } => "property",
                FunctionKind::Function { .. } => unreachable!(),
            };
            self.add_issue_onto_start_including_decorator(
                i_s,
                IssueKind::OverloadInconsistentKind { kind },
            )
        }
        if let Some(implementation) = &implementation
            && in_stub
        {
            name_def_node_ref(implementation.function_link)
                .add_issue(i_s, IssueKind::OverloadStubImplementationNotAllowed);
        }

        if should_error_out.get() {
            return None;
        }
        if functions.len() < 2 {
            self.add_issue_onto_start_including_decorator(i_s, IssueKind::OverloadSingleNotAllowed);
            return None;
        } else if implementation.is_none()
            && !in_stub
            && self.class.map(|c| !c.is_protocol(i_s.db)).unwrap_or(true)
            && !has_abstract
        {
            if i_s.db.mypy_compatible() {
                name_def_node_ref(functions.first().unwrap().defined_at)
                    .name_ref_of_name_def()
                    .add_issue_onto_start_including_decorator(
                        i_s,
                        IssueKind::OverloadImplementationNeeded,
                    );
            } else {
                name_def_node_ref(functions.first().unwrap().defined_at)
                    .add_issue(i_s, IssueKind::OverloadImplementationNeeded);
            }
        }
        if has_non_abstract && has_abstract {
            self.add_issue_onto_start_including_decorator(
                i_s,
                IssueKind::OverloadWithAbstractAndNonAbstract,
            );
        }

        let is_final = if in_stub {
            functions.first().is_some_and(|f| f.is_final)
        } else {
            implementation
                .as_ref()
                .is_some_and(|implementation| implementation.callable.is_final)
        };

        if dataclass_transform.is_some() {
            debug!("Found dataclass transform overload");
        }
        Some(OverloadDefinition {
            functions: {
                debug_assert!(functions.len() > 1);
                FunctionOverload::new(functions.into_boxed_slice())
            },
            implementation,
            is_final,
            is_override,
            dataclass_transform,
        })
    }

    fn maybe_part_of_unreachable_overload(&self) -> Option<&OverloadDefinition> {
        let file = self.node_ref.file;
        if self.node_ref.point().maybe_specific() == Some(Specific::OverloadUnreachable)
            && let Some(first_index) =
                first_defined_name_of_multi_def(file, self.node().name().index())
            && let Some(func) = NodeRef::new(file, first_index).maybe_name_of_function()
            && let Some(ComplexPoint::FunctionOverload(o)) =
                NodeRef::new(self.node_ref.file, func.index()).maybe_complex()
        {
            return Some(o);
        }
        None
    }

    pub fn is_overload_implementation(&self) -> bool {
        self.maybe_part_of_unreachable_overload()
            .and_then(|overload| overload.implementation.as_ref())
            .is_some_and(|link| link.function_link == self.node_ref.as_link())
    }

    pub fn is_abstract(&self) -> bool {
        match self.node_ref.maybe_complex() {
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
        match self.node_ref.maybe_complex() {
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

    pub fn as_callable(
        &self,
        i_s: &InferenceState,
        first_param: FirstParamProperties,
    ) -> CallableContent {
        self.as_callable_with_options(
            i_s,
            AsCallableOptions {
                first_param,
                return_type: self.inferred_return_type(i_s),
            },
        )
    }

    pub fn as_callable_without_inferring_return_type(
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

    pub fn as_type_without_inferring_return_type(
        &self,
        i_s: &InferenceState,
        first_param: FirstParamProperties,
    ) -> Type {
        Type::Callable(Arc::new(
            self.as_callable_without_inferring_return_type(i_s, first_param),
        ))
    }

    pub fn as_callable_with_options(
        &self,
        i_s: &InferenceState,
        options: AsCallableOptions,
    ) -> CallableContent {
        let mut params = self.iter_params().peekable();
        let needs_self_type = match options.first_param {
            FirstParamProperties::Skip { .. } => {
                if let Some(p) = params.peek()
                    && matches!(
                        p.specific(i_s.db),
                        WrappedParamType::PositionalOnly(_)
                            | WrappedParamType::PositionalOrKeyword(_)
                    )
                {
                    params.next();
                }
                false
            }
            FirstParamProperties::None => {
                options.return_type.has_self_type(i_s.db)
                    || params_have_self_type_after_self(i_s.db, self.iter_params())
            }
        };

        let as_type = |t: &Type| {
            if matches!(options.first_param, FirstParamProperties::None) {
                return t.clone();
            }
            let Some(func_class) = self.class else {
                return t.clone();
            };
            t.replace_type_var_likes_and_self(
                i_s.db,
                &mut |usage| maybe_class_usage(i_s.db, &func_class, &usage),
                &|| {
                    if let FirstParamProperties::Skip { to_self_instance } = options.first_param {
                        Some(to_self_instance())
                    } else {
                        self.class.map(|t| t.as_type(i_s.db))
                    }
                },
            )
            .unwrap_or_else(|| t.clone())
        };
        let return_type = as_type(&options.return_type);
        let type_vars = self.type_vars(i_s.db).clone();
        let mut callable = self.internal_as_type(
            i_s,
            &type_vars,
            params,
            needs_self_type,
            as_type,
            return_type,
        );
        callable.type_vars = type_vars;
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
        Type::Callable(Arc::new(self.as_callable(i_s, first)))
    }

    fn internal_as_type(
        &self,
        i_s: &InferenceState,
        type_vars: &TypeVarLikes,
        params: impl Iterator<Item = FunctionParam<'a>>,
        needs_self_type: bool,
        mut as_type: impl FnMut(&Type) -> Type,
        return_type: Type,
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

        let return_result = |params| {
            self.as_callable_content_internal(
                i_s.db.python_state.empty_type_var_likes.clone(),
                params,
                had_first_annotation,
                return_type,
            )
        };

        let mut new_params = vec![];
        let file_index = self.node_ref.file_index();
        let mut had_positional_only = false;
        let mut had_positional_or_keyword = None;
        for (i, p) in params.enumerate() {
            if p.param.kind() == ParamKind::Star
                && let Some(ts) = p
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
            let specific = p.specific(i_s.db);
            let mut as_t = |t: Option<Cow<_>>| {
                t.map(|t| as_type(&t)).unwrap_or({
                    let name_ref = NodeRef::new(self.node_ref.file, p.param.name_def().index());
                    if name_ref.point().maybe_specific() == Some(Specific::MaybeSelfParam) {
                        if self.is_dunder_new() {
                            Type::Type(Arc::new(Type::Self_))
                        } else {
                            match kind {
                                FunctionKind::Function { .. } | FunctionKind::Property { .. } => {
                                    if needs_self_type {
                                        Type::Self_
                                    } else if let Some(cls) = self.class {
                                        cls.as_type(i_s.db)
                                    } else {
                                        recoverable_error!(
                                            "Tried to access Self in InferenceState"
                                        );
                                        Type::ERROR
                                    }
                                }
                                FunctionKind::Classmethod { .. } => {
                                    if let Some(cls) = self.class {
                                        cls.as_type_type(i_s.db)
                                    } else {
                                        recoverable_error!(
                                            "No class for calculating classmethod type"
                                        );
                                        Type::Any(AnyCause::Unannotated)
                                    }
                                }
                                FunctionKind::Staticmethod => {
                                    if let Some(usage) =
                                        type_vars.find_untyped_param_type_var(self.as_link(), i)
                                    {
                                        Type::TypeVar(usage)
                                    } else {
                                        Type::Any(AnyCause::Unannotated)
                                    }
                                }
                            }
                        }
                    } else if let Some(usage) =
                        type_vars.find_untyped_param_type_var(self.as_link(), i)
                    {
                        Type::TypeVar(usage)
                    } else {
                        Type::Any(AnyCause::Unannotated)
                    }
                })
            };
            let n = p.param.name_def();
            let param_specific = match specific {
                WrappedParamType::PositionalOnly(t) => {
                    had_positional_only = true;
                    ParamType::PositionalOnly(as_t(t))
                }
                WrappedParamType::PositionalOrKeyword(t) => {
                    if is_private(n.as_code()) && !had_positional_only {
                        // Mypy/conformance tests treat __ params as positional only
                        if let Some(on_number) = had_positional_or_keyword
                            // Ignore self
                            && (on_number != 0 || self.class.is_none())
                        {
                            // Generally we shouldn't add issues here when generating the callable.
                            // However this callable should only be generated once.
                            NodeRef::new(self.file, p.param.name_def().index()).add_type_issue(
                                i_s.db,
                                IssueKind::LegacyPositionalOnlyParamAfterNormal,
                            )
                        }
                        ParamType::PositionalOnly(as_t(t))
                    } else {
                        had_positional_or_keyword = Some(i);
                        ParamType::PositionalOrKeyword(as_t(t))
                    }
                }
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
                            let TupleArgs::ArbitraryLen(t) = Arc::unwrap_or_clone(tup).args else {
                                unreachable!()
                            };
                            StarParamType::ArbitraryLen(Arc::unwrap_or_clone(t))
                        }
                        _ => StarParamType::UnpackedTuple(tup),
                    })
                }
                WrappedParamType::Star(WrappedStar::ParamSpecArgs(u1)) => {
                    if let Some(c) = self.class
                        && c.node_ref.as_link() == u1.in_definition
                    {
                        let new = replace_param_spec(
                            i_s.db,
                            &mut |usage| {
                                Some(c.generics().nth_usage(i_s.db, &usage).into_generic_item())
                            },
                            u1,
                        );
                        return return_result(match new {
                            CallableParams::Simple(params) => {
                                new_params.extend_from_slice(&params);
                                CallableParams::Simple(new_params.into())
                            }
                            CallableParams::Any(cause) => CallableParams::Any(cause),
                        });
                    }
                    ParamType::Star(StarParamType::ParamSpecArgs(u1.clone()))
                }
                WrappedParamType::StarStar(WrappedStarStar::ValueType(t)) => {
                    ParamType::StarStar(StarStarParamType::ValueType(as_t(t)))
                }
                WrappedParamType::StarStar(WrappedStarStar::UnpackTypedDict(u)) => {
                    ParamType::StarStar(StarStarParamType::UnpackTypedDict(u))
                }
                WrappedParamType::StarStar(WrappedStarStar::ParamSpecKwargs(u)) => {
                    ParamType::StarStar(StarStarParamType::ParamSpecKwargs(u.clone()))
                }
            };
            new_params.push(CallableParam {
                type_: param_specific,
                has_default: p.has_default(),
                name: Some(StringSlice::new(file_index, n.start(), n.end()).into()),
                might_have_type_vars: p.might_have_type_vars(),
            });
        }
        return_result(CallableParams::new_simple(Arc::from(new_params)))
    }

    fn as_callable_content_internal(
        &self,
        type_vars: TypeVarLikes,
        params: CallableParams,
        had_first_self_or_class_annotation: bool,
        return_type: Type,
    ) -> CallableContent {
        CallableContent {
            // The actual kind is set by using the decorated() function.
            kind: FunctionKind::Function {
                had_first_self_or_class_annotation,
            },
            ..CallableContent::new_simple(
                Some(DbString::StringSlice(self.name_string_slice())),
                self.class.map(|c| c.name_string_slice()),
                self.node_ref.as_link(),
                type_vars,
                params,
                return_type,
            )
        }
    }

    fn as_no_type_check_callable(&self, db: &Database) -> CallableContent {
        let params = if db.mypy_compatible() {
            CallableParams::Any(AnyCause::Explicit)
        } else {
            CallableParams::Simple(
                self.iter_params()
                    .map(|p| {
                        let any = Type::Any(AnyCause::Explicit);
                        let type_ = match p.kind(db) {
                            ParamKind::PositionalOnly => ParamType::PositionalOnly(any),
                            ParamKind::PositionalOrKeyword => ParamType::PositionalOrKeyword(any),
                            ParamKind::KeywordOnly => ParamType::KeywordOnly(any),
                            ParamKind::Star => ParamType::Star(StarParamType::ArbitraryLen(any)),
                            ParamKind::StarStar => {
                                ParamType::StarStar(StarStarParamType::ValueType(any))
                            }
                        };
                        CallableParam {
                            type_,
                            has_default: p.has_default(),
                            name: Some({
                                let n = p.param.name_def();
                                StringSlice::new(self.node_ref.file_index(), n.start(), n.end())
                                    .into()
                            }),
                            might_have_type_vars: false,
                        }
                    })
                    .collect(),
            )
        };
        self.as_callable_content_internal(
            db.python_state.empty_type_var_likes.clone(),
            params,
            false,
            Type::Any(AnyCause::Explicit),
        )
    }

    pub fn iter_params(&self) -> impl Iterator<Item = FunctionParam<'a>> + use<'a> {
        let file = self.node_ref.file;
        self.node()
            .params()
            .iter()
            .map(|param| FunctionParam { file, param })
    }

    pub fn iter_untyped_params(
        &self,
        in_definition: PointLink,
        type_var_likes: &'a TypeVarLikes,
    ) -> impl Iterator<Item = UntypedFunctionParam<'a>> {
        self.iter_params()
            .enumerate()
            .map(move |(nth, param)| UntypedFunctionParam {
                param,
                in_definition,
                type_var_likes,
                nth,
            })
    }

    pub fn first_param_annotation_type(
        &self,
        i_s: &InferenceState<'db, '_>,
    ) -> Option<Cow<'_, Type>> {
        self.iter_params().next().and_then(|p| {
            let t = p.annotation(i_s.db);
            if let Some(t) = &t {
                match p.param.kind() {
                    ParamKind::PositionalOnly | ParamKind::PositionalOrKeyword => (),
                    ParamKind::Star => match t.as_ref() {
                        Type::Tuple(tup) => match &tup.args {
                            TupleArgs::ArbitraryLen(t) => return Some(Cow::Owned((**t).clone())),
                            TupleArgs::WithUnpack(w) => {
                                if let Some(first) = w.before.first() {
                                    return Some(Cow::Owned(first.clone()));
                                }
                                return Some(Cow::Borrowed(&Type::Never(NeverCause::Other)));
                            }
                            TupleArgs::FixedLen(_) => unreachable!(),
                        },
                        _ => return None,
                    },
                    ParamKind::KeywordOnly | ParamKind::StarStar => return None,
                }
            }
            t
        })
    }

    pub(super) fn execute_internal(
        &self,
        i_s: &InferenceState<'db, '_>,
        args: &dyn Args<'db>,
        skip_first_argument: bool,
        on_type_error: OnTypeError,
        replace_self_type: Option<ReplaceSelfInMatcher>,
        result_context: &mut ResultContext,
    ) -> Inferred {
        let return_annotation = self.return_annotation();
        let type_vars = self.type_vars(i_s.db);
        let calculated_type_vars =
            if self.node().is_typed() || !i_s.db.project.should_infer_untyped_params() {
                if !type_vars.is_empty()
                    && let Some(inf) = self.maybe_generic_decorator_overload_call(
                        i_s,
                        args,
                        skip_first_argument,
                        on_type_error,
                        replace_self_type,
                        result_context,
                    )
                {
                    return inf;
                }
                calc_func_type_vars(
                    i_s,
                    *self,
                    args.iter(i_s.mode),
                    |issue| args.add_issue(i_s, issue),
                    skip_first_argument,
                    type_vars,
                    self.node_ref.as_link(),
                    replace_self_type,
                    result_context,
                    Some(on_type_error),
                )
            } else {
                calc_untyped_func_type_vars(
                    i_s,
                    self,
                    args.iter(i_s.mode),
                    |issue| args.add_issue(i_s, issue),
                    skip_first_argument,
                    type_vars,
                    self.as_link(),
                    replace_self_type,
                    result_context,
                    on_type_error,
                )
            };

        if let Some(return_annotation) = return_annotation {
            self.apply_type_args_in_return_annotation_and_maybe_mark_unreachable(
                i_s,
                calculated_type_vars,
                &|| Some(replace_self_type?()),
                return_annotation,
                args,
                result_context,
            )
        } else {
            if args
                .in_file()
                .is_some_and(|file| file.flags(i_s.db).disallow_untyped_calls)
                && !self.is_typed()
                // Mypy only adds this error for explicit syntax calls like foo(), so to disable
                // all the other implicit calls, just skip magic methods.
                && !is_magic_method(self.name())
            {
                args.add_issue(
                    i_s,
                    IssueKind::CallToUntypedFunction {
                        name: self.name().into(),
                    },
                );
            }
            if i_s.db.project.should_infer_return_types() {
                self.return_without_annotation(
                    i_s,
                    self.ensure_cached_untyped_return(i_s),
                    calculated_type_vars,
                    replace_self_type,
                )
            } else {
                // The mypy-compatible case
                Inferred::new_any(AnyCause::Unannotated)
            }
        }
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
        let return_type = self.return_type(i_s);
        if return_type.is_never() {
            FLOW_ANALYSIS.with(|fa| fa.mark_current_frame_unreachable())
        }

        if result_context.expect_not_none() {
            if matches!(return_type.as_ref(), Type::None) {
                args.add_issue(
                    i_s,
                    IssueKind::DoesNotReturnAValue(self.diagnostic_string().into()),
                );
                // Not sure why Mypy returns any here, but we probably shouldn't. See also
                // discussion in Github #150
                if i_s.db.mypy_compatible() {
                    return Inferred::new_any_from_error();
                }
            }
        } else if self.is_async() {
            let return_type = calculated_type_vars.into_return_type(
                i_s,
                &return_type,
                self.class.as_ref(),
                replace_self_type,
            );
            args.add_issue(
                i_s,
                IssueKind::CoroutineValueMustBeUsed {
                    type_: return_type.format_short(i_s),
                },
            );
            return return_type;
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
        } else if self.is_async() {
            // Async functions remap the type so we can also not use the cache.
            Inferred::from_type(return_type.into_owned())
        } else {
            self.node_ref
                .file
                .name_resolution_for_types(i_s)
                .use_cached_return_annotation(return_annotation)
        }
    }

    fn maybe_generic_decorator_overload_call(
        &self,
        i_s: &InferenceState<'db, '_>,
        args: &dyn Args<'db>,
        skip_first_argument: bool,
        on_type_error: OnTypeError,
        replace_self_type: Option<ReplaceSelfInMatcher>,
        result_context: &mut ResultContext,
    ) -> Option<Inferred> {
        // This method is named is_generic_decorator_overload_call in Mypy.
        // It is necessary to pass overloads along mostly in decorators. Mypy has more reasoning
        // about it.
        let mut params = self.iter_params().skip(skip_first_argument as usize);
        let first_param = params.next()?;
        if params.next().is_some() {
            return None;
        }
        let first_annotation = first_param.annotation(i_s.db)?;
        let Type::Callable(_) = first_annotation.as_ref() else {
            return None;
        };
        let first_arg = args.maybe_single_positional_arg(i_s, &mut ResultContext::Unknown)?;
        let first_t = first_arg.as_cow_type(i_s);
        let CallableLike::Overload(overload) = first_t.maybe_callable(i_s)? else {
            return None;
        };
        let funcs: Box<[_]> = overload
            .iter_functions()
            .filter_map(|overload_callable| {
                let had_errors = Cell::new(false);
                let result = self.execute_internal(
                    i_s,
                    &KnownArgsWithCustomAddIssue::new(
                        &Inferred::from_type(Type::Callable(overload_callable.clone())),
                        &|_| {
                            had_errors.set(true);
                            false
                        },
                    ),
                    skip_first_argument,
                    on_type_error,
                    replace_self_type,
                    result_context,
                );
                let Type::Callable(mut c) = result.as_type(i_s) else {
                    return None;
                };
                if c.name.is_none() {
                    let mut new = c.as_ref().clone();
                    new.name = overload_callable.name.clone();
                    c = Arc::new(new);
                }
                (!had_errors.get()).then_some(c)
            })
            .collect();
        if funcs.len() == 0 {
            // No overload matched, therefore we can return
            return None;
        }
        Some(Inferred::from_type(Type::FunctionOverload(
            FunctionOverload::new(funcs),
        )))
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

    pub fn expected_return_type_for_return_stmt(
        &self,
        i_s: &InferenceState<'db, '_>,
    ) -> Cow<'_, Type> {
        let mut t = self.node_ref.return_annotation_type(i_s);
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
                Some(&|| class.as_type(i_s.db)),
                result_context,
            )
        } else {
            self.execute_internal(i_s, args, false, on_type_error, None, result_context)
        }
    }
}

#[derive(Copy, Clone)]
pub(crate) enum FirstParamProperties<'a> {
    Skip {
        to_self_instance: &'a dyn Fn() -> Type,
    },
    None,
}

pub(crate) struct AsCallableOptions<'a> {
    first_param: FirstParamProperties<'a>,
    return_type: Cow<'a, Type>,
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct FunctionParam<'x> {
    file: &'x PythonFile,
    param: CSTParam<'x>,
}

impl<'db: 'x, 'x> FunctionParam<'x> {
    fn annotation_or_any(&self, db: &'db Database) -> Cow<'x, Type> {
        self.annotation(db)
            .unwrap_or_else(|| Cow::Borrowed(&Type::Any(AnyCause::Unannotated)))
    }

    pub fn annotation(&self, db: &'db Database) -> Option<Cow<'x, Type>> {
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

    fn name(&self, _db: &'x Database) -> Option<&str> {
        Some(self.param.name_def().as_code())
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
                Some(Type::ParamSpecArgs(param_spec_usage)) => {
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

    fn kind(&self, _: &Database) -> ParamKind {
        self.param.kind()
    }

    fn into_callable_param(self) -> CallableParam {
        unreachable!("It feels like this might not be necessary")
    }

    fn has_self_type(&self, db: &Database) -> bool {
        self.annotation(db).is_some_and(|t| t.has_self_type(db))
    }

    fn might_have_type_vars(&self) -> bool {
        self.param.annotation().is_some_and(|param_annot| {
            let p = self.file.points.get(param_annot.index());
            p.maybe_specific() != Some(Specific::AnnotationOrTypeCommentWithoutTypeVars)
        })
    }
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct UntypedFunctionParam<'x> {
    param: FunctionParam<'x>,
    type_var_likes: &'x TypeVarLikes,
    in_definition: PointLink,
    nth: usize,
}

impl<'x> Param<'x> for UntypedFunctionParam<'x> {
    fn has_default(&self) -> bool {
        self.param.has_default()
    }

    fn name(&self, db: &'x Database) -> Option<&str> {
        self.param.name(db)
    }

    fn specific<'db: 'x>(&self, db: &'db Database) -> WrappedParamType<'x> {
        let mut pt = self.param.specific(db);
        let Some(usage) = self
            .type_var_likes
            .find_untyped_param_type_var(self.in_definition, self.nth)
        else {
            debug!(
                "Did not find type var for untyped param {:?}[{}]",
                self.type_var_likes, self.nth
            );
            // TODO Currently with multi-inheritance this can happen if the wrong __init__/__new__
            // is chosen.
            return pt;
        };
        match &mut pt {
            WrappedParamType::PositionalOnly(t)
            | WrappedParamType::PositionalOrKeyword(t)
            | WrappedParamType::KeywordOnly(t)
            | WrappedParamType::Star(WrappedStar::ArbitraryLen(t))
            | WrappedParamType::StarStar(WrappedStarStar::ValueType(t)) => {
                *t = Some(Cow::Owned(Type::TypeVar(usage)));
            }
            _ => {
                recoverable_error!("Did not handle untyped param {pt:?}");
            }
        };
        pt
    }

    fn kind(&self, db: &Database) -> ParamKind {
        self.param.kind(db)
    }

    fn into_callable_param(self) -> CallableParam {
        unreachable!("It feels like this might not be necessary")
    }

    fn has_self_type(&self, _: &Database) -> bool {
        false
    }

    fn might_have_type_vars(&self) -> bool {
        true
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
    let inference = file.inference(i_s);
    let inf = inference.infer_decorator(decorator);
    if let Some(saved_link) = inf.maybe_saved_link() {
        if saved_link == i_s.db.python_state.overload_link() {
            return InferredDecorator::Overload;
        }
        if saved_link == i_s.db.python_state.typing_final().as_link() {
            return InferredDecorator::Final;
        }
        if saved_link == i_s.db.python_state.typing_override_link {
            return InferredDecorator::Override;
        }
        if saved_link == i_s.db.python_state.abstractmethod_link() {
            return InferredDecorator::Abstractmethod;
        }
        if saved_link == i_s.db.python_state.no_type_check_link() {
            return InferredDecorator::NoTypeCheck;
        }
        let node_ref = NodeRef::from_link(i_s.db, saved_link);
        // All these cases are classes.
        if node_ref.maybe_class().is_some() {
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
                        setter_type: None,
                    },
                    is_abstract: is_abstract_property,
                };
            }
            if class.class_link_in_mro(i_s.db, i_s.db.python_state.cached_property_link()) {
                return InferredDecorator::FunctionKind {
                    kind: FunctionKind::Property {
                        had_first_self_or_class_annotation: had_first_annotation,
                        setter_type: Some(Arc::new(PropertySetter {
                            type_: PropertySetterType::SameTypeFromCachedProperty,
                            deprecated_reason: None,
                        })),
                    },
                    is_abstract: false,
                };
            }
        }
    }
    match inf.maybe_complex_point(i_s.db) {
        Some(ComplexPoint::TypeInstance(Type::DataclassTransformObj(transform))) => {
            InferredDecorator::DataclassTransform(transform.clone())
        }
        Some(ComplexPoint::TypeInstance(Type::Class(c)))
            if Some(c.link) == i_s.db.python_state.deprecated_link() =>
        {
            let reason = inference.infer_deprecated_reason(decorator);
            InferredDecorator::Deprecated(reason)
        }
        _ => {
            // We only care about this case for non-mypy compatibility, because for Mypy there are
            // no untyped type params.
            if i_s.db.project.should_infer_return_types()
                && inf
                    .maybe_any(i_s.db)
                    .is_some_and(|cause| cause == AnyCause::UntypedDecorator)
            {
                InferredDecorator::UntypedDecorator
            } else {
                InferredDecorator::Inferred(inf)
            }
        }
    }
}

#[derive(Debug)]
enum InferredDecorator {
    FunctionKind {
        kind: FunctionKind,
        is_abstract: bool,
    },
    Inferred(Inferred),
    Overload,
    DataclassTransform(DataclassTransformObj),
    Abstractmethod,
    Override,
    NoTypeCheck,
    UntypedDecorator,
    Deprecated(Arc<Box<str>>),
    Final,
}

struct FunctionDetails {
    inferred: Inferred,
    kind: FunctionKind,
    is_overload: bool,
    is_override: bool,
    dataclass_transform: Option<DataclassTransformObj>,
    has_decorator: bool,
}

enum PropertyModifier {
    JustADecorator,
    Setter(Arc<PropertySetter>),
    Deleter,
}

#[derive(PartialEq, Debug)]
pub(crate) enum FirstParamKind {
    Self_,
    ClassOfSelf,
    InStaticmethod,
}

pub(crate) struct GeneratorType {
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

impl FuncLike for Function<'_, '_> {
    fn inferred_return_type<'a>(&'a self, i_s: &InferenceState<'a, '_>) -> Cow<'a, Type> {
        if !i_s.db.project.should_infer_return_types() || self.return_annotation().is_some() {
            FuncNodeRef::return_type(self, i_s)
        } else {
            Cow::Owned(self.ensure_cached_untyped_return(i_s).as_type(i_s))
        }
    }

    fn diagnostic_string(&self, _: &Database) -> Option<String> {
        Some(self.diagnostic_string())
    }

    fn defined_at(&self) -> PointLink {
        self.node_ref.as_link()
    }

    fn type_vars<'a>(&'a self, db: &'a Database) -> &'a TypeVarLikes {
        FuncNodeRef::type_vars(self, db)
    }

    fn class(&self) -> Option<Class<'_>> {
        self.class
    }

    fn first_self_or_class_annotation<'a>(
        &'a self,
        i_s: &'a InferenceState,
    ) -> Option<Cow<'a, Type>> {
        self.first_param_annotation_type(i_s)
    }

    fn has_keyword_param_with_name(&self, db: &Database, name: &str) -> bool {
        self.iter_params().any(|p| {
            p.name(db) == Some(name)
                && matches!(
                    p.kind(db),
                    ParamKind::PositionalOrKeyword | ParamKind::KeywordOnly
                )
        })
    }

    fn is_callable(&self) -> bool {
        false
    }
}
