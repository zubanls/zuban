use parsa_python_ast::{
    Decorated, Decorator, ExpressionContent, ExpressionPart, FunctionDef, FunctionParent,
    NodeIndex, Param as ASTParam, ParamIterator as ASTParamIterator, ParamKind, PrimaryContent,
    PrimaryOrAtom, ReturnAnnotation, ReturnOrYield,
};
use std::borrow::Cow;
use std::cell::Cell;
use std::fmt;
use std::rc::Rc;

use super::{Callable, Module};
use crate::arguments::{Argument, ArgumentIterator, ArgumentKind, Arguments, KnownArguments};
use crate::database::{
    CallableContent, CallableParam, CallableParams, ClassGenerics, ComplexPoint, Database, DbType,
    DoubleStarredParamSpecific, FormatStyle, FunctionKind, FunctionOverload, GenericClass,
    GenericItem, GenericsList, Locality, OverloadDefinition, OverloadImplementation,
    ParamSpecUsage, ParamSpecific, Point, PointType, Specific, StarredParamSpecific, StringSlice,
    TupleContent, TupleTypeArguments, TypeOrTypeVarTuple, TypeVar, TypeVarKind, TypeVarLike,
    TypeVarLikeUsage, TypeVarLikes, TypeVarManager, TypeVarName, TypeVarUsage, Variance,
    WrongPositionalCount,
};
use crate::diagnostics::{Issue, IssueType};
use crate::file::{
    use_cached_annotation_type, PythonFile, TypeComputation, TypeComputationOrigin,
    TypeVarCallbackReturn,
};
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::matching::params::{
    InferrableParamIterator2, Param, WrappedDoubleStarred, WrappedParamSpecific, WrappedStarred,
};
use crate::matching::{
    calculate_callable_init_type_vars_and_return, calculate_callable_type_vars_and_return,
    calculate_function_type_vars_and_return, maybe_class_usage,
    replace_class_type_vars_in_callable, ArgumentIndexWithParam, CalculatedTypeArguments,
    FormatData, FunctionOrCallable, Generic, LookupResult, OnTypeError, ReplaceSelf, ResultContext,
    SignatureMatch, Type,
};
use crate::node_ref::NodeRef;
use crate::type_helpers::Class;
use crate::utils::rc_unwrap_or_clone;
use crate::{debug, new_class};

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
        debug_assert!(matches!(
            node_ref.point().maybe_specific(),
            Some(Specific::Function | Specific::DecoratedFunction)
        ));
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

    pub fn is_dynamic(&self) -> bool {
        self.return_annotation().is_none()
            && !self
                .node()
                .params()
                .iter()
                .any(|p| p.annotation().is_some())
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

    pub fn is_missing_param_annotations(&self, i_s: &InferenceState) -> bool {
        let mut iterator = self.node().params().iter();
        if self.class.is_some() && self.kind(i_s) != FunctionKind::Staticmethod {
            // The param annotation is defined implicitly as Self or Type[Self]
            iterator.next();
        }
        iterator.any(|p| p.annotation().is_none())
    }

    pub fn iter_inferrable_params<'b>(
        &self,
        db: &'db Database,
        args: &'b dyn Arguments<'db>,
        skip_first_param: bool,
    ) -> InferrableParamIterator<'db, 'b>
    where
        'a: 'b,
    {
        let mut params = self.node().params().iter();
        if skip_first_param {
            params.next();
        }
        InferrableParamIterator::new(db, self.node_ref.file, params, args.iter())
    }

    pub fn iter_args_with_params<'b, AI: Iterator<Item = Argument<'db, 'b>>>(
        &self,
        db: &'db Database,
        args: AI,
        skip_first_param: bool,
    ) -> InferrableParamIterator2<
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
        InferrableParamIterator2::new(db, params, args)
    }

    pub fn infer_param(
        &self,
        i_s: &InferenceState<'db, '_>,
        param_name_def_index: NodeIndex,
        args: &dyn Arguments<'db>,
    ) -> Inferred {
        let func_node =
            FunctionDef::from_param_name_def_index(&self.node_ref.file.tree, param_name_def_index);
        //let temporary_args;
        //let temporary_func;
        let (check_args, func) = if func_node.index() == self.node_ref.node_index {
            (args, self)
        } else {
            debug!("TODO untyped param");
            return Inferred::new_unknown();
        };
        for param in func.iter_inferrable_params(i_s.db, check_args, false) {
            if param.is_at(param_name_def_index) {
                return param.infer(i_s).unwrap_or_else(Inferred::new_unknown);
            }
        }
        unreachable!("{param_name_def_index:?}");
    }

    fn execute_without_annotation(
        &self,
        i_s: &InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
    ) -> Inferred {
        if i_s.db.python_state.project.mypy_compatible {
            return Inferred::new_any();
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

    fn iter_return_or_yield(&self) -> ReturnOrYieldIterator<'a> {
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

    pub fn type_vars(&self, i_s: &InferenceState<'db, '_>) -> Option<&'a TypeVarLikes> {
        // To save the generics just use the ( operator's storage.
        // + 1 for def; + 2 for name + 1 for (...)
        let type_var_reference = self.node_ref.add_to_node_index(4);
        if type_var_reference.point().calculated() {
            if let Some(complex) = type_var_reference.complex() {
                match complex {
                    ComplexPoint::TypeVarLikes(vars) => return Some(vars),
                    _ => unreachable!(),
                }
            }
            return None;
        }
        let func_node = self.node();
        let implicit_optional = i_s.db.python_state.project.implicit_optional;
        let mut inference = self.node_ref.file.inference(i_s);
        let in_result_type = Cell::new(false);
        let mut unbound_type_vars = vec![];
        let mut on_type_var = |i_s: &InferenceState,
                               manager: &TypeVarManager,
                               type_var: TypeVarLike,
                               current_callable: Option<_>| {
            self.class
                .and_then(|class| {
                    class
                        .type_vars(i_s)
                        .and_then(|t| t.find(type_var.clone(), class.node_ref.as_link()))
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
            &mut inference,
            self.node_ref.as_link(),
            &mut on_type_var,
            TypeComputationOrigin::ParamTypeCommentOrAnnotation,
        );
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
                type_computation.cache_annotation(annotation, is_implicit_optional);
            }
        }
        if let Some(return_annot) = func_node.return_annotation() {
            in_result_type.set(true);
            type_computation.cache_return_annotation(return_annot);
        }
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
            if let DbType::TypeVar(t) = self.result_type(i_s).as_ref() {
                if unbound_type_vars.contains(&TypeVarLike::TypeVar(t.type_var.clone())) {
                    let node_ref = self.expect_return_annotation_node_ref();
                    node_ref.add_issue(i_s, IssueType::TypeVarInReturnButNotArgument);
                    if let TypeVarKind::Bound(bound) = &t.type_var.kind {
                        node_ref.add_issue(
                            i_s,
                            IssueType::Note(
                                format!(
                                    "Consider using the upper bound \"{}\" instead",
                                    Type::new(bound).format_short(i_s.db)
                                )
                                .into(),
                            ),
                        );
                    }
                }
            }
        }
        match type_vars.len() {
            0 => type_var_reference.set_point(Point::new_node_analysis(Locality::Todo)),
            _ => type_var_reference
                .insert_complex(ComplexPoint::TypeVarLikes(type_vars), Locality::Todo),
        }
        debug_assert!(type_var_reference.point().calculated());
        self.type_vars(i_s)
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
                    .map(|p| p.param_specific.expect_positional_db_type()),
            );
            Rc::from(types)
        };
        match self.class {
            Some(c) if c.node_ref.as_link() == usage.in_definition => match c
                .generics()
                .nth_usage(i_s.db, &TypeVarLikeUsage::ParamSpec(Cow::Borrowed(usage)))
            {
                Generic::ParamSpecArgument(p) => match p.into_owned().params {
                    CallableParams::Any => CallableParams::Any,
                    CallableParams::Simple(params) => {
                        // Performance issue: Rc -> Vec check https://github.com/rust-lang/rust/issues/93610#issuecomment-1528108612
                        pre_params.extend(params.iter().cloned());
                        CallableParams::Simple(Rc::from(pre_params))
                    }
                    CallableParams::WithParamSpec(pre, p) => {
                        // Performance issue: Rc -> Vec check https://github.com/rust-lang/rust/issues/93610#issuecomment-1528108612
                        let types: Vec<_> = Vec::from(pre.as_ref());
                        CallableParams::WithParamSpec(into_types(types, pre_params), p)
                    }
                },
                _ => unreachable!(),
            },
            _ => {
                let types = vec![];
                CallableParams::WithParamSpec(into_types(types, pre_params), usage.clone())
            }
        }
    }

    pub fn as_inferred_from_name(&self, i_s: &InferenceState) -> Inferred {
        match self.node_ref.point().maybe_specific() {
            Some(Specific::Function) => Inferred::from_saved_node_ref(self.node_ref),
            Some(Specific::DecoratedFunction) => self.decorated(i_s),
            _ => unreachable!(),
        }
    }

    pub fn decorator_ref(&self) -> NodeRef {
        // To save the generics just use the ( operator's storage.
        // + 1 for def; + 2 for name + 1 for (...) + 1 for (
        self.node_ref.add_to_node_index(5)
    }

    pub fn decorated(&self, i_s: &InferenceState<'db, '_>) -> Inferred {
        let decorator_ref = self.decorator_ref();
        if decorator_ref.point().calculated() {
            return self
                .node_ref
                .file
                .inference(i_s)
                .check_point_cache(decorator_ref.node_index)
                .unwrap();
        }
        if let Some(class) = self.class {
            let class = Class::with_self_generics(i_s.db, class.node_ref);
            Self::new(self.node_ref, Some(class))
                .decorated_to_be_saved(&i_s.with_class_context(&class), decorator_ref)
        } else {
            self.decorated_to_be_saved(i_s, decorator_ref)
        }
        .save_redirect(i_s, decorator_ref.file, decorator_ref.node_index)
    }

    pub fn is_dunder_new(&self) -> bool {
        self.class.is_some() && self.name() == "__new__"
    }

    pub fn first_param_kind(&self, i_s: &InferenceState<'db, '_>) -> FirstParamKind {
        if self.is_dunder_new() {
            return FirstParamKind::ClassOfSelf;
        }
        match self.kind(i_s) {
            FunctionKind::Function | FunctionKind::Property { .. } => FirstParamKind::Self_,
            FunctionKind::Classmethod => FirstParamKind::ClassOfSelf,
            FunctionKind::Staticmethod => FirstParamKind::InStaticmethod,
        }
    }

    pub fn kind(&self, i_s: &InferenceState<'db, '_>) -> FunctionKind {
        if self.node_ref.point().specific() == Specific::DecoratedFunction {
            // Ensure it's cached
            let inf = self.decorated(i_s);
            if inf.maybe_saved_specific(i_s.db) == Some(Specific::OverloadUnreachable) {
                return FunctionKind::Function;
            }
            match self.decorator_ref().complex() {
                Some(ComplexPoint::FunctionOverload(o)) => o.kind(),
                Some(ComplexPoint::TypeInstance(DbType::Callable(c))) => c.kind,
                _ => FunctionKind::Function,
            }
        } else {
            FunctionKind::Function
        }
    }

    fn decorated_to_be_saved(
        &self,
        i_s: &InferenceState<'db, '_>,
        decorator_ref: NodeRef,
    ) -> Inferred {
        let node = self.node();
        let Some(details) = self.calculate_decorated_function_details(i_s) else {
            return Inferred::new_any()
        };

        let func_node = self.node();
        let file = self.node_ref.file;
        if details.is_overload {
            return if let Some(overload) = self.calculate_next_overload_items(i_s, details) {
                Inferred::new_unsaved_complex(ComplexPoint::FunctionOverload(Box::new(overload)))
            } else {
                Inferred::new_any()
            };
        }
        if matches!(details.kind, FunctionKind::Property { .. }) {
            let DbType::Callable(mut callable) = details.inferred.as_type(i_s).into_db_type() else {
                unreachable!()
            };
            if let Some(wrong) = callable.has_exactly_one_positional_parameter() {
                match wrong {
                    WrongPositionalCount::TooMany => {
                        NodeRef::new(file, self.expect_decorated_node().index())
                            .add_issue(i_s, IssueType::TooManyArguments(" for property".into()))
                    }
                    // IssueType::MethodWithoutArguments will be checked and added later.
                    WrongPositionalCount::TooFew => (),
                }
                return Inferred::new_any();
            }
            // Make sure the old Rc count is decreased, so we can use it mutable without cloning.
            drop(details);
            self.calculate_property_setter_and_deleter(i_s, Rc::make_mut(&mut callable));
            Inferred::from_type(DbType::Callable(callable))
        } else {
            details.inferred
        }
    }

    fn expect_decorated_node(&self) -> Decorated {
        match self.node().parent() {
            FunctionParent::Decorated(decorated) | FunctionParent::DecoratedAsync(decorated) => {
                decorated
            }
            _ => unreachable!(),
        }
    }

    fn calculate_decorated_function_details(
        &self,
        i_s: &InferenceState,
    ) -> Option<FunctionDetails> {
        let decorated = self.expect_decorated_node();
        let used_with_a_non_method = |name| {
            NodeRef::new(self.node_ref.file, decorated.index())
                .add_issue(i_s, IssueType::UsedWithANonMethod { name })
        };

        let mut inferred = Inferred::from_type(self.as_db_type(i_s, FirstParamProperties::None));
        let mut kind = FunctionKind::Function;
        let mut is_overload = false;
        for decorator in decorated.decorators().iter_reverse() {
            if matches!(kind, FunctionKind::Property { .. }) {
                NodeRef::new(self.node_ref.file, decorator.index())
                    .add_issue(i_s, IssueType::DecoratorOnTopOfPropertyNotSupported);
                break;
            }

            match infer_decorator(i_s, self.node_ref.file, decorator) {
                InferredDecorator::FunctionKind(k) => {
                    match k {
                        FunctionKind::Property { .. } => {
                            if is_overload {
                                NodeRef::new(self.node_ref.file, decorator.index())
                                    .add_issue(i_s, IssueType::OverloadedPropertyNotSupported);
                                return None;
                            }
                            if self.class.is_none() {
                                used_with_a_non_method("property");
                                return None;
                            }
                        }
                        FunctionKind::Classmethod => {
                            if kind == FunctionKind::Staticmethod {
                                NodeRef::new(self.node_ref.file, decorated.index())
                                    .add_issue(i_s, IssueType::InvalidClassmethodAndStaticmethod);
                                return None;
                            }
                            if self.class.is_none() {
                                used_with_a_non_method("classmethod");
                                return None;
                            }
                        }
                        FunctionKind::Staticmethod => {
                            if kind == FunctionKind::Classmethod {
                                NodeRef::new(self.node_ref.file, decorated.index())
                                    .add_issue(i_s, IssueType::InvalidClassmethodAndStaticmethod)
                            }
                            if self.class.is_none() {
                                used_with_a_non_method("staticmethod");
                                return None;
                            }
                        }
                        // A decorator has no way to specify its a normal function.
                        FunctionKind::Function => unreachable!(),
                    }
                    kind = k
                }
                InferredDecorator::Inferred(inf) => {
                    // TODO check if it's an function without a return annotation and
                    // abort in that case.
                    inferred = inf.execute(
                        i_s,
                        &KnownArguments::new(
                            &inferred,
                            NodeRef::new(self.node_ref.file, decorator.index()),
                        ),
                    );
                }
                InferredDecorator::Overload => is_overload = true,
                InferredDecorator::Abstractmethod => (),
            }
        }
        if let DbType::Callable(callable_content) = inferred.as_type(i_s).as_ref() {
            let mut callable_content = (**callable_content).clone();
            callable_content.name = Some(self.name_string_slice());
            callable_content.class_name = self.class.map(|c| c.name_string_slice());
            callable_content.kind = kind;
            inferred = Inferred::from_type(DbType::Callable(Rc::new(callable_content)));
        } else if !matches!(kind, FunctionKind::Function | FunctionKind::Staticmethod) {
            todo!("{kind:?}")
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
    ) {
        let is_property_modifier = |decorator: Decorator| {
            let ExpressionContent::ExpressionPart(ExpressionPart::Primary(primary)) = decorator.named_expression().expression().unpack() else {
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
            debug_assert_eq!(point.type_(), PointType::MultiDefinition);
            current_name_index = point.node_index();
            if current_name_index <= first_index {
                break;
            }
            let redirect_point = file.points.get(current_name_index - 1);
            debug_assert_eq!(redirect_point.type_(), PointType::Redirect);
            let func_ref = NodeRef::new(file, redirect_point.node_index());
            let next_func = Self::new(func_ref, self.class);

            if func_ref.point().specific() != Specific::DecoratedFunction {
                debug_assert_eq!(func_ref.point().specific(), Specific::Function);
                func_ref.add_issue(
                    i_s,
                    IssueType::UnexpectedDefinitionForProperty {
                        name: self.name().into(),
                    },
                );
                continue;
            }
            // Make sure this is not calculated again.
            next_func
                .decorator_ref()
                .set_point(Point::new_simple_specific(
                    Specific::OverloadUnreachable,
                    Locality::File,
                ));

            let decorated = next_func.expect_decorated_node();
            let mut iterator = decorated.decorators().iter();
            let decorator = iterator.next().unwrap();
            match is_property_modifier(decorator) {
                PropertyModifier::JustADecorator => {
                    NodeRef::new(file, decorator.index()).add_issue(
                        i_s,
                        IssueType::OnlySupportedTopDecoratorSetter {
                            name: self.name().into(),
                        },
                    );
                }
                PropertyModifier::Setter => {
                    callable.kind = FunctionKind::Property { writable: true };
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
        let mut add_func = |inf: Inferred| {
            if let Some(callable) = inf.as_type(i_s).maybe_callable(i_s) {
                functions.push(rc_unwrap_or_clone(callable))
            } else {
                todo!()
            }
        };
        let mut inconsistent_function_kind = None;
        add_func(details.inferred);
        let mut implementation: Option<OverloadImplementation> = None;
        let mut should_error_out = false;
        loop {
            let point = file.points.get(current_name_index);
            if !point.calculated() {
                break;
            }
            debug_assert_eq!(point.type_(), PointType::MultiDefinition);
            current_name_index = point.node_index();
            if current_name_index <= first_index {
                break;
            }
            let redirect_point = file.points.get(current_name_index - 1);
            debug_assert_eq!(redirect_point.type_(), PointType::Redirect);
            let func_ref = NodeRef::new(file, redirect_point.node_index());
            let next_func = Self::new(func_ref, self.class);
            let next_details = match func_ref.point().maybe_specific() {
                Some(Specific::DecoratedFunction) => {
                    if let Some(d) = next_func.calculate_decorated_function_details(i_s) {
                        d
                    } else {
                        should_error_out = true;
                        next_func
                            .decorator_ref()
                            .set_point(Point::new_simple_specific(
                                Specific::OverloadUnreachable,
                                Locality::File,
                            ));
                        continue;
                    }
                }
                Some(Specific::Function) => FunctionDetails {
                    inferred: Inferred::from_type(
                        next_func.as_db_type(i_s, FirstParamProperties::None),
                    ),
                    kind: FunctionKind::Function,
                    is_overload: false,
                    has_decorator: false,
                },
                _ => unreachable!(),
            };
            if details.kind != next_details.kind {
                if details.kind != FunctionKind::Function {
                    inconsistent_function_kind = Some(details.kind);
                }
                if next_details.kind != FunctionKind::Function {
                    inconsistent_function_kind = Some(next_details.kind);
                }
            }
            if next_details.has_decorator {
                // To make sure overloads aren't executed another time and to separate these
                // functions from the other ones, mark them unreachable here.
                next_func
                    .decorator_ref()
                    .set_point(Point::new_simple_specific(
                        Specific::OverloadUnreachable,
                        Locality::File,
                    ));
            }
            if next_details.is_overload {
                if let Some(implementation) = &implementation {
                    NodeRef::from_link(i_s.db, implementation.function_link)
                        .add_issue(i_s, IssueType::OverloadImplementationNotLast)
                }
                add_func(next_details.inferred)
            } else {
                // Check if the implementing function was already set
                if implementation.is_none() {
                    let t = next_details.inferred.as_type(i_s);
                    if !next_details.has_decorator && next_func.is_dynamic() || t.is_any() {
                        implementation = Some(OverloadImplementation {
                            function_link: func_ref.as_link(),
                            callable: CallableContent::new_any_with_defined_at(func_ref.as_link()),
                        });
                    } else if let Some(callable) = t.maybe_callable(i_s) {
                        implementation = Some(OverloadImplementation {
                            function_link: func_ref.as_link(),
                            callable: rc_unwrap_or_clone(callable),
                        });
                    } else {
                        implementation = Some(OverloadImplementation {
                            function_link: func_ref.as_link(),
                            callable: CallableContent::new_any_with_defined_at(func_ref.as_link()),
                        });
                        NodeRef::new(func_ref.file, next_func.expect_decorated_node().index())
                            .add_issue(
                                i_s,
                                IssueType::NotCallable {
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
                .add_issue(i_s, IssueType::OverloadInconsistentKind { kind })
        }
        if functions.len() < 2 && !should_error_out {
            self.node_ref
                .add_issue(i_s, IssueType::OverloadSingleNotAllowed);
        } else if implementation.is_none()
            && !file.is_stub(i_s.db)
            && self.class.map(|c| !c.is_protocol(i_s.db)).unwrap_or(true)
        {
            name_def_node_ref(functions.last().unwrap().defined_at)
                .add_issue(i_s, IssueType::OverloadImplementationNeeded);
        }
        if let Some(implementation) = &implementation {
            if file.is_stub(i_s.db) {
                name_def_node_ref(implementation.function_link)
                    .add_issue(i_s, IssueType::OverloadStubImplementationNotAllowed);
            }
        }
        debug_assert!(!functions.is_empty());
        (!should_error_out).then(|| OverloadDefinition {
            functions: FunctionOverload::new(functions.into_boxed_slice()),
            implementation,
        })
    }

    pub(crate) fn add_issue_for_declaration(&self, i_s: &InferenceState, type_: IssueType) {
        let node = self.node();
        self.node_ref.file.add_issue(
            i_s,
            Issue {
                type_,
                start_position: node.start(),
                end_position: node.end_position_of_colon(),
            },
        )
    }

    pub fn as_callable(
        &self,
        i_s: &InferenceState,
        first: FirstParamProperties,
    ) -> CallableContent {
        let mut params = self.iter_params().peekable();
        let mut self_type_var_usage = None;
        let defined_at = self.node_ref.as_link();
        let mut type_vars = self.type_vars(i_s).cloned(); // Cache annotation types
        let mut type_vars = if let Some(type_vars) = type_vars.take() {
            type_vars.as_vec()
        } else {
            vec![]
        };
        match first {
            FirstParamProperties::MethodAccessedOnClass => {
                let mut needs_self_type_variable =
                    self.result_type(i_s).has_explicit_self_type(i_s.db);
                for param in self.iter_params().skip(1) {
                    if let Some(t) = param.annotation(i_s) {
                        needs_self_type_variable |= t.has_explicit_self_type(i_s.db);
                    }
                }
                if needs_self_type_variable {
                    let self_type_var = Rc::new(TypeVar {
                        name_string: TypeVarName::Self_,
                        kind: TypeVarKind::Bound(self.class.unwrap().as_db_type(i_s.db)),
                        variance: Variance::Invariant,
                    });
                    self_type_var_usage = Some(TypeVarUsage {
                        in_definition: defined_at,
                        type_var: self_type_var.clone(),
                        index: 0.into(),
                    });
                    type_vars.insert(0, TypeVarLike::TypeVar(self_type_var));
                }
            }
            FirstParamProperties::Skip { .. } => {
                params.next();
            }
            FirstParamProperties::None => (),
        }
        let self_type_var_usage = self_type_var_usage.as_ref();

        let as_db_type = |i_s: &InferenceState, t: Type| {
            if matches!(first, FirstParamProperties::None) {
                return t.as_db_type();
            }
            let Some(func_class) = self.class else {
                return t.as_db_type()
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
                        DbType::TypeVar(self_type_var_usage.clone())
                    } else if let FirstParamProperties::Skip { to_self_instance } = first {
                        to_self_instance()
                    } else {
                        DbType::Self_
                    }
                },
            )
        };
        let mut callable =
            self.internal_as_db_type(i_s, params, self_type_var_usage.is_some(), as_db_type);
        callable.type_vars = (!type_vars.is_empty()).then(|| TypeVarLikes::from_vec(type_vars));
        callable
    }

    pub fn as_db_type(&self, i_s: &InferenceState, first: FirstParamProperties) -> DbType {
        DbType::Callable(Rc::new(self.as_callable(i_s, first)))
    }

    pub fn as_type(&self, i_s: &InferenceState<'db, '_>) -> Type<'a> {
        Type::owned(self.as_db_type(i_s, FirstParamProperties::None))
    }

    fn internal_as_db_type(
        &self,
        i_s: &InferenceState,
        params: impl Iterator<Item = FunctionParam<'a>>,
        has_self_type_var_usage: bool,
        mut as_db_type: impl FnMut(&InferenceState, Type) -> DbType,
    ) -> CallableContent {
        let kind = match self.node_ref.point().specific() {
            Specific::DecoratedFunction => {
                kind_of_decorators(i_s, self.node_ref.file, self.expect_decorated_node())
            }
            _ => FunctionKind::Function,
        };
        let mut params = params.peekable();
        let result_type = self.result_type(i_s);
        let mut result_type = as_db_type(i_s, result_type);
        if self.is_async() && !self.is_generator() {
            result_type = new_class!(
                i_s.db.python_state.coroutine_link(),
                DbType::Any,
                DbType::Any,
                result_type,
            );
        }

        let return_result = |params| CallableContent {
            name: Some(self.name_string_slice()),
            class_name: self.class.map(|c| c.name_string_slice()),
            defined_at: self.node_ref.as_link(),
            // The actual kind is set by using the decorated() function.
            kind: FunctionKind::Function,
            params,
            type_vars: None,
            result_type,
        };

        let mut new_params = vec![];
        let mut had_param_spec_args = false;
        let file_index = self.node_ref.file_index();
        while let Some(p) = params.next() {
            let specific = p.specific(i_s.db);
            let mut as_t = |t: Option<Type>| {
                t.map(|t| as_db_type(i_s, t)).unwrap_or({
                    let name_ref =
                        NodeRef::new(self.node_ref.file, p.param.name_definition().index());
                    if name_ref.point().maybe_specific() == Some(Specific::MaybeSelfParam) {
                        if self.is_dunder_new() {
                            if has_self_type_var_usage {
                                DbType::Type(Rc::new(DbType::Self_))
                            } else {
                                self.class.unwrap().as_type(i_s).into_db_type()
                            }
                        } else if has_self_type_var_usage {
                            DbType::Self_
                        } else {
                            match kind {
                                FunctionKind::Function | FunctionKind::Property { .. } => {
                                    self.class.unwrap().as_db_type(i_s.db)
                                }
                                FunctionKind::Classmethod => DbType::Any,
                                FunctionKind::Staticmethod => DbType::Any,
                            }
                        }
                    } else {
                        DbType::Any
                    }
                })
            };
            let param_specific = match specific {
                WrappedParamSpecific::PositionalOnly(t) => ParamSpecific::PositionalOnly(as_t(t)),
                WrappedParamSpecific::PositionalOrKeyword(t) => {
                    ParamSpecific::PositionalOrKeyword(as_t(t))
                }
                WrappedParamSpecific::KeywordOnly(t) => ParamSpecific::KeywordOnly(as_t(t)),
                WrappedParamSpecific::Starred(WrappedStarred::ArbitraryLength(t)) => {
                    ParamSpecific::Starred(StarredParamSpecific::ArbitraryLength(as_t(t)))
                }
                WrappedParamSpecific::Starred(WrappedStarred::ParamSpecArgs(u1)) => {
                    match params.peek().map(|p| p.specific(i_s.db)) {
                        Some(WrappedParamSpecific::DoubleStarred(
                            WrappedDoubleStarred::ParamSpecKwargs(u2),
                        )) if u1 == u2 => {
                            had_param_spec_args = true;
                            continue;
                        }
                        _ => todo!(),
                    }
                }
                WrappedParamSpecific::DoubleStarred(WrappedDoubleStarred::ValueType(t)) => {
                    ParamSpecific::DoubleStarred(DoubleStarredParamSpecific::ValueType(as_t(t)))
                }
                WrappedParamSpecific::DoubleStarred(WrappedDoubleStarred::ParamSpecKwargs(u)) => {
                    if !had_param_spec_args {
                        todo!()
                    }
                    return return_result(self.remap_param_spec(i_s, new_params, u));
                }
            };
            new_params.push(CallableParam {
                param_specific,
                has_default: p.has_default(),
                name: Some({
                    let n = p.param.name_definition();
                    StringSlice::new(file_index, n.start(), n.end())
                }),
            });
        }
        return_result(CallableParams::Simple(Rc::from(new_params)))
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

    pub fn first_param_annotation_type(&self, i_s: &InferenceState<'db, '_>) -> Option<Type> {
        self.iter_params().next().and_then(|p| p.annotation(i_s))
    }

    pub(super) fn execute_internal(
        &self,
        i_s: &InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
        on_type_error: OnTypeError<'db, '_>,
        replace_self_type: ReplaceSelf,
        result_context: &mut ResultContext,
    ) -> Inferred {
        let return_annotation = self.return_annotation();
        let func_type_vars = return_annotation.and_then(|_| self.type_vars(i_s));
        let calculated_type_vars = calculate_function_type_vars_and_return(
            i_s,
            *self,
            args.iter(),
            &|| args.as_node_ref(),
            false,
            func_type_vars,
            self.node_ref.as_link(),
            result_context,
            Some(on_type_error),
        );
        let result = if let Some(return_annotation) = return_annotation {
            self.apply_type_args_in_return_annotation(
                i_s,
                calculated_type_vars,
                replace_self_type,
                return_annotation,
                args,
                result_context,
            )
        } else {
            if i_s.db.python_state.project.disallow_untyped_calls && self.is_dynamic() {
                args.as_node_ref().add_issue(
                    i_s,
                    IssueType::CallToUntypedFunction {
                        name: self.name().into(),
                    },
                )
            }
            self.execute_without_annotation(i_s, args)
        };
        if self.is_async() && !self.is_generator() {
            return Inferred::from_type(new_class!(
                i_s.db.python_state.coroutine_link(),
                DbType::Any,
                DbType::Any,
                result.as_type(i_s).into_db_type(),
            ));
        }
        result
    }

    fn apply_type_args_in_return_annotation(
        &self,
        i_s: &InferenceState<'db, '_>,
        calculated_type_vars: CalculatedTypeArguments,
        replace_self_type: ReplaceSelf,
        return_annotation: ReturnAnnotation,
        args: &dyn Arguments<'db>,
        result_context: &mut ResultContext,
    ) -> Inferred {
        let return_type = self
            .node_ref
            .file
            .inference(i_s)
            .use_cached_return_annotation_type(return_annotation);
        if result_context.expect_not_none(i_s) && matches!(return_type.as_ref(), DbType::None) {
            args.as_node_ref().add_issue(
                i_s,
                IssueType::DoesNotReturnAValue(self.diagnostic_string().into()),
            );
            return Inferred::new_any();
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
            return_type.execute_and_resolve_type_vars(
                i_s,
                &calculated_type_vars,
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

    pub fn result_type(&self, i_s: &InferenceState<'db, '_>) -> Type<'a> {
        self.return_annotation()
            .map(|a| {
                self.node_ref
                    .file
                    .inference(i_s)
                    .use_cached_return_annotation_type(a)
            })
            .unwrap_or_else(|| Type::new(&DbType::Any))
    }

    fn format_overload_variant(&self, i_s: &InferenceState, is_init: bool) -> Box<str> {
        // Make sure annotations/type vars are calculated
        self.type_vars(i_s);

        let node = self.node();
        let ret = match node.return_annotation() {
            Some(annotation) => self
                .node_ref
                .file
                .inference(i_s)
                .use_cached_return_annotation_type(annotation),
            None => Type::new(&DbType::Any),
        };
        format_pretty_function_like(
            &FormatData::new_short(i_s.db),
            self.class,
            self.class.is_some()
                && self
                    .iter_params()
                    .next()
                    .is_some_and(|t| t.annotation(i_s).is_none()),
            self.name(),
            self.type_vars(i_s),
            self.iter_params(),
            (!is_init).then_some(ret),
        )
    }

    pub fn execute(
        &self,
        i_s: &InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
        result_context: &mut ResultContext,
        on_type_error: OnTypeError<'db, '_>,
    ) -> Inferred {
        if let Some(class) = &self.class {
            self.execute_internal(
                &i_s.with_class_context(class),
                args,
                on_type_error,
                &|| class.as_db_type(i_s.db),
                result_context,
            )
        } else {
            self.execute_internal(i_s, args, on_type_error, &|| DbType::Self_, result_context)
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
        format!(
            "{}.{}",
            Module::new(self.node_ref.file).qualified_name(db),
            self.name()
        )
    }

    pub fn name(&self) -> &str {
        let func = FunctionDef::by_index(&self.node_ref.file.tree, self.node_ref.node_index);
        func.name().as_str()
    }
}

#[derive(Copy, Clone)]
pub enum FirstParamProperties<'a> {
    Skip {
        to_self_instance: &'a dyn Fn() -> DbType,
    },
    MethodAccessedOnClass,
    None,
}

struct ReturnOrYieldIterator<'a> {
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
            Some(ReturnOrYield::by_index(&self.file.tree, index - 1))
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct FunctionParam<'x> {
    file: &'x PythonFile,
    param: ASTParam<'x>,
}

impl<'db: 'x, 'x> FunctionParam<'x> {
    pub fn annotation(&self, i_s: &InferenceState<'db, '_>) -> Option<Type<'x>> {
        self.param
            .annotation()
            .map(|annotation| use_cached_annotation_type(i_s.db, self.file, annotation))
    }
}

impl<'x> Param<'x> for FunctionParam<'x> {
    fn has_default(&self) -> bool {
        self.param.default().is_some()
    }

    fn name(&self, db: &'x Database) -> Option<&str> {
        Some(self.param.name_definition().as_code())
    }

    fn specific<'db: 'x>(&self, db: &'db Database) -> WrappedParamSpecific<'x> {
        let t = self
            .param
            .annotation()
            .map(|annotation| use_cached_annotation_type(db, self.file, annotation));
        fn dbt<'a>(t: Option<&Type<'a>>) -> Option<&'a DbType> {
            t.map(|t| t.expect_borrowed_db_type())
        }
        match self.kind(db) {
            ParamKind::PositionalOnly => WrappedParamSpecific::PositionalOnly(t),
            ParamKind::PositionalOrKeyword => WrappedParamSpecific::PositionalOrKeyword(t),
            ParamKind::KeywordOnly => WrappedParamSpecific::KeywordOnly(t),
            ParamKind::Starred => WrappedParamSpecific::Starred(match dbt(t.as_ref()) {
                Some(DbType::ParamSpecArgs(ref param_spec_usage)) => {
                    WrappedStarred::ParamSpecArgs(param_spec_usage)
                }
                _ => WrappedStarred::ArbitraryLength(t.map(|t| {
                    let DbType::Tuple(t) = t.expect_borrowed_db_type() else {
                        unreachable!()
                    };
                    match t.args.as_ref().unwrap() {
                        TupleTypeArguments::FixedLength(..) => todo!(),
                        TupleTypeArguments::ArbitraryLength(t) => Type::new(t),
                    }
                }))
            }),
            ParamKind::DoubleStarred => WrappedParamSpecific::DoubleStarred(match dbt(t.as_ref()) {
                Some(DbType::ParamSpecKwargs(param_spec_usage)) => {
                    WrappedDoubleStarred::ParamSpecKwargs(param_spec_usage)
                }
                _ => WrappedDoubleStarred::ValueType(t.map(|t| {
                    let DbType::Class(GenericClass {generics: ClassGenerics::List(generics), ..}) = t.expect_borrowed_db_type() else {
                        unreachable!()
                    };
                    let GenericItem::TypeArgument(t) = &generics[1.into()] else {
                        unreachable!();
                    };
                    Type::new(t)
                }))
            })
        }
    }

    fn kind(&self, db: &Database) -> ParamKind {
        let mut t = self.param.type_();
        if t == ParamKind::PositionalOrKeyword
            && db.python_state.project.mypy_compatible
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

pub struct InferrableParamIterator<'db, 'a> {
    db: &'db Database,
    arguments: ArgumentIterator<'db, 'a>,
    params: ASTParamIterator<'a>,
    file: &'a PythonFile,
    unused_keyword_arguments: Vec<Argument<'db, 'a>>,
}

impl<'db, 'a> InferrableParamIterator<'db, 'a> {
    fn new(
        db: &'db Database,
        file: &'a PythonFile,
        params: ASTParamIterator<'a>,
        arguments: ArgumentIterator<'db, 'a>,
    ) -> Self {
        Self {
            db,
            arguments,
            file,
            params,
            unused_keyword_arguments: vec![],
        }
    }

    fn next_argument(&mut self, param: &FunctionParam<'a>) -> ParamInput<'db, 'a> {
        for (i, unused) in self.unused_keyword_arguments.iter().enumerate() {
            match &unused.kind {
                ArgumentKind::Keyword { key, .. } => {
                    if *key == param.name(self.db).unwrap() {
                        return ParamInput::Argument(self.unused_keyword_arguments.remove(i));
                    }
                }
                _ => unreachable!(),
            }
        }
        match param.kind(self.db) {
            ParamKind::PositionalOrKeyword => {
                for argument in &mut self.arguments {
                    match argument.kind {
                        ArgumentKind::Keyword { key, .. } => {
                            if key == param.name(self.db).unwrap() {
                                return ParamInput::Argument(argument);
                            } else {
                                self.unused_keyword_arguments.push(argument);
                            }
                        }
                        _ => return ParamInput::Argument(argument),
                    }
                }
            }
            ParamKind::KeywordOnly => {
                for argument in &mut self.arguments {
                    match argument.kind {
                        ArgumentKind::Keyword { key, .. } => {
                            if key == param.name(self.db).unwrap() {
                                return ParamInput::Argument(argument);
                            } else {
                                self.unused_keyword_arguments.push(argument);
                            }
                        }
                        _ => todo!(),
                    }
                }
            }
            ParamKind::PositionalOnly => todo!(),
            ParamKind::Starred => {
                let mut args = vec![];
                for argument in &mut self.arguments {
                    if argument.is_keyword_argument() {
                        self.unused_keyword_arguments.push(argument);
                        break;
                    }
                    args.push(argument)
                }
                return ParamInput::Tuple(args.into_boxed_slice());
            }
            ParamKind::DoubleStarred => todo!(),
        }
        for argument in &mut self.arguments {
            // TODO check param type here and make sure that it makes sense.
        }
        ParamInput::None
    }
}

impl<'db, 'a> Iterator for InferrableParamIterator<'db, 'a> {
    type Item = InferrableParam<'db, 'a>;

    fn next(&mut self) -> Option<Self::Item> {
        self.params.next().map(|param| {
            let param = FunctionParam {
                file: self.file,
                param,
            };
            let argument = self.next_argument(&param);
            InferrableParam { param, argument }
        })
    }
}

#[derive(Debug)]
enum ParamInput<'db, 'a> {
    Argument(Argument<'db, 'a>),
    Tuple(Box<[Argument<'db, 'a>]>),
    None,
}

#[derive(Debug)]
pub struct InferrableParam<'db, 'a> {
    pub param: FunctionParam<'a>,
    argument: ParamInput<'db, 'a>,
}

impl<'db> InferrableParam<'db, '_> {
    fn is_at(&self, index: NodeIndex) -> bool {
        self.param.param.name_definition().index() == index
    }

    pub fn has_argument(&self) -> bool {
        !matches!(self.argument, ParamInput::None)
    }

    pub fn infer(&self, i_s: &InferenceState<'db, '_>) -> Option<Inferred> {
        if !matches!(&self.argument, ParamInput::None) {
            debug!("Infer param {:?}", self.param.name(i_s.db));
        }
        match &self.argument {
            ParamInput::Argument(arg) => Some(arg.infer(i_s, &mut ResultContext::Unknown)),
            ParamInput::Tuple(args) => {
                let mut list = vec![];
                for arg in args.iter() {
                    if arg.in_args_or_kwargs_and_arbitrary_len() {
                        todo!()
                    }
                    list.push(TypeOrTypeVarTuple::Type(
                        arg.infer(i_s, &mut ResultContext::Unknown).as_db_type(i_s),
                    ))
                }
                let t = TupleContent::new_fixed_length(list.into());
                Some(Inferred::from_type(DbType::Tuple(Rc::new(t))))
            }
            ParamInput::None => None,
        }
    }
}

#[derive(Debug)]
pub struct OverloadedFunction<'a> {
    overload: &'a Rc<FunctionOverload>,
    class: Option<Class<'a>>,
}

pub enum OverloadResult<'a> {
    Single(Callable<'a>),
    Union(DbType),
    NotFound,
}

#[derive(Debug)]
pub enum UnionMathResult {
    FirstSimilarIndex(usize),
    Match {
        first_similar_index: usize,
        result: DbType,
    },
    NoMatch,
}

impl<'db: 'a, 'a> OverloadedFunction<'a> {
    pub fn new(overload: &'a Rc<FunctionOverload>, class: Option<Class<'a>>) -> Self {
        Self { overload, class }
    }

    pub(super) fn find_matching_function(
        &self,
        i_s: &InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
        class: Option<&Class>,
        search_init: bool, // TODO this feels weird, maybe use a callback?
        result_context: &mut ResultContext,
        on_type_error: OnTypeError<'db, '_>,
    ) -> OverloadResult<'a> {
        let match_signature = |i_s: &InferenceState<'db, '_>,
                               result_context: &mut ResultContext,
                               callable: Callable| {
            if search_init {
                calculate_callable_init_type_vars_and_return(
                    i_s,
                    class.unwrap(),
                    callable,
                    args.iter(),
                    &|| args.as_node_ref(),
                    result_context,
                    None,
                )
            } else {
                calculate_callable_type_vars_and_return(
                    i_s,
                    callable,
                    args.iter(),
                    &|| args.as_node_ref(),
                    false,
                    result_context,
                    None,
                )
            }
        };
        let mut first_arbitrary_length_not_handled = None;
        let mut first_similar = None;
        let mut multi_any_match: Option<(_, _, Box<_>)> = None;
        let mut had_error_in_func = None;
        for (i, callable) in self.overload.iter_functions().enumerate() {
            let callable = Callable::new(callable, self.class);
            let (calculated_type_args, had_error) =
                i_s.do_overload_check(|i_s| match_signature(i_s, result_context, callable));
            if had_error && had_error_in_func.is_none() {
                had_error_in_func = Some(callable);
            }
            match calculated_type_args.matches {
                SignatureMatch::True {
                    arbitrary_length_handled,
                } => {
                    if multi_any_match.is_some() {
                        // This means that there was an explicit any in a param.
                        return OverloadResult::NotFound;
                    } else if !arbitrary_length_handled {
                        if first_arbitrary_length_not_handled.is_none() {
                            first_arbitrary_length_not_handled =
                                Some((calculated_type_args.type_arguments, callable));
                        }
                    } else {
                        debug!(
                            "Decided overload for {} (called on #{}): {:?}",
                            self.name(i_s.db),
                            args.as_node_ref().line(),
                            callable.content.format(&FormatData::new_short(i_s.db))
                        );
                        args.reset_cache();
                        return OverloadResult::Single(callable);
                    }
                }
                SignatureMatch::TrueWithAny { argument_indices } => {
                    // TODO there could be three matches or more?
                    // TODO maybe merge list[any] and list[int]
                    if let Some((_, _, ref old_indices)) = multi_any_match {
                        // If multiple signatures match because of Any, we should just return
                        // without an error message, there is no clear choice, i.e. it's ambiguous,
                        // but there should also not be an error.
                        if are_any_arguments_ambiguous_in_overload(
                            i_s.db,
                            old_indices,
                            &argument_indices,
                        ) {
                            if had_error {
                                args.reset_cache();
                                // Need to run the whole thing again to generate errors, because
                                // the function is not going to be checked.
                                match_signature(i_s, result_context, callable);
                                todo!("Add a test")
                            }
                            debug!(
                                "Decided overload with any for {} (called on #{}): {:?}",
                                self.name(i_s.db),
                                args.as_node_ref().line(),
                                callable.content.format(&FormatData::new_short(i_s.db)),
                            );
                            args.reset_cache();
                            return OverloadResult::NotFound;
                        }
                    } else {
                        multi_any_match = Some((
                            calculated_type_args.type_arguments,
                            callable,
                            argument_indices,
                        ))
                    }
                }
                SignatureMatch::False { similar: true } => {
                    if first_similar.is_none() {
                        first_similar = Some(callable)
                    }
                }
                SignatureMatch::False { similar: false } => (),
            }
            args.reset_cache();
        }
        if let Some((type_arguments, callable, _)) = multi_any_match {
            debug!(
                "Decided overload with any fallback for {} (called on #{}): {:?}",
                self.name(i_s.db),
                args.as_node_ref().line(),
                callable.content.format(&FormatData::new_short(i_s.db))
            );
            return OverloadResult::Single(callable);
        }
        if let Some((type_arguments, callable)) = first_arbitrary_length_not_handled {
            return OverloadResult::Single(callable);
        }
        if first_similar.is_none() && args.has_a_union_argument(i_s) {
            let mut non_union_args = vec![];
            match self.check_union_math(
                i_s,
                result_context,
                args.iter(),
                &mut non_union_args,
                args.as_node_ref(),
                search_init,
                class,
            ) {
                UnionMathResult::Match { result, .. } => return OverloadResult::Union(result),
                UnionMathResult::FirstSimilarIndex(index) => {
                    first_similar = Some(Callable::new(
                        self.overload.iter_functions().nth(index).unwrap(),
                        self.class,
                    ))
                }
                UnionMathResult::NoMatch => (),
            }
        }
        if let Some(callable) = first_similar {
            // In case of similar params, we simply use the first similar overload and calculate
            // its diagnostics and return its types.
            // This is also how mypy does it. See `check_overload_call` (9943444c7)
            let calculated_type_args = match_signature(i_s, result_context, callable);
            return OverloadResult::Single(callable);
        } else if let Some(on_overload_mismatch) = on_type_error.on_overload_mismatch {
            on_overload_mismatch(i_s, class)
        } else {
            let f_or_c = FunctionOrCallable::Callable(Callable::new(
                self.overload.iter_functions().next().unwrap(),
                self.class,
            ));
            let t = IssueType::OverloadMismatch {
                name: (on_type_error.generate_diagnostic_string)(&f_or_c, i_s.db)
                    .unwrap_or_else(|| todo!())
                    .into(),
                args: args.iter().into_argument_types(i_s),
                variants: self.variants(i_s, search_init),
            };
            args.as_node_ref().add_issue(i_s, t);
        }
        if let Some(callable) = had_error_in_func {
            // Need to run the whole thing again to generate errors, because the function is not
            // going to be checked.
            match_signature(i_s, result_context, callable);
        }
        OverloadResult::NotFound
    }

    fn check_union_math<'x>(
        &self,
        i_s: &InferenceState<'db, '_>,
        result_context: &mut ResultContext,
        mut args: ArgumentIterator<'db, 'x>,
        non_union_args: &mut Vec<Argument<'db, 'x>>,
        args_node_ref: NodeRef,
        search_init: bool,
        class: Option<&Class>,
    ) -> UnionMathResult {
        if let Some(next_arg) = args.next() {
            let inf = next_arg.infer(i_s, result_context);
            if inf.is_union(i_s) {
                // TODO this is shit
                let nxt_arg: &'x Argument<'db, 'x> = unsafe { std::mem::transmute(&next_arg) };
                non_union_args.push(Argument {
                    index: next_arg.index,
                    kind: ArgumentKind::Overridden {
                        original: nxt_arg,
                        inferred: Inferred::new_unknown(),
                    },
                });
                let DbType::Union(u) = inf.as_type(i_s).into_db_type() else {
                    unreachable!()
                };
                let mut unioned = DbType::Never;
                let mut first_similar = None;
                let mut mismatch = false;
                for entry in u.entries.into_vec().into_iter() {
                    let non_union_args_len = non_union_args.len();
                    non_union_args.last_mut().unwrap().kind = ArgumentKind::Overridden {
                        original: nxt_arg,
                        inferred: Inferred::from_type(entry.type_),
                    };
                    let r = self.check_union_math(
                        i_s,
                        result_context,
                        args.clone(),
                        non_union_args,
                        args_node_ref,
                        search_init,
                        class,
                    );
                    if let UnionMathResult::Match {
                        first_similar_index,
                        ..
                    }
                    | UnionMathResult::FirstSimilarIndex(first_similar_index) = r
                    {
                        if first_similar
                            .map(|f| f > first_similar_index)
                            .unwrap_or(true)
                        {
                            first_similar = Some(first_similar_index);
                        }
                    }
                    match r {
                        UnionMathResult::Match { result, .. } if !mismatch => {
                            unioned.union_in_place(i_s.db, result);
                        }
                        _ => mismatch = true,
                    };
                    non_union_args.truncate(non_union_args_len);
                }
                if mismatch {
                    if let Some(first_similar_index) = first_similar {
                        UnionMathResult::FirstSimilarIndex(first_similar_index)
                    } else {
                        UnionMathResult::NoMatch
                    }
                } else {
                    UnionMathResult::Match {
                        result: unioned,
                        first_similar_index: first_similar.unwrap(),
                    }
                }
            } else {
                non_union_args.push(next_arg);
                self.check_union_math(
                    i_s,
                    result_context,
                    args,
                    non_union_args,
                    args_node_ref,
                    search_init,
                    class,
                )
            }
        } else {
            let mut first_similar = None;
            for (i, callable) in self.overload.iter_functions().enumerate() {
                let callable = Callable::new(callable, self.class);
                let (calculated_type_args, had_error) = i_s.do_overload_check(|i_s| {
                    if search_init {
                        calculate_callable_init_type_vars_and_return(
                            i_s,
                            class.unwrap(),
                            callable,
                            non_union_args.clone().into_iter(),
                            &|| args_node_ref,
                            result_context,
                            None,
                        )
                    } else {
                        calculate_callable_type_vars_and_return(
                            i_s,
                            callable,
                            non_union_args.clone().into_iter(),
                            &|| args_node_ref,
                            false,
                            result_context,
                            None,
                        )
                    }
                });
                if had_error {
                    todo!()
                }
                match calculated_type_args.matches {
                    SignatureMatch::True { .. } => {
                        if search_init {
                            todo!()
                        } else {
                            return UnionMathResult::Match {
                                result: Type::new(&callable.content.result_type)
                                    .execute_and_resolve_type_vars(
                                        i_s,
                                        &calculated_type_args,
                                        self.class.as_ref(),
                                        &|| {
                                            class
                                                .map(|c| c.as_db_type(i_s.db))
                                                .unwrap_or(DbType::Self_)
                                        },
                                    )
                                    .as_db_type(i_s),
                                first_similar_index: i,
                            };
                        }
                    }
                    SignatureMatch::TrueWithAny { argument_indices } => todo!(),
                    SignatureMatch::False { similar: true } if first_similar.is_none() => {
                        first_similar = Some(i);
                    }
                    SignatureMatch::False { .. } => (),
                }
            }
            if let Some(first_similar) = first_similar {
                UnionMathResult::FirstSimilarIndex(first_similar)
            } else {
                UnionMathResult::NoMatch
            }
        }
    }

    fn variants(&self, i_s: &InferenceState<'db, '_>, is_init: bool) -> Box<[Box<str>]> {
        self.overload
            .iter_functions()
            .map(|callable| {
                let func =
                    Function::new(NodeRef::from_link(i_s.db, callable.defined_at), self.class);
                func.format_overload_variant(i_s, is_init)
            })
            .collect()
    }

    fn fallback_type(&self, i_s: &InferenceState<'db, '_>) -> Inferred {
        let mut t: Option<Type> = None;
        for callable in self.overload.iter_functions() {
            let f_t = Type::new(&callable.result_type);
            if let Some(old_t) = t.take() {
                t = Some(old_t.merge_matching_parts(i_s.db, f_t))
            } else {
                t = Some(f_t);
            }
        }
        Inferred::from_type(t.unwrap().into_db_type())
    }

    pub fn as_db_type(
        &self,
        i_s: &InferenceState<'db, '_>,
        replace_self_type: Option<ReplaceSelf>,
    ) -> DbType {
        if let Some(replace_self_type) = replace_self_type {
            DbType::FunctionOverload(FunctionOverload::new(
                self.overload
                    .iter_functions()
                    .map(|callable| {
                        replace_class_type_vars_in_callable(
                            i_s.db,
                            &callable.remove_first_param().unwrap(),
                            self.class.as_ref(),
                            replace_self_type,
                        )
                    })
                    .collect(),
            ))
        } else {
            DbType::FunctionOverload(self.overload.clone())
        }
    }

    pub fn as_type(&self, i_s: &InferenceState<'db, '_>) -> Type<'static> {
        Type::owned(self.as_db_type(i_s, None))
    }

    pub fn execute(
        &self,
        i_s: &InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
        result_context: &mut ResultContext,
        on_type_error: OnTypeError<'db, '_>,
    ) -> Inferred {
        debug!("Execute overloaded function {}", self.name(i_s.db));
        match self.find_matching_function(i_s, args, None, false, result_context, on_type_error) {
            OverloadResult::Single(callable) => {
                callable.execute(i_s, args, on_type_error, result_context)
            }
            OverloadResult::Union(t) => Inferred::from_type(t),
            OverloadResult::NotFound => self.fallback_type(i_s),
        }
    }

    pub fn name(&self, db: &'a Database) -> &'a str {
        self.overload
            .iter_functions()
            .next()
            .unwrap()
            .name
            .unwrap_or_else(|| todo!())
            .as_str(db)
    }
}

fn are_any_arguments_ambiguous_in_overload(
    db: &Database,
    a: &[ArgumentIndexWithParam],
    b: &[ArgumentIndexWithParam],
) -> bool {
    // This function checks if an argument with an Any (like List[Any]) makes it unclear which
    // overload would need to be chosen. Please have a look at the test
    // `testOverloadWithOverlappingItemsAndAnyArgument4` for more information.
    for p1 in a {
        for p2 in b {
            if p1.argument_index == p2.argument_index && p1.type_ != p2.type_ {
                return true;
            }
        }
    }
    false
}

pub fn format_pretty_function_like<'db: 'x, 'x, P: Param<'x>>(
    format_data: &FormatData<'db, '_, '_, '_>,
    class: Option<Class>,
    avoid_self_annotation: bool,
    name: &str,
    type_vars: Option<&TypeVarLikes>,
    params: impl Iterator<Item = P>,
    return_type: Option<Type>,
) -> Box<str> {
    let db = format_data.db;
    let not_reveal_type = format_data.style != FormatStyle::MypyRevealType;

    let mut previous_kind = None;
    let mut had_kwargs_separator = false;
    let mut args = params
        .enumerate()
        .map(|(i, p)| {
            let specific = p.specific(db);
            let annotation_str = match &specific {
                WrappedParamSpecific::PositionalOnly(t)
                | WrappedParamSpecific::PositionalOrKeyword(t)
                | WrappedParamSpecific::KeywordOnly(t)
                | WrappedParamSpecific::Starred(WrappedStarred::ArbitraryLength(t))
                | WrappedParamSpecific::DoubleStarred(WrappedDoubleStarred::ValueType(t)) => t
                    .as_ref()
                    .map(|t| format_function_type(format_data, t, class)),
                WrappedParamSpecific::Starred(WrappedStarred::ParamSpecArgs(u)) => todo!(),
                WrappedParamSpecific::DoubleStarred(WrappedDoubleStarred::ParamSpecKwargs(u)) => {
                    todo!()
                }
            };
            let current_kind = p.kind(db);
            let stars = match current_kind {
                ParamKind::Starred => "*",
                ParamKind::DoubleStarred => "**",
                _ => "",
            };
            let mut out = if i == 0 && avoid_self_annotation && stars.is_empty() {
                p.name(db).unwrap().to_owned()
            } else {
                let mut out = if current_kind == ParamKind::PositionalOnly {
                    annotation_str.unwrap_or_else(|| Box::from("Any")).into()
                } else {
                    format!(
                        "{stars}{}: {}",
                        p.name(db).unwrap(),
                        annotation_str.as_deref().unwrap_or("Any")
                    )
                };
                if previous_kind == Some(ParamKind::PositionalOnly)
                    && current_kind != ParamKind::PositionalOnly
                    && not_reveal_type
                {
                    out = format!("/, {out}")
                }
                out
            };
            if matches!(&specific, WrappedParamSpecific::KeywordOnly(_)) && !had_kwargs_separator {
                had_kwargs_separator = true;
                out = format!("*, {out}");
            }
            had_kwargs_separator |= matches!(specific, WrappedParamSpecific::Starred(_));
            if p.has_default() {
                if not_reveal_type {
                    out += " = ...";
                } else {
                    out += " =";
                }
            }
            previous_kind = Some(current_kind);
            out
        })
        .collect::<Vec<_>>()
        .join(", ");
    if previous_kind == Some(ParamKind::PositionalOnly) && not_reveal_type {
        args += ", /";
    }
    format_pretty_function_with_params(format_data, class, type_vars, return_type, name, &args)
}

pub fn format_pretty_function_with_params(
    format_data: &FormatData,
    class: Option<Class>,
    type_vars: Option<&TypeVarLikes>,
    return_type: Option<Type>,
    name: &str,
    params: &str,
) -> Box<str> {
    let type_var_string = type_vars.map(|type_vars| {
        format!(
            "[{}] ",
            type_vars
                .iter()
                .map(|t| match t {
                    TypeVarLike::TypeVar(t) => {
                        let mut s = t.name(format_data.db).to_owned();
                        match &t.kind {
                            TypeVarKind::Unrestricted => (),
                            TypeVarKind::Bound(bound) => {
                                s += &format!(" <: {}", Type::new(bound).format(format_data));
                            }
                            TypeVarKind::Constraints(constraints) => {
                                s += &format!(
                                    " in ({})",
                                    constraints
                                        .iter()
                                        .map(|t| Type::new(t).format(format_data))
                                        .collect::<Vec<_>>()
                                        .join(", ")
                                );
                            }
                        }
                        s
                    }
                    TypeVarLike::TypeVarTuple(t) => todo!(),
                    TypeVarLike::ParamSpec(s) => s.name(format_data.db).into(),
                })
                .collect::<Vec<_>>()
                .join(", "),
        )
    });
    let type_var_str = type_var_string.as_deref().unwrap_or("");
    let result_string = return_type
        .as_ref()
        .filter(|t| {
            format_data.style != FormatStyle::MypyRevealType || !matches!(t.as_ref(), DbType::None)
        })
        .map(|t| format_function_type(format_data, t, class));

    if let Some(result_string) = result_string {
        format!("def {type_var_str}{name}({params}) -> {result_string}").into()
    } else {
        format!("def {type_var_str}{name}({params})").into()
    }
}

fn format_function_type(format_data: &FormatData, t: &Type, class: Option<Class>) -> Box<str> {
    if let Some(func_class) = class {
        let t = t.replace_type_var_likes_and_self(
            format_data.db,
            &mut |usage| {
                maybe_class_usage(format_data.db, &func_class, &usage)
                    .unwrap_or_else(|| usage.into_generic_item())
            },
            &|| todo!(),
        );
        t.format(format_data)
    } else {
        t.format(format_data)
    }
}

fn kind_of_decorators(
    i_s: &InferenceState,
    file: &PythonFile,
    decorated: Decorated,
) -> FunctionKind {
    for decorator in decorated.decorators().iter() {
        if let InferredDecorator::FunctionKind(kind) = infer_decorator(i_s, file, decorator) {
            return kind;
        }
    }
    FunctionKind::Function
}

fn infer_decorator(
    i_s: &InferenceState,
    file: &PythonFile,
    decorator: Decorator,
) -> InferredDecorator {
    let node_ref = NodeRef::new(file, decorator.index());
    let mut inference = file.inference(i_s);
    let redirect = if node_ref.point().calculated() {
        inference.check_point_cache(node_ref.node_index).unwrap()
    } else {
        let i = inference.infer_named_expression(decorator.named_expression());
        i.save_redirect(i_s, file, node_ref.node_index)
    };
    if let Some(saved_link) = redirect.maybe_saved_link() {
        let node_ref = NodeRef::from_link(i_s.db, saved_link);
        if saved_link == i_s.db.python_state.overload_link() {
            return InferredDecorator::Overload;
        }
        // All these cases are classes.
        if let Some(class_def) = node_ref.maybe_class() {
            if saved_link == i_s.db.python_state.classmethod_node_ref().as_link() {
                return InferredDecorator::FunctionKind(FunctionKind::Classmethod);
            }
            if saved_link == i_s.db.python_state.staticmethod_node_ref().as_link() {
                return InferredDecorator::FunctionKind(FunctionKind::Staticmethod);
            }
            if saved_link == i_s.db.python_state.abstractmethod_link() {
                return InferredDecorator::Abstractmethod;
            }
            let class = Class::from_non_generic_link(i_s.db, saved_link);
            if class.class_link_in_mro(i_s.db, i_s.db.python_state.property_node_ref().as_link())
                || saved_link == i_s.db.python_state.abstractproperty_link()
            {
                return InferredDecorator::FunctionKind(FunctionKind::Property { writable: false });
            }
        }
    }
    InferredDecorator::Inferred(redirect)
}

enum InferredDecorator {
    FunctionKind(FunctionKind),
    Inferred(Inferred),
    Overload,
    Abstractmethod,
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
    pub yield_type: DbType,
    pub send_type: Option<DbType>,
    pub return_type: Option<DbType>,
}

impl GeneratorType {
    pub fn from_type(db: &Database, t: Type) -> Option<Self> {
        match t.as_ref() {
            DbType::Class(c)
                if c.link == db.python_state.iterator_link()
                    || c.link == db.python_state.iterable_link()
                    || c.link == db.python_state.async_iterator_link()
                    || c.link == db.python_state.async_iterable_link() =>
            {
                let cls = Class::from_generic_class(db, c);
                Some(GeneratorType {
                    yield_type: cls.nth_type_argument(db, 0),
                    send_type: None,
                    return_type: None,
                })
            }
            DbType::Class(c) if c.link == db.python_state.generator_link() => {
                let cls = Class::from_generic_class(db, c);
                Some(GeneratorType {
                    yield_type: cls.nth_type_argument(db, 0),
                    send_type: Some(cls.nth_type_argument(db, 1)),
                    return_type: Some(cls.nth_type_argument(db, 2)),
                })
            }
            DbType::Class(c) if c.link == db.python_state.async_generator_link() => {
                let cls = Class::from_generic_class(db, c);
                Some(GeneratorType {
                    yield_type: cls.nth_type_argument(db, 0),
                    send_type: Some(cls.nth_type_argument(db, 1)),
                    return_type: None,
                })
            }
            DbType::Union(union) => union.iter().fold(None, |a, b| {
                if let Some(b) = Self::from_type(db, Type::new(b)) {
                    if let Some(a) = a {
                        let optional_union = |t1: Option<DbType>, t2: Option<DbType>| {
                            if let Some(t1) = t1 {
                                if let Some(t2) = t2 {
                                    Some(t1.union(db, t2))
                                } else {
                                    Some(t1)
                                }
                            } else {
                                t2
                            }
                        };
                        Some(Self {
                            yield_type: a.yield_type.union(db, b.yield_type),
                            // TODO is taking the Union here correct, since its contravariant?
                            send_type: optional_union(a.send_type, b.send_type),
                            return_type: optional_union(a.return_type, b.return_type),
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
