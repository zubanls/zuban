use std::{borrow::Cow, cell::RefCell, sync::Arc};

use parsa_python_cst::ParamKind;

use crate::{
    arguments::{CombinedArgs, KnownArgsWithCustomAddIssue},
    database::OverloadDefinition,
    file::use_cached_annotation_or_type_comment,
    inferred::{BoundMethodState, InferredState},
    matching::{
        Generics, calculate_property_return, create_signature_without_self_for_callable,
        match_self_type, maybe_class_usage, replace_class_type_vars,
    },
    prelude::*,
    type_::{
        ClassGenerics, FunctionKind, FunctionOverload, GenericsList, PropertySetter,
        PropertySetterType,
    },
    type_helpers::{
        BoundMethod, BoundMethodFunction, Callable, FirstParamProperties, Function,
        OverloadedFunction, TypeOrClass,
    },
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd)]
pub(crate) struct MroIndex(pub u32);

impl From<usize> for MroIndex {
    fn from(item: usize) -> Self {
        Self(item as u32)
    }
}

impl<'db: 'slf, 'slf> Inferred {
    fn new_bound_method(instance: Type, mro_index: MroIndex, func_link: PointLink) -> Self {
        Self {
            state: InferredState::BoundMethod(BoundMethodState {
                instance,
                mro_index,
                func_link,
            }),
        }
    }

    pub(super) fn load_bound_method_class<'a: 'slf>(
        i_s: &InferenceState<'db, 'a>,
        instance: &'slf Type,
        mro_index: MroIndex,
    ) -> Class<'slf> {
        let Some(instance_class) = instance.inner_generic_class(i_s) else {
            unreachable!("{instance:?}")
        };
        let Some((_, class_t)) = instance_class
            .mro_without_remap(i_s.db, false)
            .nth(mro_index.0 as usize)
        else {
            // Happens with super().__init__ when self: SomeProtocol.
            return i_s.db.python_state.object_class();
        };

        // Mro classes are never owned, because they are saved on classes.
        match class_t {
            TypeOrClass::Class(class) => class,
            TypeOrClass::Type(t) => match t {
                Cow::Borrowed(Type::Dataclass(d)) => d.class(i_s.db),
                _ => unreachable!("{t:?}"),
            },
        }
    }

    pub(crate) fn bind_instance_descriptors(
        self,
        i_s: &InferenceState,
        for_name: &str,
        instance: Type,
        func_class: Class,
        add_issue: impl Fn(IssueKind) -> bool,
        mro_index: MroIndex,
        disallow_lazy_bound_method: bool,
        avoid_inferring_return_types: bool,
    ) -> Option<(Self, AttributeKind)> {
        self.bind_instance_descriptors_internal(
            i_s,
            for_name,
            instance,
            func_class,
            add_issue,
            mro_index,
            ApplyDescriptorsKind::All,
            disallow_lazy_bound_method,
            avoid_inferring_return_types,
        )
    }

    fn bind_instance_descriptors_internal(
        self,
        i_s: &InferenceState,
        for_name: &str,
        instance: Type,
        attribute_class: Class,
        add_issue: impl Fn(IssueKind) -> bool,
        mro_index: MroIndex,
        apply_descriptors_kind: ApplyDescriptorsKind,
        disallow_lazy_bound_method: bool,
        avoid_inferring_return_types: bool,
    ) -> Option<(Self, AttributeKind)> {
        match &self.state {
            InferredState::Saved(definition) => {
                let node_ref = NodeRef::from_link(i_s.db, *definition);
                let point = node_ref.point();
                match point.kind() {
                    PointKind::Specific => match point.specific() {
                        Specific::Function => {
                            let func = prepare_func(i_s, *definition, attribute_class);
                            let attr_kind = AttributeKind::DefMethod { is_final: false };
                            if !func.as_node().params().iter().next().is_some_and(|p| {
                                matches!(
                                    p.kind(),
                                    ParamKind::PositionalOnly
                                        | ParamKind::PositionalOrKeyword
                                        | ParamKind::Star
                                )
                            }) {
                                add_issue(IssueKind::NotAcceptingSelfArgument {
                                    function_name: Box::from(func.name()),
                                    callable: func
                                        .as_callable(i_s, FirstParamProperties::None)
                                        .format(&FormatData::new_short(i_s.db))
                                        .into(),
                                });
                            }
                            return if let Some(first_type) = func.first_param_annotation_type(i_s) {
                                Some((
                                    infer_callable_with_first_param_annotation(
                                        i_s,
                                        func,
                                        &first_type,
                                        &attribute_class,
                                        instance,
                                        add_issue,
                                    ),
                                    attr_kind,
                                ))
                            } else if avoid_inferring_return_types {
                                Some((
                                    Self::from_type(
                                        BoundMethod::new(
                                            &instance,
                                            BoundMethodFunction::Function(func),
                                        )
                                        .as_type_without_inferring_returns(i_s),
                                    ),
                                    attr_kind,
                                ))
                            } else if disallow_lazy_bound_method
                                || instance.inner_generic_class(i_s).is_none()
                            {
                                Some((
                                    Self::from_type(
                                        BoundMethod::new(
                                            &instance,
                                            BoundMethodFunction::Function(func),
                                        )
                                        .as_type(i_s),
                                    ),
                                    attr_kind,
                                ))
                            } else {
                                Some((
                                    Self::new_bound_method(instance, mro_index, *definition),
                                    attr_kind,
                                ))
                            };
                        }
                        specific if specific.is_annotation_or_type_comment() => {
                            let t = use_cached_annotation_or_type_comment(i_s, node_ref);
                            let is_remapped = matches!(
                                specific,
                                Specific::AnnotationOrTypeCommentWithTypeVars
                                | Specific::AnnotationOrTypeCommentFinal
                                if !attribute_class.needs_generic_remapping_for_attributes(i_s, &t)
                            );
                            let t = if is_remapped {
                                replace_class_type_vars(i_s.db, &t, &attribute_class, &|| {
                                    Some(instance.clone())
                                })
                            } else {
                                Cow::Borrowed(t.as_ref())
                            };
                            let is_class_var =
                                specific == Specific::AnnotationOrTypeCommentClassVar;
                            let attr_kind = if is_class_var {
                                AttributeKind::ClassVar
                            } else if specific == Specific::AnnotationOrTypeCommentFinal {
                                AttributeKind::Final
                            } else {
                                AttributeKind::AnnotatedAttribute
                            };
                            if let Some(r) = Self::bind_instance_descriptors_for_type(
                                i_s,
                                for_name,
                                instance,
                                attribute_class,
                                add_issue,
                                &t,
                                if is_class_var {
                                    ApplyDescriptorsKind::All
                                } else {
                                    ApplyDescriptorsKind::NoBoundMethod
                                },
                                avoid_inferring_return_types,
                            ) {
                                return r.map(|(inf, _)| (inf, attr_kind));
                            }
                            if is_remapped {
                                return Some((Inferred::from_type(t.into_owned()), attr_kind));
                            }
                            return Some((self, attr_kind));
                        }
                        Specific::PartialNone if i_s.db.project.flags.local_partial_types => {
                            // Looking up partials means that they have not yet been processed and
                            // will be inferred as None | Any. I'm not 100% sure this is always
                            // safe, but at this point we haven't found code that
                            return Some((
                                Inferred::from_type(i_s.db.python_state.any_or_none.clone()),
                                AttributeKind::Attribute,
                            ));
                        }
                        _ => (),
                    },
                    PointKind::Complex => {
                        match node_ref.maybe_complex().unwrap() {
                            ComplexPoint::FunctionOverload(o) => {
                                if i_s.db.project.flags.disallow_deprecated
                                    && let Some(i) = &o.implementation
                                    && let Some(reason) = &i.callable.deprecated_reason
                                    && !matches!(i.callable.kind, FunctionKind::Staticmethod)
                                {
                                    add_issue(IssueKind::Deprecated {
                                        identifier: format!(
                                            "function {}",
                                            i.callable.qualified_name(i_s.db)
                                        )
                                        .into(),
                                        reason: reason.clone(),
                                    });
                                }
                                let kind = o.kind();
                                let attr_kind = match kind {
                                    FunctionKind::Staticmethod => {
                                        return Some((
                                            self,
                                            AttributeKind::Staticmethod {
                                                is_final: o.is_final,
                                            },
                                        ));
                                    }
                                    FunctionKind::Function { .. } => AttributeKind::DefMethod {
                                        is_final: o.is_final,
                                    },
                                    FunctionKind::Classmethod { .. } => {
                                        AttributeKind::Classmethod {
                                            is_final: o.is_final,
                                        }
                                    }
                                    FunctionKind::Property { .. } => unreachable!(),
                                };

                                let has_self_arguments = o
                                    .iter_functions()
                                    .any(|c| c.kind.had_first_self_or_class_annotation());
                                if has_self_arguments {
                                    let results: Vec<_> = o
                                        .iter_functions()
                                        .filter_map(|callable| {
                                            match kind {
                                                FunctionKind::Function { .. } => {
                                                    if let Some(t) =
                                                        callable.first_positional_type()
                                                    {
                                                        create_signature_without_self_for_callable(
                                                            i_s,
                                                            for_name,
                                                            callable,
                                                            &instance,
                                                            &attribute_class,
                                                            &t,
                                                        )
                                                    } else {
                                                        None
                                                    }
                                                }
                                                FunctionKind::Classmethod { .. } => {
                                                    infer_class_method_on_instance(
                                                        i_s,
                                                        &instance,
                                                        attribute_class,
                                                        callable,
                                                    )
                                                }
                                                FunctionKind::Staticmethod
                                                | FunctionKind::Property { .. } => unreachable!(),
                                            }
                                            .map(Arc::new)
                                        })
                                        .collect();
                                    match results.len() {
                                        0 => {
                                            let overload = OverloadedFunction::new(
                                                &o.functions,
                                                Some(attribute_class),
                                            );
                                            let t = IssueKind::InvalidClassMethodFirstArgument {
                                                argument_type: Type::Type(Arc::new(instance))
                                                    .format_short(i_s.db),
                                                function_name: Box::from(overload.name(i_s.db)),
                                                // Mypy just picks the first function.
                                                callable: o
                                                    .functions
                                                    .iter_functions()
                                                    .next()
                                                    .unwrap()
                                                    .format(&FormatData::new_short(i_s.db))
                                                    .into(),
                                            };
                                            add_issue(t);
                                            return Some((Self::new_any_from_error(), attr_kind));
                                        }
                                        1 => {
                                            return Some((
                                                Inferred::from_type(Type::Callable(
                                                    results.into_iter().next().unwrap(),
                                                )),
                                                attr_kind,
                                            ));
                                        }
                                        _ => {
                                            return Some((
                                                Inferred::from_type(Type::FunctionOverload(
                                                    FunctionOverload::new(
                                                        results.into_iter().collect(),
                                                    ),
                                                )),
                                                attr_kind,
                                            ));
                                        }
                                    }
                                }
                                return Some((
                                    if disallow_lazy_bound_method
                                        || instance.inner_generic_class(i_s).is_none()
                                    {
                                        Self::from_type(
                                            OverloadedFunction::new(
                                                &o.functions,
                                                Some(attribute_class),
                                            )
                                            .as_type(i_s, Some(&|| instance.clone())),
                                        )
                                    } else {
                                        Self::new_bound_method(instance, mro_index, *definition)
                                    },
                                    attr_kind,
                                ));
                            }
                            ComplexPoint::TypeInstance(t) => {
                                if let Some(inf) = Self::bind_instance_descriptors_for_type(
                                    i_s,
                                    for_name,
                                    instance,
                                    attribute_class,
                                    add_issue,
                                    t,
                                    apply_descriptors_kind,
                                    avoid_inferring_return_types,
                                ) {
                                    return inf;
                                }
                            }
                            ComplexPoint::WidenedType(widened) => {
                                if let Some(inf) = Self::bind_instance_descriptors_for_type(
                                    i_s,
                                    for_name,
                                    instance,
                                    attribute_class,
                                    add_issue,
                                    &widened.widened,
                                    apply_descriptors_kind,
                                    avoid_inferring_return_types,
                                ) {
                                    return inf;
                                } else {
                                    return Some((
                                        Inferred::from_type(widened.widened.clone()),
                                        AttributeKind::Attribute,
                                    ));
                                }
                            }
                            _ => (),
                        }
                    }
                    _ => (),
                }
            }
            InferredState::UnsavedComplex(complex) => {
                if let ComplexPoint::TypeInstance(t) = complex
                    && let Some(inf) = Self::bind_instance_descriptors_for_type(
                        i_s,
                        for_name,
                        instance,
                        attribute_class,
                        add_issue,
                        t,
                        apply_descriptors_kind,
                        avoid_inferring_return_types,
                    )
                {
                    return inf;
                }
            }
            InferredState::UnsavedFileReference(_)
            | InferredState::UnsavedSpecific(_)
            | InferredState::BoundMethod { .. } => (),
        }
        Some((self, AttributeKind::Attribute))
    }

    fn bind_instance_descriptors_for_type(
        i_s: &InferenceState,
        for_name: &str,
        instance: Type,
        attribute_class: Class,
        add_issue: impl Fn(IssueKind) -> bool,
        t: &Type,
        apply_descriptors_kind: ApplyDescriptorsKind,
        avoid_inferring_return_types: bool,
    ) -> Option<Option<(Self, AttributeKind)>> {
        let mut t = t; // Weird lifetime issue
        let add_invalid_self_arg = |c: &CallableContent| {
            add_issue(IssueKind::InvalidSelfArgument {
                argument_type: instance.format_short(i_s.db),
                function_name: Box::from(
                    c.name
                        .as_ref()
                        .map(|n| n.as_str(i_s.db))
                        .unwrap_or(for_name),
                ),
                callable: c.format(&FormatData::new_short(i_s.db)).into(),
            })
        };
        match t {
            Type::Callable(c) => {
                if i_s.db.project.flags.disallow_deprecated
                    && let Some(reason) = &c.deprecated_reason
                {
                    add_issue(IssueKind::Deprecated {
                        identifier: format!("function {}", c.qualified_name(i_s.db)).into(),
                        reason: reason.clone(),
                    });
                    return Self::bind_instance_descriptors_for_type(
                        i_s,
                        for_name,
                        instance,
                        attribute_class,
                        add_issue,
                        &Type::Callable(c.remove_deprecated_reason()),
                        apply_descriptors_kind,
                        avoid_inferring_return_types,
                    );
                }
                match &c.kind {
                    FunctionKind::Function { .. }
                        if !i_s.db.mypy_compatible()
                            // ParamSpecs are bound and can only be used from self
                            && c.params.maybe_param_spec().is_none()
                            && attribute_class.maybe_dataclass(i_s.db).is_none()
                            || !matches!(
                                apply_descriptors_kind,
                                ApplyDescriptorsKind::NoBoundMethod
                            ) =>
                    {
                        debug_assert!(matches!(c.kind, FunctionKind::Function { .. }));
                        if let Some(f) = c.first_positional_type() {
                            let mut new_c = create_signature_without_self_for_callable(
                                i_s,
                                for_name,
                                c,
                                &instance,
                                &attribute_class,
                                &f,
                            )
                            .map(Arc::new)
                            .unwrap_or_else(|| {
                                add_invalid_self_arg(c);
                                i_s.db.python_state.any_callable_from_error.clone()
                            });
                            if avoid_inferring_return_types
                                && let Some(func) = new_c.maybe_original_function(i_s.db)
                                && func.return_annotation().is_none()
                            {
                                let mut new = new_c.as_ref().clone();
                                new.return_type = Type::Any(AnyCause::Unannotated);
                                new_c = Arc::new(new)
                            }
                            return Some(Some((
                                Inferred::from_type(Type::Callable(new_c)),
                                AttributeKind::DefMethod {
                                    is_final: c.is_final,
                                },
                            )));
                        } else {
                            add_issue(IssueKind::NotAcceptingSelfArgument {
                                function_name: Box::from(for_name),
                                callable: c.format(&FormatData::new_short(i_s.db)).into(),
                            });
                        }
                    }
                    FunctionKind::Function { .. } => (),
                    FunctionKind::Property { setter_type, .. } => {
                        return Some(Some(
                            if let Some(t) = calculate_property_return(
                                i_s,
                                &instance,
                                &attribute_class,
                                c,
                                avoid_inferring_return_types,
                            ) {
                                let setter_type = setter_type.as_ref().map(|s| match &s.type_ {
                                    PropertySetterType::OtherType(t)
                                        if attribute_class
                                            .needs_generic_remapping_for_attributes(i_s, t) =>
                                    {
                                        let t = replace_class_type_vars(
                                            i_s.db,
                                            t,
                                            &attribute_class,
                                            &|| Some(instance.clone()),
                                        );
                                        Arc::new(PropertySetter {
                                            type_: PropertySetterType::OtherType(t.into_owned()),
                                            deprecated_reason: None,
                                        })
                                    }
                                    _ => s.clone(),
                                });
                                (
                                    Inferred::from_type(t),
                                    AttributeKind::Property {
                                        setter_type,
                                        is_abstract: c.is_abstract,
                                        is_final: c.is_final,
                                    },
                                )
                            } else {
                                add_invalid_self_arg(c);
                                (Inferred::new_any_from_error(), AttributeKind::Attribute)
                            },
                        ));
                    }
                    FunctionKind::Classmethod { .. } => {
                        let result =
                            infer_class_method_on_instance(i_s, &instance, attribute_class, c);
                        if result.is_none() {
                            let t = IssueKind::InvalidClassMethodFirstArgument {
                                argument_type: Type::Type(Arc::new(instance)).format_short(i_s.db),
                                function_name: c.name(i_s.db).into(),
                                callable: t.format_short(i_s.db),
                            };
                            add_issue(t);
                            return Some(Some((
                                Self::new_any_from_error(),
                                AttributeKind::Attribute,
                            )));
                        }
                        let is_final = c.is_final;
                        return Some(result.map(|mut c| {
                            if avoid_inferring_return_types
                                && let Some(func) = c.maybe_original_function(i_s.db)
                                && func.return_annotation().is_none()
                            {
                                c.return_type = Type::Any(AnyCause::Unannotated);
                            }
                            (
                                callable_into_inferred(c),
                                AttributeKind::Classmethod { is_final },
                            )
                        }));
                    }
                    FunctionKind::Staticmethod => {
                        let mut t = t.clone();
                        if avoid_inferring_return_types
                            && let Some(func) = c.maybe_original_function(i_s.db)
                            && func.return_annotation().is_none()
                            && let Type::Callable(c) = &t
                        {
                            let mut new_c = c.as_ref().clone();
                            new_c.return_type = Type::Any(AnyCause::Unannotated);
                            t = Type::Callable(Arc::new(new_c));
                        }
                        if t.has_type_vars() && !t.has_untyped_type_params(i_s.db) {
                            t = Type::Callable(Arc::new(c.merge_class_type_vars_detailed(
                                i_s.db,
                                attribute_class,
                                attribute_class,
                                false,
                                || {
                                    recoverable_error!("staticmethod should never have Self");
                                    Type::ERROR
                                },
                            )));
                        }
                        return Some(Some((
                            Inferred::from_type(t),
                            AttributeKind::Staticmethod {
                                is_final: c.is_final,
                            },
                        )));
                    }
                }
            }
            Type::CustomBehavior(custom) => {
                return Some(Some((
                    Inferred::from_type(Type::CustomBehavior(custom.bind(Arc::new(instance)))),
                    AttributeKind::DefMethod { is_final: false },
                )));
            }
            _ => (),
        }

        let mut new = None;
        if attribute_class.needs_generic_remapping_for_attributes(i_s, t) {
            new = Some(replace_class_type_vars(
                i_s.db,
                t,
                &attribute_class,
                &|| Some(instance.clone()),
            ));
            t = new.as_ref().unwrap();
        }

        if let Some(c) = t.inner_generic_class(i_s) {
            if let Some(inf) = c
                .instance()
                .bind_dunder_get(i_s, |i| add_issue(i), instance)
            {
                return Some(Some((inf, AttributeKind::Attribute)));
            }
        }
        // TODO this clone should not be necessary, but there appears to be a bug in the compiler.
        if let Some(new) = new.clone() {
            return Some(Some((
                Inferred::from_type(new.into_owned()),
                AttributeKind::Attribute,
            )));
        }
        None
    }

    pub(crate) fn bind_class_descriptors(
        self,
        i_s: &InferenceState,
        class: &Class,
        attribute_class: Class, // The (sub-)class in which an attribute is defined
        func_class_type: &TypeOrClass,
        add_issue: impl Fn(IssueKind) -> bool,
        apply_descriptors: ApplyClassDescriptorsOrigin,
        as_type_type: Option<&dyn Fn() -> Type>,
    ) -> Option<(Self, AttributeKind)> {
        let mut attr_kind = AttributeKind::Attribute;
        match &self.state {
            InferredState::Saved(definition) => {
                let node_ref = NodeRef::from_link(i_s.db, *definition);
                let point = node_ref.point();
                match point.kind() {
                    PointKind::Specific => match point.specific() {
                        Specific::Function => {
                            let func = Function::new(node_ref, Some(attribute_class));
                            let c = func.as_callable(i_s, FirstParamProperties::None);
                            let c = Arc::new(c.merge_class_type_vars(
                                i_s.db,
                                *class,
                                attribute_class,
                                func_class_type,
                            ));
                            return Some((
                                Inferred::from_type(Type::Callable(c)),
                                AttributeKind::DefMethod { is_final: false },
                            ));
                        }
                        specific @ (Specific::AnnotationOrTypeCommentWithoutTypeVars
                        | Specific::AnnotationOrTypeCommentClassVar
                        | Specific::AnnotationOrTypeCommentWithTypeVars
                        | Specific::AnnotationOrTypeCommentSimpleClassInstance
                        | Specific::AnnotationOrTypeCommentFinal) => {
                            if specific == Specific::AnnotationOrTypeCommentWithTypeVars
                                && apply_descriptors.should_add_ambigous_class_var_access()
                            {
                                add_issue(IssueKind::AmbigousClassVariableAccess);
                            }
                            let t = use_cached_annotation_or_type_comment(
                                i_s,
                                NodeRef::from_link(i_s.db, *definition),
                            );
                            if specific == Specific::AnnotationOrTypeCommentClassVar {
                                attr_kind = AttributeKind::ClassVar
                            } else if specific == Specific::AnnotationOrTypeCommentFinal {
                                attr_kind = AttributeKind::Final
                            } else {
                                attr_kind = AttributeKind::AnnotatedAttribute
                            };
                            if let Some(r) = Self::bind_class_descriptors_for_type(
                                i_s,
                                class,
                                attribute_class,
                                add_issue,
                                apply_descriptors,
                                &t,
                                as_type_type,
                                func_class_type,
                            ) {
                                return r.map(|inf| (inf, attr_kind));
                            }
                        }
                        _ => (),
                    },
                    PointKind::Complex => match node_ref.maybe_complex().unwrap() {
                        ComplexPoint::FunctionOverload(o) => match o.kind() {
                            FunctionKind::Function { .. } => {
                                return Some((
                                    Inferred::from_type(Type::FunctionOverload(
                                        FunctionOverload::new(
                                            o.iter_functions()
                                                .map(|c| {
                                                    Arc::new(c.merge_class_type_vars(
                                                        i_s.db,
                                                        *class,
                                                        attribute_class,
                                                        func_class_type,
                                                    ))
                                                })
                                                .collect(),
                                        ),
                                    )),
                                    AttributeKind::DefMethod { is_final: false },
                                ));
                            }
                            FunctionKind::Property { .. } => unreachable!(),
                            FunctionKind::Classmethod { .. } => {
                                let Some(inf) =
                                    infer_overloaded_class_method(i_s, *class, attribute_class, o)
                                else {
                                    add_issue(IssueKind::InvalidSelfArgument {
                                        argument_type: class
                                            .as_type_type(i_s.db)
                                            .format_short(i_s.db),
                                        function_name: o
                                            .iter_functions()
                                            .next()
                                            .map(|c| c.name(i_s.db))
                                            .unwrap()
                                            .into(),
                                        callable: self.format_short(i_s),
                                    });
                                    return Some((
                                        Inferred::new_any_from_error(),
                                        AttributeKind::Attribute,
                                    ));
                                };
                                return Some((inf, AttributeKind::Attribute));
                            }
                            FunctionKind::Staticmethod => (),
                        },
                        ComplexPoint::TypeInstance(t) => {
                            if let Type::Callable(c) = t {
                                match c.kind {
                                    FunctionKind::Function { .. } => {
                                        attr_kind = AttributeKind::DefMethod {
                                            is_final: c.is_final,
                                        };
                                    }
                                    FunctionKind::Property { .. } => (),
                                    FunctionKind::Classmethod { .. } => {
                                        attr_kind = AttributeKind::Classmethod {
                                            is_final: c.is_final,
                                        };
                                    }
                                    FunctionKind::Staticmethod => {
                                        attr_kind = AttributeKind::Staticmethod {
                                            is_final: c.is_final,
                                        };
                                    }
                                }
                            }
                            if let Some(r) = Self::bind_class_descriptors_for_type(
                                i_s,
                                class,
                                attribute_class,
                                add_issue,
                                apply_descriptors,
                                t,
                                as_type_type,
                                func_class_type,
                            ) {
                                return r.map(|inf| (inf, attr_kind));
                            }
                        }
                        ComplexPoint::IndirectFinal(t) => {
                            attr_kind = AttributeKind::Final;
                            if let Some(r) = Self::bind_class_descriptors_for_type(
                                i_s,
                                class,
                                attribute_class,
                                add_issue,
                                apply_descriptors,
                                t,
                                as_type_type,
                                func_class_type,
                            ) {
                                return r.map(|inf| (inf, attr_kind));
                            }
                        }
                        ComplexPoint::WidenedType(widened) => {
                            if let Some(r) = Self::bind_class_descriptors_for_type(
                                i_s,
                                class,
                                attribute_class,
                                add_issue,
                                apply_descriptors,
                                &widened.widened,
                                as_type_type,
                                func_class_type,
                            ) {
                                return r.map(|inf| (inf, attr_kind));
                            } else {
                                return Some((
                                    Inferred::from_type(widened.widened.clone()),
                                    attr_kind,
                                ));
                            }
                        }
                        _ => (),
                    },
                    _ => (),
                }
            }
            InferredState::UnsavedComplex(complex) => {
                if let ComplexPoint::TypeInstance(t) = complex
                    && let Some(inf) = Self::bind_class_descriptors_for_type(
                        i_s,
                        class,
                        attribute_class,
                        add_issue,
                        apply_descriptors,
                        t,
                        as_type_type,
                        func_class_type,
                    )
                {
                    return inf.map(|inf| (inf, AttributeKind::Attribute));
                }
            }
            InferredState::UnsavedFileReference(_)
            | InferredState::UnsavedSpecific(_)
            | InferredState::BoundMethod { .. } => (),
        }
        Some((self, attr_kind))
    }

    pub(crate) fn bind_class_descriptors_for_type(
        i_s: &InferenceState,
        class: &Class,
        attribute_class: Class, // The (sub-)class in which an attribute is defined
        add_issue: impl Fn(IssueKind) -> bool,
        apply_descriptors: ApplyClassDescriptorsOrigin,
        t: &Type,
        as_type_type: Option<&dyn Fn() -> Type>,
        func_class_type: &TypeOrClass,
    ) -> Option<Option<Self>> {
        let mut t = t;
        if let Type::Callable(c) = t {
            if i_s.db.project.flags.disallow_deprecated
                && let Some(reason) = &c.deprecated_reason
            {
                add_issue(IssueKind::Deprecated {
                    identifier: format!("function {}", c.qualified_name(i_s.db)).into(),
                    reason: reason.clone(),
                });
                return Self::bind_class_descriptors_for_type(
                    i_s,
                    class,
                    attribute_class,
                    add_issue,
                    apply_descriptors,
                    &Type::Callable(c.remove_deprecated_reason()),
                    as_type_type,
                    func_class_type,
                );
            }
            match c.kind {
                FunctionKind::Function { .. } => {
                    return Some(Some(Inferred::from_type(Type::Callable(Arc::new(
                        c.merge_class_type_vars(i_s.db, *class, attribute_class, func_class_type),
                    )))));
                }
                FunctionKind::Property { .. } => {
                    if apply_descriptors.should_apply() {
                        return Some(Some(Inferred::from_type(
                            i_s.db.python_state.property_type(),
                        )));
                    }
                }
                FunctionKind::Classmethod { .. } => {
                    let result = infer_class_method(i_s, *class, attribute_class, c, as_type_type);
                    if result.is_none() {
                        let inv = IssueKind::InvalidSelfArgument {
                            argument_type: class.as_type_type(i_s.db).format_short(i_s.db),
                            function_name: c.name(i_s.db).into(),
                            callable: t.format_short(i_s.db),
                        };
                        add_issue(inv);
                        return Some(Some(Self::new_any_from_error()));
                    }
                    return Some(result.map(callable_into_inferred));
                }
                FunctionKind::Staticmethod => {
                    if t.has_type_vars() {
                        return Some(Some(Inferred::from_type(Type::Callable(Arc::new(
                            c.merge_class_type_vars_detailed(
                                i_s.db,
                                attribute_class,
                                attribute_class,
                                false,
                                || {
                                    recoverable_error!(
                                        "staticmethod should never have a Self annotation"
                                    );
                                    Type::ERROR
                                },
                            ),
                        )))));
                    }
                }
            }
        }
        let mut new = None;
        if attribute_class.needs_generic_remapping_for_attributes(i_s, t) {
            new = Some(replace_class_type_vars(
                i_s.db,
                t,
                &attribute_class,
                &|| {
                    Some({
                        if let Some(as_type_type) = as_type_type {
                            let Type::Type(t) = as_type_type() else {
                                unreachable!()
                            };
                            (*t).clone()
                        } else {
                            class.as_type(i_s.db)
                        }
                    })
                },
            ));
            t = new.as_ref().unwrap();
        }

        if apply_descriptors.should_apply()
            && let Some(c) = t.inner_generic_class(i_s)
        {
            if let Some(inf) = c
                .instance()
                .type_lookup(i_s, &add_issue, "__get__")
                .into_maybe_inferred()
            {
                let class_as_inferred = class.as_inferred(i_s);
                return Some(Some(inf.execute(
                    i_s,
                    &CombinedArgs::new(
                        &KnownArgsWithCustomAddIssue::new(&Inferred::new_none(), &add_issue),
                        &KnownArgsWithCustomAddIssue::new(&class_as_inferred, &add_issue),
                    ),
                )));
            }
        }
        // TODO this clone should not be necessary, but there appears to be a bug in the compiler.
        if let Some(new) = new.clone() {
            return Some(Some(Inferred::from_type(new.into_owned())));
        }
        None
    }

    pub fn bind_new_descriptors(
        self,
        i_s: &InferenceState,
        class: &Class,
        class_of_attribute: Option<Class>,
        add_issue: &dyn Fn(IssueKind) -> bool,
    ) -> Self {
        debug!("Bind __new__ descriptors");
        let indent = debug_indent();
        // This method exists for __new__
        let attribute_class = class_of_attribute.unwrap_or(*class);
        let to_class_method = |callable| {
            let result = infer_class_method(
                i_s,
                *class,
                attribute_class,
                callable,
                Some(&|| class.as_type_type(i_s.db)),
            );
            if result.is_none()
                && let Some(t) = callable.first_positional_type()
            {
                let class_t = class.as_type_type(i_s.db);
                add_issue(IssueKind::InvalidSelfArgument {
                    argument_type: class_t.format_short(i_s.db),
                    function_name: "__new__".into(),
                    callable: t.format_short(i_s.db),
                });
            }
            result
        };
        match &self.state {
            InferredState::Saved(definition) => {
                let node_ref = NodeRef::from_link(i_s.db, *definition);
                let point = node_ref.point();
                match point.kind() {
                    PointKind::Specific => {
                        if point.specific() == Specific::Function {
                            let func = Function::new(node_ref, Some(attribute_class));
                            if let Some(result) =
                                to_class_method(&func.as_callable(i_s, FirstParamProperties::None))
                            {
                                return callable_into_inferred(result);
                            } else {
                                // e.g. def __new__() -> X: ...
                                // Error will be added to the class and not the caller
                                return Self::new_any_from_error();
                            }
                        }
                    }
                    PointKind::Complex => match node_ref.maybe_complex().unwrap() {
                        ComplexPoint::FunctionOverload(o) => {
                            let Some(inf) =
                                infer_overloaded_class_method(i_s, *class, attribute_class, o)
                            else {
                                drop(indent);
                                debug!(
                                    "Issue: Class method for __new__ cannot be created, using any instead"
                                );
                                return Self::new_any_from_error();
                            };
                            return inf;
                        }
                        complex => {
                            if let Some(Type::Callable(c)) = complex.maybe_instance() {
                                let Some(c) = to_class_method(c) else {
                                    return Self::new_any_from_error();
                                };
                                return Inferred::from_type(Type::Callable(Arc::new(c)));
                            }
                        }
                    },
                    _ => (),
                }
            }
            InferredState::UnsavedComplex(ComplexPoint::TypeInstance(Type::Callable(c))) => {
                // This is reached by NamedTuples. Not sure it this reached otherwise as well.
                let result = to_class_method(c);
                if let Some(result) = result {
                    return callable_into_inferred(result);
                } else {
                    return Self::new_any_from_error();
                }
            }
            _ => (),
        }
        self
    }
}

fn callable_into_inferred(callable: CallableContent) -> Inferred {
    Inferred::from_type(Type::Callable(Arc::new(callable)))
}

fn prepare_func<'db, 'class>(
    i_s: &InferenceState<'db, '_>,
    definition: PointLink,
    func_class: Class<'class>,
) -> Function<'db, 'class> {
    let node_ref = NodeRef::from_link(i_s.db, definition);

    Function::new(node_ref, Some(func_class))
}

enum ApplyDescriptorsKind {
    All,
    NoBoundMethod,
}

#[derive(Copy, Clone)]
pub(crate) enum ApplyClassDescriptorsOrigin {
    ClassAccess,
    AssignToClass,
    InstanceSetattrAccess,
    AssignContext,
}

impl ApplyClassDescriptorsOrigin {
    pub fn should_apply(&self) -> bool {
        matches!(self, Self::ClassAccess)
    }

    fn should_add_ambigous_class_var_access(&self) -> bool {
        matches!(self, Self::ClassAccess | Self::AssignToClass)
    }
}

#[derive(Debug, PartialEq, Clone)]
pub(crate) enum AttributeKind {
    AnnotatedAttribute,
    Attribute,
    ClassVar,
    Final,
    Property {
        setter_type: Option<Arc<PropertySetter>>,
        is_final: bool,
        is_abstract: bool,
    },
    Classmethod {
        is_final: bool,
    },
    Staticmethod {
        is_final: bool,
    },
    DefMethod {
        is_final: bool,
    },
}

impl AttributeKind {
    pub fn is_read_only_property(&self) -> bool {
        matches!(
            self,
            Self::Property {
                setter_type: None,
                ..
            }
        )
    }

    pub fn classmethod_or_staticmethod(&self) -> bool {
        matches!(self, Self::Classmethod { .. } | Self::Staticmethod { .. })
    }

    pub fn classvar_like(&self) -> bool {
        matches!(
            self,
            Self::ClassVar
                | Self::DefMethod { .. }
                | Self::Property { .. }
                | Self::Classmethod { .. }
                | Self::Staticmethod { .. }
        )
    }

    pub fn is_final(&self) -> bool {
        matches!(
            self,
            Self::Final
                | Self::DefMethod { is_final: true, .. }
                | Self::Property { is_final: true, .. }
                | Self::Classmethod { is_final: true, .. }
                | Self::Staticmethod { is_final: true, .. }
        )
    }

    pub(crate) fn is_writable(&self) -> bool {
        matches!(
            self,
            Self::Attribute
                | Self::AnnotatedAttribute
                | Self::ClassVar
                | Self::Property {
                    setter_type: Some(_),
                    ..
                }
        )
    }

    pub(crate) fn is_overwritable(&self) -> bool {
        matches!(
            self,
            Self::Attribute
                | Self::AnnotatedAttribute
                | Self::ClassVar
                | Self::Property {
                    is_abstract: false,
                    ..
                }
                | Self::Property {
                    is_abstract: true,
                    setter_type: Some(_),
                    ..
                }
        )
    }

    pub(crate) fn property_setter_type(&self) -> Option<&Type> {
        if let Self::Property { setter_type, .. } = self {
            match &setter_type.as_ref()?.type_ {
                PropertySetterType::OtherType(t) => Some(t),
                PropertySetterType::SameTypeFromCachedProperty => None,
            }
        } else {
            None
        }
    }

    pub fn is_attribute(&self) -> bool {
        matches!(
            self,
            Self::AnnotatedAttribute | Self::Attribute | Self::ClassVar | Self::Final
        )
    }

    pub fn is_cached_property(&self) -> bool {
        if let Self::Property { setter_type, .. } = self {
            matches!(
                setter_type.as_ref().map(|s| &s.type_),
                Some(PropertySetterType::SameTypeFromCachedProperty)
            )
        } else {
            false
        }
    }
}

fn infer_callable_with_first_param_annotation(
    i_s: &InferenceState,
    func: Function,
    first_type: &Type,
    attribute_class: &Class,
    instance: Type,
    add_issue: impl Fn(IssueKind) -> bool,
) -> Inferred {
    let as_instance = || instance.clone();
    let mut matcher = Matcher::new_function_matcher(&func, func.type_vars(i_s.db), &as_instance);
    // If __call__ has a self type that is a Callable, just ignore it,
    // because that causes a recursion. It is how Mypy does it in
    // c68bd7ae2cffe8f0377ea9aab54b963b9fac3231
    if !(matches!(first_type, Type::Callable(_)) && func.name() == "__call__")
        && !match_self_type(i_s, &mut matcher, &instance, &attribute_class, first_type)
    {
        add_issue(IssueKind::InvalidSelfArgument {
            argument_type: instance.format_short(i_s.db),
            function_name: Box::from(func.name()),
            callable: func
                .as_type(i_s, FirstParamProperties::None)
                .format_short(i_s.db),
        });
    }
    let callable = func.as_callable(
        i_s,
        FirstParamProperties::Skip {
            to_self_instance: &|| instance.clone(),
        },
    );
    Inferred::new_unsaved_complex(ComplexPoint::TypeInstance(Type::Callable(Arc::new(
        matcher.remove_self_from_callable(i_s, callable),
    ))))
}

fn infer_overloaded_class_method(
    i_s: &InferenceState,
    class: Class,
    attribute_class: Class,
    o: &OverloadDefinition,
) -> Option<Inferred> {
    let functions: Arc<[_]> = o
        .iter_functions()
        .enumerate()
        .filter_map(|(i, callable)| {
            debug!("Bind class method overload member #{i}");
            let indent = debug_indent();
            let Some(c) = infer_class_method(i_s, class, attribute_class, callable, None) else {
                drop(indent);
                debug!("Class method overload member #{i} did not match, skipping it");
                return None;
            };
            Some(Arc::new(c))
        })
        .collect();
    Some(Inferred::from_type(
        CallableLike::from_overload_funcs(functions)?.into(),
    ))
}

pub fn infer_class_method_on_instance<'db: 'class, 'class>(
    i_s: &InferenceState<'db, '_>,
    instance: &Type,
    func_class: Class,
    callable: &CallableContent,
) -> Option<CallableContent> {
    proper_classmethod_callable(
        i_s,
        callable,
        &func_class,
        None,
        || instance.clone(),
        || Type::Type(Arc::new(instance.clone())),
    )
}

pub fn infer_class_method<'db: 'class, 'class>(
    i_s: &InferenceState<'db, '_>,
    mut class: Class<'class>,
    func_class: Class,
    callable: &CallableContent,
    as_type_type: Option<&dyn Fn() -> Type>,
) -> Option<CallableContent> {
    let mut func_class = func_class;
    let class_generics_not_defined_yet = matches!(class.generics, Generics::NotDefinedYet { .. })
        && !class.type_vars(i_s).is_empty();
    if class_generics_not_defined_yet {
        // Check why this is necessary by following class_generics_not_defined_yet.
        let self_generics = Generics::Self_ {
            class_ref: class.node_ref,
        };
        class.generics = self_generics;
        if matches!(func_class.generics, Generics::NotDefinedYet { .. }) {
            func_class.generics = self_generics;
        }
    }

    proper_classmethod_callable(
        i_s,
        callable,
        &func_class,
        class_generics_not_defined_yet.then_some(class),
        || match as_type_type {
            Some(as_type_type) => match as_type_type() {
                Type::Type(t) => (*t).clone(),
                _ => unreachable!(),
            },
            None => class.as_type(i_s.db),
        },
        || match as_type_type {
            Some(as_type_type) => as_type_type(),
            None => class.as_type_type(i_s.db),
        },
    )
}

fn proper_classmethod_callable(
    i_s: &InferenceState,
    original_callable: &CallableContent,
    func_class: &Class,
    class_generics_not_defined_yet: Option<Class>,
    as_type: impl Fn() -> Type,
    as_type_type: impl Fn() -> Type,
) -> Option<CallableContent> {
    let mut class_method_type_var_usage = None;
    let mut callable = original_callable.clone();
    let mut type_vars = callable.type_vars.as_vec();
    match &callable.params {
        CallableParams::Simple(params) => {
            let mut vec = params.to_vec();
            // The first argument in a class param is not relevant if we execute descriptors.
            if vec.is_empty() {
                return None;
            }
            let first_param = vec.remove(0);

            if let Some(t) = first_param.type_.maybe_positional_type() {
                callable.params = CallableParams::Simple(Arc::from(vec));
                let c = Callable::new(original_callable, None);
                let mut matcher = Matcher::new_callable_matcher(&c);
                let t = replace_class_type_vars(i_s.db, t, func_class, &|| Some(as_type()));
                // It feels weird to do this here, but this is just annoying currently
                if !matches!(func_class.generics, Generics::Self_ { .. })
                    && !t
                        .is_super_type_of(i_s, &mut matcher, &as_type_type())
                        .bool()
                {
                    return None;
                }
                if let Type::Type(t) = t.as_ref()
                    && let Type::TypeVar(usage) = t.as_ref()
                    && usage.in_definition == callable.defined_at
                {
                    class_method_type_var_usage = Some(usage.clone());
                    type_vars.remove(0);
                }
                if matcher.has_type_var_matcher() && class_method_type_var_usage.is_none() {
                    callable = callable.replace_type_var_likes_and_self_inplace(
                        i_s.db,
                        &mut |usage| matcher.replace_usage_if_calculated(i_s.db, usage),
                        &|| None,
                    )
                }
            }
        }
        CallableParams::Any(_) => (),
    };

    let type_vars = RefCell::new(type_vars);

    let callable_defined_at = callable.defined_at;
    let ensure_classmethod_type_var_like = |tvl| {
        let pos = type_vars.borrow().iter().position(|t| t == &tvl);
        let position = pos.unwrap_or_else(|| {
            type_vars.borrow_mut().push(tvl.clone());
            type_vars.borrow().len() - 1
        });
        tvl.as_type_var_like_usage(position.into(), callable_defined_at)
            .into_generic_item()
    };
    let get_class_method_class = || {
        if let Some(class) = class_generics_not_defined_yet {
            let type_var_likes = class.use_cached_type_vars(i_s.db);
            Type::new_class(
                class.node_ref.as_link(),
                match type_var_likes.is_empty() {
                    true => ClassGenerics::new_none(),
                    false => ClassGenerics::List(GenericsList::new_generics(
                        type_var_likes
                            .iter()
                            .map(|tvl| ensure_classmethod_type_var_like(tvl.clone()))
                            .collect(),
                    )),
                },
            )
        } else {
            as_type()
        }
    };
    let mut new_callable = callable.replace_type_var_likes_and_self_inplace(
        i_s.db,
        &mut |mut usage| {
            let in_definition = usage.in_definition();
            if let Some(result) = maybe_class_usage(i_s.db, func_class, &usage) {
                // We need to remap again, because in generics of classes will be
                // generic in the function of the classmethod, see for example
                // `testGenericClassMethodUnboundOnClass`.
                if let Some(class) = class_generics_not_defined_yet {
                    return result.maybe_replace_type_var_likes_and_self(
                        i_s.db,
                        &mut |usage| {
                            (usage.in_definition() == class.node_ref.as_link())
                                .then(|| ensure_classmethod_type_var_like(usage.as_type_var_like()))
                        },
                        &|| None,
                    );
                }
                Some(result)
            } else if in_definition == callable_defined_at {
                if let Some(u) = &class_method_type_var_usage {
                    return if u.index == usage.index() {
                        Some(Generic::TypeArg(get_class_method_class()))
                    } else {
                        usage.add_to_index(-1);
                        Some(usage.into_generic_item())
                    };
                }
                None
            } else {
                // This can happen for example if the return value is a Callable with its
                // own type vars.
                None
            }
        },
        &|| Some(get_class_method_class()),
    );
    let type_vars = type_vars.into_inner();
    new_callable.type_vars = TypeVarLikes::from_vec(type_vars);
    // We just skipped the first param, so from now on every param has an annotation, even if it's
    // an implicit Type::Any.
    new_callable
        .kind
        .update_had_first_self_or_class_annotation(true);
    Some(new_callable)
}
