use std::{borrow::Cow, sync::Arc};

use parsa_python_cst::ParamKind;

use crate::{
    file::use_cached_annotation_or_type_comment,
    inferred::{
        BoundMethodState, InferredState,
        attribute_kind::AttributeKind,
        binding_utils::{callable_into_inferred, proper_classmethod_callable},
    },
    prelude::*,
    type_::{FunctionKind, FunctionOverload, PropertySetter, PropertySetterType},
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
                                t.replace_class_type_vars(i_s.db, &attribute_class, &|| {
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
                                    let results: Vec<_> =
                                        o.iter_functions()
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
                                            .map(|mut callable| {
                                                callable.receiver_bound = true;
                                                Arc::new(callable)
                                            })
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
                        if !c.receiver_bound
                            && (!i_s.db.mypy_compatible()
                            // ParamSpecs are bound and can only be used from self
                            && c.params.maybe_param_spec().is_none()
                            && attribute_class.maybe_dataclass(i_s.db).is_none()
                                || !matches!(
                                    apply_descriptors_kind,
                                    ApplyDescriptorsKind::NoBoundMethod
                                )) =>
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
                                && let Some(func) = new_c.maybe_original_func_def(i_s.db)
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
                                        let t = t.replace_class_type_vars(
                                            i_s.db,
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
                                && let Some(func) = c.maybe_original_func_def(i_s.db)
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
                            && let Some(func) = c.maybe_original_func_def(i_s.db)
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
            Type::FunctionOverload(overload) => {
                let first = overload.iter_functions().next().unwrap();
                if matches!(first.kind, FunctionKind::Function { .. })
                    && (!i_s.db.mypy_compatible()
                        && first.params.maybe_param_spec().is_none()
                        && attribute_class.maybe_dataclass(i_s.db).is_none()
                        || !matches!(apply_descriptors_kind, ApplyDescriptorsKind::NoBoundMethod))
                {
                    let bound: Vec<_> = overload
                        .iter_functions()
                        .filter_map(|callable| {
                            if callable.receiver_bound {
                                return Some(callable.clone());
                            }
                            let first_type = callable.first_positional_type()?;
                            let mut bound = create_signature_without_self_for_callable(
                                i_s,
                                for_name,
                                callable,
                                &instance,
                                &attribute_class,
                                &first_type,
                            )?;
                            bound.receiver_bound = true;
                            if avoid_inferring_return_types
                                && let Some(func) = bound.maybe_original_func_def(i_s.db)
                                && func.return_annotation().is_none()
                            {
                                bound.return_type = Type::Any(AnyCause::Unannotated);
                            }
                            Some(Arc::new(bound))
                        })
                        .collect();
                    let inferred = match bound.len() {
                        0 => {
                            add_invalid_self_arg(first);
                            Inferred::new_any_from_error()
                        }
                        1 => Inferred::from_type(Type::Callable(bound.into_iter().next().unwrap())),
                        _ => Inferred::from_type(Type::FunctionOverload(FunctionOverload::new(
                            bound.into_iter().collect(),
                        ))),
                    };
                    return Some(Some((
                        inferred,
                        AttributeKind::DefMethod {
                            is_final: first.is_final,
                        },
                    )));
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
            new = Some(
                t.replace_class_type_vars(i_s.db, &attribute_class, &|| Some(instance.clone())),
            );
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

pub(crate) fn infer_class_method_on_instance<'db: 'class, 'class>(
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

fn create_signature_without_self_for_callable(
    i_s: &InferenceState,
    for_name: &str,
    callable: &CallableContent,
    instance: &Type,
    func_class: &Class,
    first_type: &Type,
) -> Option<CallableContent> {
    let c = Callable::new(callable, None);
    let mut matcher = Matcher::new_callable_matcher(&c);
    if !match_self_type(i_s, &mut matcher, instance, func_class, first_type) {
        if for_name == "__new__" {
            // For some things like @override checking of __new__, the self type of the signature
            // is actually a classmethod and therefore special.
            return infer_class_method_on_instance(i_s, instance, *func_class, callable);
        }
        debug!(
            "Couldn't create signature without self for callable {} with instance {}",
            callable.format(&FormatData::new_short(i_s.db)),
            instance.format_short(i_s.db)
        );
        return None;
    }
    let c = callable
        .remove_first_positional_param()
        .expect("Signatures without any params should have been filtered before");
    let c = c
        .replace_class_type_vars(i_s.db, Some(func_class), &|| Some(instance.clone()))
        .unwrap_or(c);
    Some(matcher.remove_self_from_callable(i_s, c))
}

pub fn match_self_type(
    i_s: &InferenceState,
    matcher: &mut Matcher,
    instance: &Type,
    func_class: &Class,
    first_type: &Type,
) -> bool {
    let expected =
        first_type.replace_class_type_vars(i_s.db, func_class, &|| Some(instance.clone()));
    expected.is_super_type_of(i_s, matcher, instance).bool()
}

pub fn calculate_property_return(
    i_s: &InferenceState,
    instance: &Type,
    func_class: &Class,
    callable: &CallableContent,
    avoid_inferring_return_types: bool,
) -> Option<Type> {
    let first_type = callable.first_positional_type()?;
    let c = Callable::new(callable, None); // TODO is this correct?
    let mut matcher = Matcher::new_callable_matcher(&c);
    if callable.kind.had_first_self_or_class_annotation()
        && !match_self_type(i_s, &mut matcher, instance, func_class, &first_type)
    {
        return None;
    }

    if avoid_inferring_return_types
        && let Some(func) = callable.maybe_original_func_def(i_s.db)
        && func.return_annotation().is_none()
    {
        return Some(Type::Any(AnyCause::Unannotated));
    }
    let t = callable
        .return_type
        .replace_class_type_vars(i_s.db, func_class, &|| Some(instance.clone()));

    Some(if callable.type_vars.is_empty() {
        t.into_owned()
    } else {
        matcher
            .replace_type_var_likes_for_unknown_type_vars(i_s.db, t.as_ref())
            .into_owned()
    })
}
