use std::sync::Arc;

use crate::{
    arguments::{CombinedArgs, KnownArgsWithCustomAddIssue},
    file::use_cached_annotation_or_type_comment,
    inferred::{
        InferredState,
        attribute_kind::AttributeKind,
        binding_utils::{
            callable_into_inferred, infer_class_method, infer_overloaded_class_method,
        },
    },
    matching::replace_class_type_vars,
    prelude::*,
    type_::{FunctionKind, FunctionOverload},
    type_helpers::{FirstParamProperties, Function, TypeOrClass},
};

impl<'db: 'slf, 'slf> Inferred {
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
