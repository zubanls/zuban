use std::{cell::RefCell, sync::Arc};

use crate::{
    database::OverloadDefinition,
    matching::{Generics, replace_class_type_vars},
    prelude::*,
    type_::{ClassGenerics, GenericsList},
    type_helpers::Callable,
};

pub(super) fn infer_overloaded_class_method(
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

pub(crate) fn infer_class_method<'db: 'class, 'class>(
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

pub(super) fn proper_classmethod_callable(
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
            if let Some(result) = usage.maybe_class_generic(i_s.db, func_class) {
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

pub(super) fn callable_into_inferred(callable: CallableContent) -> Inferred {
    Inferred::from_type(Type::Callable(Arc::new(callable)))
}
