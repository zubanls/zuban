use std::{iter::repeat_n, sync::Arc};

use super::{
    AnyCause, LookupResult, Namespace, NewType, TupleArgs, Type, TypeVarKind, dataclass_initialize,
    initialize_typed_dict, lookup_dataclass_symbol, lookup_on_dataclass, lookup_on_dataclass_type,
    lookup_on_enum_class, lookup_on_enum_instance, lookup_on_enum_member_instance,
    lookup_on_typed_dict,
    tuple::{lookup_on_tuple, lookup_tuple_magic_methods},
};
use crate::{
    arguments::{Args, NoArgs},
    database::{Database, Specific},
    debug,
    diagnostics::IssueKind,
    file::PythonFile,
    getitem::SliceType,
    imports::{ImportResult, namespace_import},
    inference_state::InferenceState,
    inferred::{AttributeKind, Inferred},
    match_::Match,
    matching::{
        ErrorTypes, GotType, IteratorContent, LookupKind, OnLookupError, OnTypeError,
        calc_callable_type_vars,
    },
    node_ref::NodeRef,
    recoverable_error,
    result_context::ResultContext,
    type_::{
        ClassGenerics, DbBytes, DbString, Intersection, Literal, LiteralKind, LiteralValue,
        NamedTuple, TupleUnpack,
    },
    type_helpers::{
        Callable, Class, ClassLookupOptions, Function, Instance, InstanceLookupOptions,
        LookupDetails, OverloadedFunction,
    },
};

impl Type {
    pub(crate) fn lookup(
        &self,
        i_s: &InferenceState,
        from_file: &PythonFile,
        name: &str,
        lookup_kind: LookupKind,
        result_context: &mut ResultContext,
        add_issue: &dyn Fn(IssueKind) -> bool,
        on_lookup_error: OnLookupError,
    ) -> LookupResult {
        self.lookup_with_first_attr_kind(
            i_s,
            from_file,
            name,
            lookup_kind,
            result_context,
            add_issue,
            on_lookup_error,
        )
        .0
    }

    pub(crate) fn lookup_with_first_attr_kind(
        &self,
        i_s: &InferenceState,
        from_file: &PythonFile,
        name: &str,
        lookup_kind: LookupKind,
        result_context: &mut ResultContext,
        add_issue: &dyn Fn(IssueKind) -> bool,
        on_lookup_error: OnLookupError,
    ) -> (LookupResult, AttributeKind) {
        let mut result: Option<(LookupResult, AttributeKind)> = None;
        self.run_after_lookup_on_each_union_member(
            i_s,
            None,
            from_file,
            name,
            lookup_kind,
            result_context,
            add_issue,
            &mut |t, lookup_result| {
                if matches!(lookup_result.lookup, LookupResult::None) {
                    on_lookup_error(t);
                }
                result = Some(if let Some(l) = result.take() {
                    (
                        LookupResult::UnknownName(
                            l.0.into_inferred()
                                .simplified_union(i_s, lookup_result.lookup.into_inferred()),
                        ),
                        l.1,
                    )
                } else {
                    (lookup_result.lookup, lookup_result.attr_kind)
                })
            },
        );
        result.unwrap_or_else(|| {
            debug_assert!(matches!(self, Type::Never(_)));
            on_lookup_error(self);
            (LookupResult::None, AttributeKind::Attribute)
        })
    }

    pub fn lookup_symbol<'db: 'a, 'a>(
        &'a self,
        i_s: &InferenceState<'db, '_>,
        name: &str,
    ) -> (Option<Class<'a>>, LookupResult) {
        match self {
            Type::Dataclass(d) => lookup_dataclass_symbol(d, i_s, name),
            Type::Tuple(tuple) => (None, lookup_tuple_magic_methods(tuple.clone(), name).lookup),
            Type::NamedTuple(nt) => (
                Some(i_s.db.python_state.typing_named_tuple_class(i_s.db)),
                nt.type_lookup(i_s, name, None).lookup,
            ),
            // This should only happen in case some other weird conditions appear where errors
            // were generated. Simply return that there is no such definition to avoid crashing.
            Type::TypedDict(_) => (None, LookupResult::None),
            _ => unreachable!("{name:?} {self:?}"),
        }
    }

    #[inline]
    pub(crate) fn run_after_lookup_on_each_union_member(
        &self,
        i_s: &InferenceState,
        from_inferred: Option<&Inferred>,
        from_file: &PythonFile,
        name: &str,
        kind: LookupKind,
        result_context: &mut ResultContext,
        add_issue: &dyn Fn(IssueKind) -> bool,
        callable: &mut dyn FnMut(&Type, LookupDetails),
    ) {
        let options = || {
            /* TODO ?
            if avoid_inferring_return_types {
                options = options.with_avoid_inferring_return_types();
            }
            */
            InstanceLookupOptions::new(add_issue).with_kind(kind)
        };
        match self {
            Type::Class(c) => {
                let inst = Instance::new(c.class(i_s.db), from_inferred);
                let l = inst.lookup(i_s, name, options());
                callable(self, l)
            }
            Type::Any(cause) => callable(self, LookupDetails::any(*cause)),
            Type::None => {
                let mut result = i_s
                    .db
                    .python_state
                    .none_instance()
                    .lookup(i_s, name, options());
                if name == "__class__" {
                    // The class of None is Type[None]
                    result
                        .lookup
                        .update_inferred(Inferred::from_type(Type::Type(Arc::new(Type::None))))
                }
                callable(self, result)
            }
            Type::Literal(literal) => {
                let instance = literal.as_instance(i_s.db);
                let l =
                    instance.lookup(i_s, name, options().with_as_self_instance(&|| self.clone()));
                callable(self, l)
            }
            t @ Type::TypeVar(usage) => match usage.type_var.kind(i_s.db) {
                TypeVarKind::Bound(bound) => {
                    if let Type::Class(c) = bound {
                        let inst = Instance::new(c.class(i_s.db), None);
                        let l =
                            inst.lookup(i_s, name, options().with_as_self_instance(&|| t.clone()));
                        callable(self, l)
                    } else {
                        bound.run_after_lookup_on_each_union_member(
                            i_s,
                            None,
                            from_file,
                            name,
                            kind,
                            result_context,
                            add_issue,
                            callable,
                        );
                    }
                }
                TypeVarKind::Constraints(_constraints) => {
                    debug!("TODO type var values");
                    /*
                    for type_ in constraints.iter() {
                    }
                    */
                    // TODO it's kind of stupid that we recreate an instance object here all the time, we
                    // should just use a precreated object() from somewhere.
                    callable(
                        self,
                        Instance::new(i_s.db.python_state.object_class(), None).lookup(
                            i_s,
                            name,
                            options(),
                        ),
                    )
                }
                TypeVarKind::Unrestricted => {
                    let s = &i_s.db.python_state;
                    // TODO it's kind of stupid that we recreate an instance object here all the time, we
                    // should just use a precreated object() from somewhere.
                    callable(
                        self,
                        Instance::new(s.object_class(), None).lookup(i_s, name, options()),
                    )
                }
            },
            Type::Tuple(tup) => callable(self, lookup_on_tuple(tup, i_s, add_issue, name)),
            Type::Union(union) => {
                let ignore_attr_errors = i_s.in_try_that_ignores_attribute_errors();
                let mut need_recheck = ignore_attr_errors;
                for t in union.iter() {
                    if matches!(t, Type::None) && i_s.should_ignore_none_in_untyped_context() {
                        continue;
                    }
                    t.run_after_lookup_on_each_union_member(
                        i_s,
                        None,
                        from_file,
                        name,
                        kind,
                        result_context,
                        add_issue,
                        &mut |t, lookup| {
                            if ignore_attr_errors {
                                if lookup.lookup.is_some() {
                                    need_recheck = false;
                                } else {
                                    return;
                                }
                            }
                            callable(t, lookup)
                        },
                    )
                }
                if need_recheck {
                    // This is needed if callable was never called, because all union entries did
                    // not have an attribute and we're in a try: except AttributeError.
                    for t in union.iter() {
                        if matches!(t, Type::None) && i_s.should_ignore_none_in_untyped_context() {
                            continue;
                        }
                        t.run_after_lookup_on_each_union_member(
                            i_s,
                            None,
                            from_file,
                            name,
                            kind,
                            result_context,
                            add_issue,
                            callable,
                        )
                    }
                }
            }
            Type::Type(t) => attribute_access_of_type(
                i_s,
                &add_issue,
                name,
                kind,
                result_context,
                callable,
                t.clone(),
                None,
            ),
            Type::Callable(_) | Type::FunctionOverload(_) => callable(
                self,
                Instance::new(i_s.db.python_state.function_class(), None).lookup(
                    i_s,
                    name,
                    options(),
                ),
            ),
            Type::Module(file_index) => {
                let lookup = i_s
                    .db
                    .loaded_python_file(*file_index)
                    .lookup(i_s.db, add_issue, name);
                let mut attr_kind = AttributeKind::Attribute;
                if let Some(inf) = lookup.maybe_inferred()
                    && inf.maybe_saved_specific(i_s.db)
                        == Some(Specific::AnnotationOrTypeCommentFinal)
                {
                    attr_kind = AttributeKind::Final
                }
                callable(self, LookupDetails::new(self.clone(), lookup, attr_kind))
            }
            Type::Namespace(namespace) => callable(
                self,
                LookupDetails::new(
                    self.clone(),
                    lookup_in_namespace(i_s.db, from_file, namespace, name),
                    AttributeKind::Attribute,
                ),
            ),
            Type::Self_ => {
                let Some(current_class) = i_s.current_class() else {
                    recoverable_error!(
                        "Self lookup without current_class, you should probably report this"
                    );
                    callable(
                        self,
                        LookupDetails::new(
                            self.clone(),
                            LookupResult::None,
                            AttributeKind::Attribute,
                        ),
                    );
                    return;
                };
                let class_infos = current_class.use_cached_class_infos(i_s.db);
                if let Some(t) = class_infos.undefined_generics_type.get()
                    && matches!(t.as_ref(), Type::Enum(_))
                {
                    t.run_after_lookup_on_each_union_member(
                        i_s,
                        None,
                        from_file,
                        name,
                        kind,
                        result_context,
                        add_issue,
                        callable,
                    );
                    return;
                }
                let inst = Instance::new(
                    Class::with_self_generics(
                        i_s.db,
                        current_class.node_ref.to_db_lifetime(i_s.db),
                    ),
                    from_inferred,
                );
                let l = inst.lookup(i_s, name, options().with_as_self_instance(&|| Type::Self_));
                callable(self, l)
            }
            Type::Super {
                class,
                bound_to,
                mro_index,
            } => {
                let class = class.class(i_s.db);
                let mut l = if matches!(bound_to.as_ref(), Type::Type(_)) {
                    class.lookup(
                        i_s,
                        name,
                        ClassLookupOptions::new(add_issue)
                            .with_super_count(*mro_index)
                            .with_as_type_type(&|| (**bound_to).clone()),
                    )
                } else {
                    let instance = Instance::new(class, None);
                    instance.lookup(
                        i_s,
                        name,
                        InstanceLookupOptions::new(add_issue)
                            .with_kind(LookupKind::OnlyType)
                            .with_super_count(*mro_index)
                            .with_disallow_lazy_bound_method()
                            .with_as_self_instance(&|| (**bound_to).clone()),
                    )
                };
                if matches!(&l.lookup, LookupResult::None) {
                    add_issue(IssueKind::UndefinedInSuperclass { name: name.into() });
                    callable(self, LookupDetails::any(AnyCause::FromError));
                    return;
                }
                // Set is_abstract_from_super
                set_is_abstract_from_super(i_s, &mut l);
                callable(self, l)
            }
            Type::Dataclass(d) => callable(self, lookup_on_dataclass(d, i_s, add_issue, name)),
            Type::TypedDict(td) => callable(
                self,
                lookup_on_typed_dict(td.clone(), i_s, add_issue, name, kind),
            ),
            Type::NamedTuple(nt) => callable(
                self,
                nt.lookup(i_s, add_issue, name, Some(&|| self.clone())),
            ),
            Type::Never(_) => callable(
                self,
                LookupDetails::new(
                    self.clone(),
                    LookupResult::UnknownName(Inferred::from_type(self.clone())),
                    AttributeKind::Attribute,
                ),
            ),
            Type::NewType(new_type) => {
                if let Type::Class(c) = &new_type.type_ {
                    let l = Instance::new(c.class(i_s.db), None).lookup(
                        i_s,
                        name,
                        options().with_as_self_instance(&|| self.clone()),
                    );
                    callable(self, l)
                } else {
                    new_type.type_.run_after_lookup_on_each_union_member(
                        i_s,
                        None,
                        from_file,
                        name,
                        kind,
                        result_context,
                        add_issue,
                        callable,
                    )
                }
            }
            Type::Enum(e) => callable(self, lookup_on_enum_instance(i_s, add_issue, e, name)),
            Type::EnumMember(member) => callable(
                self,
                lookup_on_enum_member_instance(i_s, add_issue, member, name),
            ),
            Type::RecursiveType(r) => r
                .calculated_type(i_s.db)
                .run_after_lookup_on_each_union_member(
                    i_s,
                    None,
                    from_file,
                    name,
                    kind,
                    result_context,
                    add_issue,
                    callable,
                ),
            Type::ParamSpecArgs(_) => i_s
                .db
                .python_state
                .tuple_of_obj
                .run_after_lookup_on_each_union_member(
                    i_s,
                    None,
                    from_file,
                    name,
                    kind,
                    result_context,
                    add_issue,
                    callable,
                ),
            Type::ParamSpecKwargs(_) => i_s
                .db
                .python_state
                .dict_of_str_and_obj
                .run_after_lookup_on_each_union_member(
                    i_s,
                    None,
                    from_file,
                    name,
                    kind,
                    result_context,
                    add_issue,
                    callable,
                ),
            Type::CustomBehavior(_) => {
                Type::Callable(i_s.db.python_state.any_callable_from_error.clone())
                    .run_after_lookup_on_each_union_member(
                        i_s,
                        None,
                        from_file,
                        name,
                        kind,
                        result_context,
                        add_issue,
                        callable,
                    )
            }
            Self::Intersection(i) => {
                // We need to wrap this in a function, because otherwise the Rust compiler recurses
                // while trying to create the impls.
                fn on_intersection(
                    i: &Intersection,
                    i_s: &InferenceState,
                    from_file: &PythonFile,
                    add_issue: &dyn Fn(IssueKind) -> bool,
                    name: &str,
                    kind: LookupKind,
                    result_context: &mut ResultContext,
                    callable: &mut dyn FnMut(&Type, LookupDetails),
                ) {
                    i.run_after_lookup_on_each_union_member(
                        &mut |t, add_issue, on_lookup_result| {
                            t.run_after_lookup_on_each_union_member(
                                i_s,
                                None,
                                from_file,
                                name,
                                kind,
                                result_context,
                                add_issue,
                                &mut |t, lookup| on_lookup_result(t, lookup),
                            );
                        },
                        add_issue,
                        callable,
                    )
                }
                on_intersection(
                    i,
                    i_s,
                    from_file,
                    add_issue,
                    name,
                    kind,
                    result_context,
                    callable,
                );
            }
            Type::DataclassTransformObj(_) => callable(self, LookupDetails::none()),
            Type::LiteralString { .. } => {
                let l = i_s.db.python_state.str_class().instance().lookup(
                    i_s,
                    name,
                    options().with_as_self_instance(&|| self.clone()),
                );
                callable(self, l)
            }
            Type::TypeForm(_) => {
                let inst = i_s.db.python_state.object_class().instance();
                callable(self, inst.lookup(i_s, name, options()))
            }
        }
    }

    pub fn get_item(
        &self,
        i_s: &InferenceState,
        from_inferred: Option<&Inferred>,
        slice_type: &SliceType,
        result_context: &mut ResultContext,
    ) -> Inferred {
        self.get_item_internal(i_s, from_inferred, slice_type, result_context, &|issue| {
            slice_type.as_node_ref().add_issue(i_s, issue)
        })
    }

    pub(super) fn get_item_internal(
        &self,
        i_s: &InferenceState,
        from_inferred: Option<&Inferred>,
        slice_type: &SliceType,
        result_context: &mut ResultContext,
        add_issue: &dyn Fn(IssueKind) -> bool,
    ) -> Inferred {
        let not_possible = |is_class_like| {
            if is_class_like {
                add_issue(IssueKind::OnlyClassTypeApplication);
            } else {
                add_issue(IssueKind::NotIndexable {
                    type_: self.format_short(i_s.db),
                });
            }
            slice_type.infer(i_s);
            Inferred::new_any_from_error()
        };
        match self {
            Type::Class(c) => Instance::new(c.class(i_s.db), from_inferred).get_item(
                i_s,
                slice_type,
                result_context,
                self,
                add_issue,
            ),
            Type::Any(cause) => {
                // Make sure the slices are inferred
                slice_type.infer(i_s);
                Inferred::new_any(*cause)
            }
            Type::Tuple(tup) => tup.get_item(i_s, slice_type, result_context, add_issue),
            Type::NamedTuple(nt) => nt.get_item(i_s, slice_type, result_context, add_issue),
            Type::Union(union) => Inferred::gather_simplified_union(i_s, |callable| {
                for t in union.iter() {
                    if matches!(t, Type::None) && i_s.should_ignore_none_in_untyped_context() {
                        continue;
                    }
                    callable(t.get_item_internal(i_s, None, slice_type, result_context, add_issue))
                }
            }),
            Type::TypeVar(tv) => match tv.type_var.kind(i_s.db) {
                TypeVarKind::Bound(bound) => match bound {
                    Type::Class(c) => Instance::new(c.class(i_s.db), from_inferred).get_item(
                        i_s,
                        slice_type,
                        result_context,
                        self,
                        add_issue,
                    ),
                    _ => bound.get_item_internal(i_s, None, slice_type, result_context, add_issue),
                },
                _ => not_possible(false),
            },
            Type::Type(t) => match t.as_ref() {
                Type::Class(c) => c.class(i_s.db).get_item(i_s, slice_type, result_context),
                Type::Dataclass(d) => slice_type
                    .file
                    .name_resolution_for_types(i_s)
                    .compute_type_application_on_dataclass(d, *slice_type, result_context),
                Type::NamedTuple(nt) => slice_type
                    .file
                    .name_resolution_for_types(i_s)
                    .compute_type_application_on_named_tuple(
                        nt.clone(),
                        *slice_type,
                        result_context,
                    ),
                t @ Type::Enum(_) => {
                    let enum_index = slice_type.infer(i_s);
                    if !enum_index
                        .as_cow_type(i_s)
                        .is_simple_sub_type_of(i_s, &i_s.db.python_state.str_type())
                        .bool()
                    {
                        add_issue(IssueKind::EnumIndexShouldBeAString {
                            actual: enum_index.format_short(i_s),
                        });
                    }
                    Inferred::from_type(t.clone())
                }
                Type::TypedDict(td) => slice_type
                    .file
                    .name_resolution_for_types(i_s)
                    .compute_type_application_on_typed_dict(
                        td.clone(),
                        *slice_type,
                        result_context,
                    ),
                _ => not_possible(true),
            },
            Type::Dataclass(dc) => dc.class(i_s.db).instance().get_item(
                i_s,
                slice_type,
                result_context,
                self,
                add_issue,
            ),
            Type::NewType(new_type) => {
                new_type
                    .type_
                    .get_item_internal(i_s, None, slice_type, result_context, add_issue)
            }
            Type::RecursiveType(r) => r.calculated_type(i_s.db).get_item_internal(
                i_s,
                None,
                slice_type,
                result_context,
                add_issue,
            ),
            Type::TypedDict(d) => d.get_item(i_s, slice_type, add_issue),
            Type::Literal(l) => l.fallback_type(i_s.db).get_item_internal(
                i_s,
                None,
                slice_type,
                result_context,
                add_issue,
            ),
            Type::Self_ => {
                let Some(current_class) = i_s.current_class() else {
                    recoverable_error!(
                        "Self getitem without current_class, you should probably report this"
                    );
                    return Inferred::new_any_from_error();
                };
                current_class
                    .instance()
                    .get_item(i_s, slice_type, result_context, self, add_issue)
            }
            Type::Intersection(i) => i.get_item(i_s, slice_type, result_context, add_issue),
            Type::Callable(_) => not_possible(true),
            Type::ParamSpecArgs(_) => i_s.db.python_state.tuple_of_obj.get_item_internal(
                i_s,
                None,
                slice_type,
                result_context,
                add_issue,
            ),
            Type::ParamSpecKwargs(_) => i_s.db.python_state.dict_of_str_and_obj.get_item_internal(
                i_s,
                None,
                slice_type,
                result_context,
                add_issue,
            ),
            _ => not_possible(false),
        }
    }

    pub fn setitem_context(&self, i_s: &InferenceState, slice_type: &SliceType) -> Inferred {
        self.get_item_internal(
            i_s,
            None,
            slice_type,
            &mut ResultContext::ValueExpected,
            &|_| false,
        )
    }

    pub(crate) fn execute<'db>(
        &self,
        i_s: &InferenceState<'db, '_>,
        inferred_from: Option<&Inferred>,
        args: &dyn Args<'db>,
        result_context: &mut ResultContext,
        on_type_error: OnTypeError,
    ) -> Inferred {
        let not_callable = || {
            let t = self.format_short(i_s.db);
            args.add_issue(
                i_s,
                IssueKind::NotCallable {
                    type_: format!("\"{}\"", t).into(),
                },
            );
            Inferred::new_any_from_error()
        };
        match self {
            Type::Class(c) => {
                let cls = c.class(i_s.db);
                Instance::new(cls, inferred_from).execute(i_s, args, result_context, on_type_error)
            }
            Type::Type(cls) => {
                execute_type_of_type(i_s, args, result_context, on_type_error, cls.as_ref())
            }
            Type::Union(union) => Inferred::gather_simplified_union(i_s, |gather| {
                let result_context = if result_context.expect_not_none()
                    && union.iter().any(|t| match t {
                        // If there's any callable with a return type that is not None we should
                        // not complain with the lint that a None return does not make sense,
                        // because it can be some other type.
                        Type::Callable(c) => c.return_type != Type::None,
                        _ => false,
                    }) {
                    &mut ResultContext::Unknown
                } else {
                    result_context
                };
                for entry in union.iter() {
                    if matches!(entry, Type::None) && i_s.should_ignore_none_in_untyped_context() {
                        continue;
                    }
                    gather(entry.execute(i_s, None, args, result_context, on_type_error))
                }
            }),
            Type::Callable(content) => {
                Callable::new(content, None).execute(i_s, args, on_type_error, result_context)
            }
            Type::Dataclass(d) => {
                d.class(i_s.db)
                    .instance()
                    .execute(i_s, args, result_context, on_type_error)
            }
            Type::Enum(e) => {
                e.class(i_s.db)
                    .instance()
                    .execute(i_s, args, result_context, on_type_error)
            }
            Type::EnumMember(e) => {
                e.enum_
                    .class(i_s.db)
                    .instance()
                    .execute(i_s, args, result_context, on_type_error)
            }
            Type::FunctionOverload(overload) => OverloadedFunction::new(overload, None).execute(
                i_s,
                args,
                result_context,
                on_type_error,
            ),
            Type::TypeVar(tv) => match tv.type_var.kind(i_s.db) {
                TypeVarKind::Bound(bound) => {
                    bound.execute(i_s, None, args, result_context, on_type_error)
                }
                _ => not_callable(),
            },
            Type::Any(cause) => {
                args.calculate_diagnostics_for_any_callable();
                Inferred::new_any(*cause)
            }
            Type::Never(_) => {
                args.calculate_diagnostics_for_any_callable();
                Inferred::new_any(AnyCause::Todo)
            }
            Type::CustomBehavior(custom) => {
                custom.execute(i_s, args, result_context, on_type_error)
            }
            Type::Intersection(intersection) => {
                intersection.execute(i_s, args, result_context, on_type_error)
            }
            Type::DataclassTransformObj(d) => {
                Inferred::from_type(Type::DataclassTransformObj(d.clone()))
            }
            _ => not_callable(),
        }
    }

    pub(crate) fn iter(&self, i_s: &InferenceState, infos: IterInfos) -> IteratorContent {
        match self {
            Type::Class(c) => Instance::new(c.class(i_s.db), None).iter(i_s, self, infos),
            Type::Tuple(tuple) => tuple.iter(),
            Type::NamedTuple(nt) => nt.iter(),
            Type::Union(union) => {
                let mut items = vec![];
                let with_union_infos = infos.with_in_union(self);
                for t in union.iter() {
                    if matches!(t, Type::None) && i_s.should_ignore_none_in_untyped_context() {
                        continue;
                    }
                    items.push(t.iter(i_s, with_union_infos));
                }
                IteratorContent::Union(items)
            }
            Type::TypeVar(tv) => match tv.type_var.kind(i_s.db) {
                TypeVarKind::Bound(bound) => bound.iter(i_s, infos),
                _ => {
                    infos.add_not_iterable_issue(i_s.db, self);
                    IteratorContent::Any(AnyCause::FromError)
                }
            },
            Type::NewType(n) => n.type_.iter(i_s, infos),
            Type::Self_ => {
                if let Some(current_type) = i_s.current_type() {
                    current_type.iter(i_s, infos)
                } else {
                    recoverable_error!("Had no context self for iter call");
                    IteratorContent::Any(AnyCause::Internal)
                }
            }
            Type::RecursiveType(rec) => rec.calculated_type(i_s.db).iter(i_s, infos),
            Type::Intersection(i) => i.iter(i_s, infos),
            _ => IteratorContent::Inferred(
                self.lookup(
                    i_s,
                    infos.file(),
                    "__iter__",
                    LookupKind::OnlyType,
                    &mut ResultContext::ValueExpected,
                    infos.add_issue,
                    &|t| infos.add_not_iterable_issue(i_s.db, t),
                )
                .into_inferred()
                .execute(i_s, &infos.as_no_args())
                .type_lookup_and_execute_with_attribute_error(
                    i_s,
                    infos.from,
                    "__next__",
                    &infos.as_no_args(),
                    &mut ResultContext::ValueExpected,
                ),
            ),
        }
    }

    pub fn try_operation_against_literal(
        &self,
        db: &Database,
        operand: &str,
        right: &Literal,
        add_issue: &dyn Fn(IssueKind) -> bool,
    ) -> Option<Type> {
        match self {
            Type::Literal(left) => {
                left.value(db)
                    .operation(db, operand, right.value(db), add_issue)
            }
            Type::LiteralString { .. }
                if operand == "+" && matches!(right.kind, LiteralKind::String(_)) =>
            {
                Some(Type::LiteralString { implicit: true })
            }
            _ => None,
        }
    }

    pub fn is_literal_string_only_argument_for_string_percent_formatting(&self) -> bool {
        fn check(t: &Type, allow_tuples: bool) -> bool {
            let check_tup_items = |items: &Arc<[Type]>| items.iter().all(|t| check(t, false));
            match t {
                Type::Tuple(tup) if allow_tuples => match &tup.args {
                    TupleArgs::WithUnpack(w) => match &w.unpack {
                        TupleUnpack::TypeVarTuple(_) => false,
                        TupleUnpack::ArbitraryLen(t) => {
                            check(t, false)
                                && check_tup_items(&w.before)
                                && check_tup_items(&w.after)
                        }
                    },
                    TupleArgs::FixedLen(items) => check_tup_items(items),
                    TupleArgs::ArbitraryLen(t) => check(t, false),
                },
                Type::Union(u) => u.iter().all(|t| check(t, allow_tuples)),
                Type::Intersection(i) => i.iter_entries().any(|t| check(t, allow_tuples)),
                _ => t.is_allowed_as_literal_string(true),
            }
        }
        check(self, true)
    }

    pub fn try_operation_against_literal_string(&self, operand: &str) -> Option<Type> {
        match self {
            Type::LiteralString { .. } if operand == "+" => {
                Some(Type::LiteralString { implicit: true })
            }
            Type::Literal(left)
                if operand == "+" && matches!(left.kind, LiteralKind::String(_)) =>
            {
                Some(Type::LiteralString { implicit: true })
            }
            _ => None,
        }
    }
}

impl LiteralValue<'_> {
    pub fn operation(
        self,
        db: &Database,
        operand: &str,
        right: Self,
        add_issue: &dyn Fn(IssueKind) -> bool,
    ) -> Option<Type> {
        const MAX_STR_BYTES_SIZE_FOR_MULTIPLICATION: usize = 1024 * 16;
        match (self, right) {
            (LiteralValue::Int(l), LiteralValue::Int(r)) => {
                if let Ok(l) = l.try_into()
                    && let Ok(r) = r.try_into()
                {
                    return int_operations(db, l, operand, r, add_issue);
                }
                None
            }
            (LiteralValue::String(l), LiteralValue::String(r)) => (operand == "+").then(|| {
                Type::Literal(Literal::new_implicit(LiteralKind::String(
                    DbString::ArcStr(format!("{l}{r}").into()),
                )))
            }),
            (LiteralValue::Bytes(l), LiteralValue::Bytes(r)) => (operand == "+").then(|| {
                Type::Literal(Literal::new_implicit(LiteralKind::Bytes(DbBytes::Arc(
                    l.iter().chain(r.iter()).copied().collect(),
                ))))
            }),
            (LiteralValue::String(s), LiteralValue::Int(n))
            | (LiteralValue::Int(n), LiteralValue::String(s)) => (operand == "*").then(|| {
                let n = n.try_into().unwrap_or(0);
                if s.len() * n > MAX_STR_BYTES_SIZE_FOR_MULTIPLICATION {
                    Type::LiteralString { implicit: true }
                } else {
                    Type::Literal(Literal::new_implicit(LiteralKind::String(
                        if s.is_empty() {
                            // repeat_n is really slow on an empty string.
                            DbString::Static("")
                        } else {
                            DbString::ArcStr(repeat_n(s, n).collect::<String>().into())
                        },
                    )))
                }
            }),
            (LiteralValue::Bytes(b), LiteralValue::Int(n))
            | (LiteralValue::Int(n), LiteralValue::Bytes(b)) => (operand == "*").then(|| {
                let n = n.try_into().unwrap_or(0);
                if b.len() * n > MAX_STR_BYTES_SIZE_FOR_MULTIPLICATION {
                    db.python_state.bytes_type()
                } else {
                    Type::Literal(Literal::new_implicit(LiteralKind::Bytes(DbBytes::Arc(
                        repeat_n(b.as_ref(), n).flatten().copied().collect(),
                    ))))
                }
            }),
            (LiteralValue::Bool(l), LiteralValue::Bool(r)) => {
                bool_operations(db, l, operand, r, add_issue)
            }
            (left, LiteralValue::Bool(b)) => {
                left.operation(db, operand, LiteralValue::Int(&b.into()), add_issue)
            }
            (LiteralValue::Bool(b), right) => {
                LiteralValue::Int(&b.into()).operation(db, operand, right, add_issue)
            }

            (LiteralValue::Bytes(_), LiteralValue::String(_))
            | (LiteralValue::String(_), LiteralValue::Bytes(_)) => None,
        }
    }
}

fn int_operations(
    db: &Database,
    left: i64,
    operand: &str,
    right: i64,
    add_issue: &dyn Fn(IssueKind) -> bool,
) -> Option<Type> {
    let result = match operand {
        "+" => left.checked_add(right),
        "-" => left.checked_sub(right),
        "*" => left.checked_mul(right),
        "/" => {
            return Some(if right == 0 {
                add_issue(IssueKind::DivisionByZero);
                Type::ERROR
            } else {
                db.python_state.float_type()
            });
        }
        "//" => {
            if right == 0 {
                add_issue(IssueKind::DivisionByZero);
                return Some(Type::ERROR);
            } else {
                py_div_floor(left, right)
            }
        }
        "%" => {
            if right == 0 {
                add_issue(IssueKind::DivisionByZero);
                return Some(Type::ERROR);
            } else {
                py_mod(left, right)
            }
        }
        "**" => match right.try_into() {
            Ok(right) => left.checked_pow(right),
            Err(_) => {
                return Some(if right >= 0 {
                    db.python_state.int_type()
                } else {
                    db.python_state.float_type()
                });
            }
        },
        ">>" => match right.try_into() {
            Ok(right) => left.checked_shr(right),
            Err(_) => {
                if right >= 0 {
                    None
                } else {
                    add_issue(IssueKind::NegativeShiftCount);
                    return Some(Type::ERROR);
                }
            }
        },
        "<<" => {
            let r: Result<u32, _> = right.try_into();
            match r {
                Ok(right) => {
                    if right > 63 {
                        return None;
                    }
                    ((left as i128) << right).try_into().ok()
                }
                Err(_) => {
                    if right >= 0 {
                        None
                    } else {
                        add_issue(IssueKind::NegativeShiftCount);
                        return Some(Type::ERROR);
                    }
                }
            }
        }
        "|" => Some(left | right),
        "&" => Some(left & right),
        "^" => Some(left ^ right),
        _ => {
            debug_assert!(matches!(operand, ">" | ">=" | "<" | "<="), "{operand}");
            return None;
        }
    };
    if let Some(result) = result {
        Some(Type::Literal(Literal::new_implicit(LiteralKind::Int(
            result.into(),
        ))))
    } else {
        // In case of overflows simply return int, we are probably using numbers bigger than i64
        Some(db.python_state.int_type())
    }
}

fn py_div_floor(a: i64, b: i64) -> Option<i64> {
    let q = a.checked_div(b)?;
    let r = a % b;
    Some(if (r != 0) && ((r > 0) != (b > 0)) {
        q - 1
    } else {
        q
    })
}

fn py_mod(a: i64, b: i64) -> Option<i64> {
    let r = a.checked_rem(b)?;
    Some(if (r != 0) && ((r > 0) != (b > 0)) {
        r + b
    } else {
        r
    })
}

fn bool_operations(
    db: &Database,
    left: bool,
    operand: &str,
    right: bool,
    add_issue: &dyn Fn(IssueKind) -> bool,
) -> Option<Type> {
    let result = match operand {
        "|" => left | right,
        "&" => left & right,
        "^" => left ^ right,
        _ => return int_operations(db, left.into(), operand, right.into(), add_issue),
    };
    Some(Type::Literal(Literal::new_implicit(LiteralKind::Bool(
        result,
    ))))
}

#[derive(Copy, Clone)]
pub(crate) enum IterCause {
    Iter,             // for i in *x
    AssignmentUnpack, // a, b = *x
    VariadicUnpack,   // [*x] or foo(*x)
}

#[derive(Copy, Clone)]
pub(crate) struct IterInfos<'x> {
    from: NodeRef<'x>,
    cause: IterCause,
    in_union: Option<&'x Type>,
    pub add_issue: &'x dyn Fn(IssueKind) -> bool,
}

impl<'x> IterInfos<'x> {
    pub(crate) fn new(
        from: NodeRef<'x>,
        cause: IterCause,
        add_issue: &'x dyn Fn(IssueKind) -> bool,
    ) -> IterInfos<'x> {
        Self {
            from,
            add_issue,
            cause,
            in_union: None,
        }
    }

    pub fn add_not_iterable_issue(&self, db: &Database, t: &Type) {
        let type_ = t.format_short(db);
        self.add_issue(match self.cause {
            IterCause::AssignmentUnpack => IssueKind::UnpackNotIterable {
                type_: format!("\"{type_}\"").into(),
            },
            IterCause::Iter => {
                if let Some(in_union) = self.in_union {
                    IssueKind::NotIterableMissingIterInUnion {
                        object: type_,
                        union: in_union.format_short(db),
                    }
                } else {
                    IssueKind::NotIterableMissingIter { type_ }
                }
            }
            IterCause::VariadicUnpack => IssueKind::IterableExpectedAsVariadicArgs,
        });
    }

    pub(crate) fn with_different_add_issue<'y: 'x>(
        &'y self,
        add_issue: &'y dyn Fn(IssueKind) -> bool,
    ) -> IterInfos<'y> {
        Self { add_issue, ..*self }
    }

    pub(crate) fn with_in_union<'y: 'x>(&'y self, in_union: &'y Type) -> IterInfos<'y> {
        Self {
            in_union: Some(in_union),
            ..*self
        }
    }

    pub fn file(&self) -> &'x PythonFile {
        self.from.file
    }

    pub fn as_no_args(&self) -> NoArgs<'x> {
        NoArgs::new_with_custom_add_issue(self.from, self.add_issue)
    }

    pub fn add_issue(&self, issue: IssueKind) -> bool {
        (self.add_issue)(issue)
    }
}

fn attribute_access_of_type(
    i_s: &InferenceState,
    add_issue: &dyn Fn(IssueKind) -> bool,
    name: &str,
    kind: LookupKind,
    result_context: &mut ResultContext,
    callable: &mut dyn FnMut(&Type, LookupDetails),
    in_type: Arc<Type>,
    mapped_type: Option<&Arc<Type>>,
) {
    let mapped = || mapped_type.unwrap_or(&in_type);
    let details = match in_type.as_ref() {
        Type::Union(union) => {
            debug_assert!(union.entries.len() > 1);
            for t in union.iter() {
                attribute_access_of_type(
                    i_s,
                    &add_issue,
                    name,
                    kind,
                    result_context,
                    callable,
                    Arc::new(t.clone()),
                    None,
                )
            }
            return;
        }
        Type::TypeVar(t) => match t.type_var.kind(i_s.db) {
            TypeVarKind::Bound(bound) => match bound {
                Type::Class(c) => c.class(i_s.db).lookup(
                    i_s,
                    name,
                    ClassLookupOptions::new(&add_issue)
                        .with_kind(kind)
                        .with_as_type_type(&|| Type::Type(mapped().clone())),
                ),
                Type::Dataclass(d) => {
                    lookup_on_dataclass_type(mapped(), d, i_s, add_issue, name, kind)
                }
                t => {
                    return attribute_access_of_type(
                        i_s,
                        add_issue,
                        name,
                        kind,
                        result_context,
                        callable,
                        Arc::new(t.clone()),
                        Some(mapped()),
                    );
                }
            },
            _ => LookupDetails::none(),
        },
        Type::Class(g) => g
            .class(i_s.db)
            .lookup(
                i_s,
                name,
                ClassLookupOptions::new(&add_issue).with_kind(kind),
            )
            .or_else(|| {
                if matches!(g.generics, ClassGenerics::List(_)) {
                    return i_s.db.python_state.generic_alias_class().lookup(
                        i_s,
                        name,
                        ClassLookupOptions::new(&add_issue).with_kind(kind),
                    );
                }
                LookupDetails::none()
            }),
        Type::Literal(l) => l.as_instance(i_s.db).class.lookup(
            i_s,
            name,
            ClassLookupOptions::new(&add_issue).with_kind(kind),
        ),
        Type::Callable(_) => LookupDetails::none(),
        Type::Self_ => {
            let Some(current_class) = i_s.current_class() else {
                recoverable_error!(
                    "Type[Self] lookup without current_class, you should probably report this"
                );
                callable(
                    mapped(),
                    LookupDetails::new(Type::Self_, LookupResult::None, AttributeKind::Attribute),
                );
                return;
            };
            let class_infos = current_class.use_cached_class_infos(i_s.db);
            if let Some(t) = class_infos.undefined_generics_type.get()
                && let Type::Enum(e) = t.as_ref()
            {
                lookup_on_enum_class(i_s, add_issue, mapped(), e, name, kind)
            } else {
                current_class.lookup(
                    i_s,
                    name,
                    ClassLookupOptions::new(&add_issue)
                        .with_kind(kind)
                        .with_as_type_type(&|| Type::Type(mapped().clone())),
                )
            }
        }
        Type::Any(cause) => i_s
            .db
            .python_state
            .bare_type_class()
            .instance()
            .lookup_with_details(i_s, add_issue, name, kind)
            .or_else(|| LookupDetails::any(*cause)),
        Type::Enum(e) => lookup_on_enum_class(i_s, add_issue, mapped(), e, name, kind),
        Type::Dataclass(d) => lookup_on_dataclass_type(mapped(), d, i_s, add_issue, name, kind),
        Type::TypedDict(_) => i_s.db.python_state.typed_dict_class().lookup(
            i_s,
            name,
            ClassLookupOptions::new(&add_issue).with_kind(kind),
        ),
        Type::NamedTuple(nt) => nt.type_lookup(i_s, name, Some(&|| (**mapped()).clone())),
        Type::Tuple(tup) => tup.class(i_s.db).lookup(
            i_s,
            name,
            ClassLookupOptions::new(&add_issue).with_kind(kind),
        ),
        Type::Type(_) | Type::None => i_s.db.python_state.bare_type_class().lookup(
            i_s,
            name,
            ClassLookupOptions::new(&add_issue).with_kind(kind),
        ),
        Type::Intersection(i) => {
            // We need to wrap this in a function, because otherwise the Rust compiler recurses
            // while trying to create the impls.
            fn on_intersection(
                i: &Intersection,
                i_s: &InferenceState,
                add_issue: &dyn Fn(IssueKind) -> bool,
                name: &str,
                kind: LookupKind,
                result_context: &mut ResultContext,
                callable: &mut dyn FnMut(&Type, LookupDetails),
            ) {
                i.run_after_lookup_on_each_union_member(
                    &mut |t, add_issue, on_lookup_result| {
                        attribute_access_of_type(
                            i_s,
                            add_issue,
                            name,
                            kind,
                            result_context,
                            &mut |t, details| on_lookup_result(t, details),
                            Arc::new(t.clone()),
                            None,
                        );
                    },
                    add_issue,
                    callable,
                );
            }
            on_intersection(i, i_s, add_issue, name, kind, result_context, callable);
            return;
        }
        Type::RecursiveType(r) => {
            attribute_access_of_type(
                i_s,
                add_issue,
                name,
                kind,
                result_context,
                callable,
                Arc::new(r.calculated_type(i_s.db).clone()),
                Some(mapped()),
            );
            return;
        }
        _ => {
            recoverable_error!(
                "We did not handle the attribute {name} on \"{}\", that should be handled",
                in_type.format_short(i_s.db),
            );
            LookupDetails::any(AnyCause::FromError)
        }
    };
    callable(&Type::Type(mapped().clone()), details)
}

pub(crate) fn execute_type_of_type<'db>(
    i_s: &InferenceState<'db, '_>,
    args: &dyn Args<'db>,
    result_context: &mut ResultContext,
    on_type_error: OnTypeError,
    type_: &Type,
) -> Inferred {
    match type_ {
        #![allow(unreachable_code)]
        // TODO remove this
        tuple @ Type::Tuple(_tuple_content) => {
            debug!("TODO this does not check the arguments");
            Inferred::from_type(tuple.clone())
            /*
            // TODO reenable this
            let mut args_iterator = args.iter();
            let (arg, inferred_tup) = if let Some(arg) = args_iterator.next() {
                let inf = arg.infer(i_s, &mut ResultContext::Known(tuple));
                (arg, inf)
            } else {
                debug!("TODO this does not check the arguments");
                return Inferred::from_type(tuple.clone());
            };
            if args_iterator.next().is_some() {
                TODO
            }
            let other = inferred_tup.as_cow_type(i_s);
            if let Match::False { ref reason, .. } = tuple.is_simple_super_type_of(i_s, &other) {
                let error_types = ErrorTypes {
                    matcher: &Matcher::default(),
                    reason,
                    got: GotType::Type(tuple),
                    expected: &other,
                };
                (on_type_error.callback)(i_s, &|_| TODO, &arg, error_types);
            }
            Inferred::from_type(tuple.clone())
            */
        }
        Type::Class(c) => c
            .class(i_s.db)
            .execute(i_s, args, result_context, on_type_error, true),
        Type::TypeVar(t) => {
            match t.type_var.kind(i_s.db) {
                TypeVarKind::Bound(bound) => {
                    execute_type_of_type(i_s, args, result_context, on_type_error, bound);
                }
                TypeVarKind::Unrestricted => {
                    execute_type_of_type(
                        i_s,
                        args,
                        result_context,
                        on_type_error,
                        &i_s.db.python_state.object_type(),
                    );
                }
                _ => (), // This should probably never happen
            };
            Inferred::from_type(type_.clone())
        }
        Type::NewType(n) => {
            n.check_initialization_args(i_s, args, on_type_error);
            Inferred::from_type(Type::NewType(n.clone()))
        }
        Type::Self_ => {
            if let Some(cls) = i_s.current_class() {
                // Type check initialization
                if let Some(dataclass) = cls.maybe_dataclass(i_s.db) {
                    dataclass_initialize(&dataclass, i_s, args, result_context, on_type_error);
                } else if let Some(e) = cls.maybe_enum(i_s.db) {
                    execute_type_of_type(i_s, args, result_context, on_type_error, &Type::Enum(e));
                } else {
                    cls.execute(i_s, args, result_context, on_type_error, true);
                }
                Inferred::from_type(Type::Self_)
            } else {
                recoverable_error!("Had no context class in type[Self]");
                Inferred::new_any_from_error()
            }
        }
        Type::Any(cause) => Inferred::new_any(*cause),
        Type::Dataclass(d) => dataclass_initialize(d, i_s, args, result_context, on_type_error),
        Type::TypedDict(td) => initialize_typed_dict(td.clone(), i_s, args),
        Type::NamedTuple(nt) => {
            let calculated_type_vars = calc_callable_type_vars(
                i_s,
                Callable::new(&nt.__new__, None),
                args.iter(i_s.mode),
                |issue| args.add_issue(i_s, issue),
                true,
                &mut ResultContext::ValueExpected,
                None,
                Some(on_type_error),
            );
            Inferred::from_type(Type::NamedTuple(if nt.__new__.type_vars.is_empty() {
                nt.clone()
            } else {
                let inf = calculated_type_vars.into_return_type(
                    i_s,
                    &Type::Callable(nt.__new__.clone()),
                    None,
                    &|| None,
                );
                let Type::Callable(__new__) = inf.as_type(i_s) else {
                    unreachable!()
                };
                let mut __new__ = Arc::unwrap_or_clone(__new__);
                __new__.type_vars = i_s.db.python_state.empty_type_var_likes.clone();
                Arc::new(NamedTuple::new(nt.name, __new__))
            }))
        }
        Type::Enum(_enum_) => {
            debug!("TODO did not check arguments in execution of enum");
            Inferred::from_type(type_.clone())
        }
        Type::Union(union) => Inferred::gather_simplified_union(i_s, |gather| {
            for t in union.iter() {
                gather(execute_type_of_type(
                    i_s,
                    args,
                    result_context,
                    on_type_error,
                    t,
                ))
            }
        }),
        Type::Intersection(i) => {
            // TODO this is not correct, see also intersection_execution_should_not_fail, but it's
            // at least something.
            let init_t = i.iter_entries().next().unwrap();
            execute_type_of_type(i_s, args, result_context, on_type_error, init_t)
        }
        _ => {
            recoverable_error!(
                "We did not handle a type execution for \"{}\", that should be handled",
                type_.format_short(i_s.db),
            );
            Inferred::new_any_from_error()
        }
    }
}

fn set_is_abstract_from_super(i_s: &InferenceState, l: &mut LookupDetails) {
    if let Some(inf) = l.lookup.maybe_inferred()
        && let Type::Callable(c) = inf.as_cow_type(i_s).as_ref()
        && (c.is_abstract || l.class.is_protocol(i_s.db))
        && {
            let from = NodeRef::from_link(i_s.db, c.defined_at);
            !from.file.is_stub()
                && from.maybe_function().is_some_and(|_| {
                    let func = Function::new_with_unknown_parent(i_s.db, from);
                    func.has_trivial_body(&i_s.with_func_context(&func))
                })
        }
    {
        let mut new_callable = c.as_ref().clone();
        new_callable.is_abstract_from_super = true;
        l.lookup
            .update_inferred(Inferred::from_type(Type::Callable(Arc::new(new_callable))))
    }
}

impl NewType {
    fn check_initialization_args<'db>(
        &self,
        i_s: &InferenceState<'db, '_>,
        args: &dyn Args<'db>,
        on_type_error: OnTypeError,
    ) {
        let t = &self.type_;
        let Some(inf) = args.maybe_single_positional_arg(i_s, &mut ResultContext::new_known(t))
        else {
            args.add_issue(
                i_s,
                match args.iter(i_s.mode).count() {
                    0 => {
                        IssueKind::TooFewArguments(format!(" for \"{}\"", self.name(i_s.db)).into())
                    }
                    1 => IssueKind::NewTypesExpectSinglePositionalArgument,
                    _ => IssueKind::TooManyArguments(
                        format!(" for \"{}\"", self.name(i_s.db)).into(),
                    ),
                },
            );
            return;
        };
        let other = inf.as_cow_type(i_s);
        if let Match::False { ref reason, .. } = t.is_simple_super_type_of(i_s, &other) {
            (on_type_error.callback)(
                i_s,
                &|_| Some(format!(" to \"{}\"", self.name(i_s.db)).into()),
                &args.iter(i_s.mode).next().unwrap(),
                ErrorTypes {
                    matcher: None,
                    reason,
                    got: GotType::Type(&other),
                    expected: t,
                },
            );
        }
    }
}

fn lookup_in_namespace(
    db: &Database,
    from_file: &PythonFile,
    namespace: &Namespace,
    name: &str,
) -> LookupResult {
    let Some(import) = namespace_import(db, from_file, namespace, name) else {
        return LookupResult::None;
    };
    match import.into_import_result() {
        ImportResult::File(file_index) => LookupResult::FileReference(file_index),
        ImportResult::Namespace(namespace) => {
            LookupResult::UnknownName(Inferred::from_type(Type::Namespace(namespace)))
        }
        ImportResult::PyTypedMissing => LookupResult::any(AnyCause::FromError),
    }
}
