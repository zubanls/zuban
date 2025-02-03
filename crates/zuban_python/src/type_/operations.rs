use std::rc::Rc;

use vfs::FileIndex;

use super::{
    dataclass_initialize, initialize_typed_dict, lookup_dataclass_symbol, lookup_on_dataclass,
    lookup_on_dataclass_type, lookup_on_enum_class, lookup_on_enum_instance,
    lookup_on_enum_member_instance, lookup_on_typed_dict,
    tuple::{lookup_on_tuple, lookup_tuple_magic_methods},
    AnyCause, DataclassTransformObj, LookupResult, Type, TypeVarKind,
};
use crate::{
    arguments::{Args, NoArgs},
    database::{Database, Specific},
    debug,
    diagnostics::IssueKind,
    file::PythonFile,
    getitem::SliceType,
    inference_state::InferenceState,
    inferred::{AttributeKind, Inferred},
    matching::{
        calculate_callable_type_vars_and_return, IteratorContent, LookupKind, OnLookupError,
        OnTypeError, ResultContext,
    },
    node_ref::NodeRef,
    type_::{Intersection, NamedTuple},
    type_helpers::{
        lookup_in_namespace, Callable, Class, ClassLookupOptions, Instance, InstanceLookupOptions,
        LookupDetails, Module, OverloadedFunction,
    },
};

impl Type {
    pub(crate) fn lookup(
        &self,
        i_s: &InferenceState,
        from_file: FileIndex,
        name: &str,
        lookup_kind: LookupKind,
        result_context: &mut ResultContext,
        add_issue: &dyn Fn(IssueKind),
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
        from_file: FileIndex,
        name: &str,
        lookup_kind: LookupKind,
        result_context: &mut ResultContext,
        add_issue: &dyn Fn(IssueKind),
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
            _ => unreachable!("{name:?} {self:?}"),
        }
    }

    #[inline]
    pub(crate) fn run_after_lookup_on_each_union_member(
        &self,
        i_s: &InferenceState,
        from_inferred: Option<&Inferred>,
        from_file: FileIndex,
        name: &str,
        kind: LookupKind,
        result_context: &mut ResultContext,
        add_issue: &dyn Fn(IssueKind),
        callable: &mut impl FnMut(&Type, LookupDetails),
    ) {
        match self {
            Type::Class(c) => {
                let inst = Instance::new(c.class(i_s.db), from_inferred);
                let l = inst.lookup_with_details(i_s, add_issue, name, kind);
                callable(self, l)
            }
            Type::Any(cause) => callable(self, LookupDetails::any(*cause)),
            Type::None => callable(
                self,
                i_s.db
                    .python_state
                    .none_instance()
                    .lookup_with_details(i_s, add_issue, name, kind),
            ),
            Type::Literal(literal) => {
                let instance = literal.as_instance(i_s.db);
                let l = instance.lookup_with_details(i_s, add_issue, name, kind);
                callable(self, l)
            }
            t @ Type::TypeVar(usage) => match &usage.type_var.kind {
                TypeVarKind::Bound(bound) => {
                    if let Type::Class(c) = bound {
                        let inst = Instance::new(c.class(i_s.db), None);
                        let l = inst.lookup(
                            i_s,
                            name,
                            InstanceLookupOptions::new(add_issue)
                                .with_kind(kind)
                                .with_as_self_instance(&|| t.clone()),
                        );
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
                        return match type_ {
                            Type::Class(link) => Instance::new(
                                Class::with_undefined_generics(NodeRef::from_link(i_s.db, *link)),
                                &Inferred::from_type(Type::Class(*link, None)),
                            )
                            .lookup(i_s, name),
                            _ =>
                        }
                    }
                    */
                    let s = &i_s.db.python_state;
                    // TODO it's kind of stupid that we recreate an instance object here all the time, we
                    // should just use a precreated object() from somewhere.
                    callable(
                        self,
                        Instance::new(s.object_class(), None)
                            .lookup_with_details(i_s, add_issue, name, kind),
                    )
                }
                TypeVarKind::Unrestricted => {
                    let s = &i_s.db.python_state;
                    // TODO it's kind of stupid that we recreate an instance object here all the time, we
                    // should just use a precreated object() from somewhere.
                    callable(
                        self,
                        Instance::new(s.object_class(), None)
                            .lookup_with_details(i_s, add_issue, name, kind),
                    )
                }
            },
            Type::Tuple(tup) => callable(self, lookup_on_tuple(tup, i_s, add_issue, name)),
            Type::Union(union) => {
                for t in union.iter() {
                    t.run_after_lookup_on_each_union_member(
                        i_s,
                        None,
                        from_file,
                        name,
                        kind,
                        result_context,
                        &add_issue,
                        callable,
                    )
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
            ),
            Type::Callable(_) | Type::FunctionOverload(_) => callable(
                self,
                Instance::new(i_s.db.python_state.function_class(), None)
                    .lookup_with_details(i_s, add_issue, name, kind),
            ),
            Type::Module(file_index) => {
                let module = Module::from_file_index(i_s.db, *file_index);
                let lookup = module.lookup(i_s.db, add_issue, name);
                let mut attr_kind = AttributeKind::Attribute;
                if let Some(inf) = lookup.maybe_inferred() {
                    if inf.maybe_saved_specific(i_s.db)
                        == Some(Specific::AnnotationOrTypeCommentFinal)
                    {
                        attr_kind = AttributeKind::Final
                    }
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
                let current_class = i_s.current_class().expect("Self missing");
                let class_infos = current_class.use_cached_class_infos(i_s.db);
                if let Some(t) = class_infos.undefined_generics_type.get() {
                    if matches!(t.as_ref(), Type::Enum(_)) {
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
                }
                let inst = Instance::new(
                    Class::with_self_generics(
                        i_s.db,
                        current_class.node_ref.to_db_lifetime(i_s.db),
                    ),
                    from_inferred,
                );
                let l = inst.lookup_on_self(i_s, &add_issue, name, kind);
                callable(self, l)
            }
            Type::Super {
                class,
                bound_to,
                mro_index,
            } => {
                let class = class.class(i_s.db);
                let l = if matches!(bound_to.as_ref(), Type::Type(_)) {
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
                            .with_as_self_instance(&|| (**bound_to).clone()),
                    )
                };
                if matches!(&l.lookup, LookupResult::None) {
                    add_issue(IssueKind::UndefinedInSuperclass { name: name.into() });
                    callable(self, LookupDetails::any(AnyCause::FromError));
                    return;
                }
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
            Type::Never(_) => (),
            Type::NewType(new_type) => {
                let t = new_type.type_(i_s);
                if let Type::Class(c) = t {
                    let l = Instance::new(c.class(i_s.db), None).lookup(
                        i_s,
                        name,
                        InstanceLookupOptions::new(add_issue)
                            .with_kind(kind)
                            .with_as_self_instance(&|| self.clone()),
                    );
                    callable(self, l)
                } else {
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
                    from_file: FileIndex,
                    add_issue: &dyn Fn(IssueKind),
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
        add_issue: &dyn Fn(IssueKind),
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
                    callable(t.get_item_internal(i_s, None, slice_type, result_context, add_issue))
                }
            }),
            Type::TypeVar(tv) => match &tv.type_var.kind {
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
                    .inference(i_s)
                    .compute_type_application_on_dataclass(d, *slice_type, false),
                Type::NamedTuple(nt) => slice_type
                    .file
                    .inference(i_s)
                    .compute_type_application_on_named_tuple(nt.clone(), *slice_type, false),
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
                    .inference(i_s)
                    .compute_type_application_on_typed_dict(
                        td,
                        *slice_type,
                        matches!(
                            result_context,
                            ResultContext::AssignmentNewDefinition { .. }
                        ),
                    ),
                _ => not_possible(true),
            },
            Type::NewType(new_type) => new_type.type_(i_s).get_item_internal(
                i_s,
                None,
                slice_type,
                result_context,
                add_issue,
            ),
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
            Type::Self_ => i_s.current_class().unwrap().instance().get_item(
                i_s,
                slice_type,
                result_context,
                self,
                add_issue,
            ),
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
        self.get_item_internal(i_s, None, slice_type, &mut ResultContext::Unknown, &|_| ())
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
                for entry in union.iter() {
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
            Type::TypeVar(tv) => match &tv.type_var.kind {
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
            Type::DataclassTransformObj(d) => Inferred::from_type({
                let d = DataclassTransformObj {
                    executed_by_function: true,
                    ..d.clone()
                };
                Type::DataclassTransformObj(d)
            }),
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
                    items.push(t.iter(i_s, with_union_infos));
                }
                IteratorContent::Union(items)
            }
            Type::TypeVar(tv) => match &tv.type_var.kind {
                TypeVarKind::Bound(bound) => bound.iter(i_s, infos),
                _ => {
                    infos.add_not_iterable_issue(i_s.db, self);
                    IteratorContent::Any(AnyCause::FromError)
                }
            },
            Type::NewType(n) => n.type_(i_s).iter(i_s, infos),
            Type::Self_ => Instance::new(i_s.current_class().unwrap(), None).iter(i_s, self, infos),
            Type::RecursiveType(rec) => rec.calculated_type(i_s.db).iter(i_s, infos),
            Type::Intersection(i) => i.iter(i_s, infos),
            _ => IteratorContent::Inferred(
                self.lookup(
                    i_s,
                    infos.file().file_index,
                    "__iter__",
                    LookupKind::OnlyType,
                    &mut ResultContext::Unknown,
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
                ),
            ),
        }
    }
}

#[derive(Copy, Clone)]
pub enum IterCause {
    Iter,             // for i in *x
    AssignmentUnpack, // a, b = *x
    VariadicUnpack,   // [*x] or foo(*x)
}

#[derive(Copy, Clone)]
pub(crate) struct IterInfos<'x> {
    from: NodeRef<'x>,
    cause: IterCause,
    in_union: Option<&'x Type>,
    pub add_issue: &'x dyn Fn(IssueKind),
}

impl<'x> IterInfos<'x> {
    pub(crate) fn new(
        from: NodeRef<'x>,
        cause: IterCause,
        add_issue: &'x dyn Fn(IssueKind),
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
        })
    }

    pub(crate) fn with_different_add_issue<'y: 'x>(
        &'y self,
        add_issue: &'y dyn Fn(IssueKind),
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

    pub fn add_issue(&self, issue: IssueKind) {
        (self.add_issue)(issue)
    }
}

pub(crate) fn attribute_access_of_type(
    i_s: &InferenceState,
    add_issue: &dyn Fn(IssueKind),
    name: &str,
    kind: LookupKind,
    result_context: &mut ResultContext,
    callable: &mut impl FnMut(&Type, LookupDetails),
    in_type: Rc<Type>,
) {
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
                    Rc::new(t.clone()),
                )
            }
            return;
        }
        Type::TypeVar(t) => match &t.type_var.kind {
            TypeVarKind::Bound(bound) => match bound {
                Type::Class(c) => c.class(i_s.db).lookup(
                    i_s,
                    name,
                    ClassLookupOptions::new(&add_issue)
                        .with_kind(kind)
                        .with_as_type_type(&|| Type::Type(in_type.clone())),
                ),
                _ => {
                    return attribute_access_of_type(
                        i_s,
                        add_issue,
                        name,
                        kind,
                        result_context,
                        callable,
                        Rc::new(bound.clone()),
                    )
                }
            },
            _ => LookupDetails::none(),
        },
        Type::Class(g) => g.class(i_s.db).lookup(
            i_s,
            name,
            ClassLookupOptions::new(&add_issue).with_kind(kind),
        ),
        Type::Literal(l) => l.as_instance(i_s.db).class.lookup(
            i_s,
            name,
            ClassLookupOptions::new(&add_issue).with_kind(kind),
        ),
        Type::Callable(_) => LookupDetails::none(),
        Type::Self_ => i_s.current_class().unwrap().lookup(
            i_s,
            name,
            ClassLookupOptions::new(&add_issue)
                .with_kind(kind)
                .with_as_type_type(&|| Type::Type(in_type.clone())),
        ),
        Type::Any(cause) => i_s
            .db
            .python_state
            .bare_type_class()
            .instance()
            .lookup_with_details(i_s, add_issue, name, kind)
            .or_else(|| LookupDetails::any(*cause)),
        Type::Enum(e) => lookup_on_enum_class(i_s, add_issue, &in_type, e, name),
        Type::Dataclass(d) => lookup_on_dataclass_type(&in_type, d, i_s, add_issue, name, kind),
        Type::TypedDict(_) => i_s.db.python_state.typed_dict_class().lookup(
            i_s,
            name,
            ClassLookupOptions::new(&add_issue).with_kind(kind),
        ),
        Type::NamedTuple(nt) => nt.type_lookup(i_s, name, Some(&|| (*in_type).clone())),
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
                add_issue: &dyn Fn(IssueKind),
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
                            Rc::new(t.clone()),
                        );
                    },
                    add_issue,
                    callable,
                );
            }
            on_intersection(i, i_s, add_issue, name, kind, result_context, callable);
            return;
        }
        t => unreachable!("Type getattr {name} on {t:?}"),
    };
    callable(&Type::Type(in_type.clone()), details)
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
        Type::TypeVar(t) => match &t.type_var.kind {
            TypeVarKind::Bound(bound) => {
                execute_type_of_type(i_s, args, result_context, on_type_error, bound);
                Inferred::from_type(type_.clone())
            }
            _ => {
                args.add_issue(
                    i_s,
                    IssueKind::NotCallable {
                        type_: format!("\"{}\"", type_.format_short(i_s.db)).into(),
                    },
                );
                Inferred::new_any_from_error()
            }
        },
        Type::NewType(n) => {
            execute_type_of_type(i_s, args, result_context, on_type_error, n.type_(i_s));
            Inferred::from_type(type_.clone())
        }
        Type::Self_ => {
            i_s.current_class()
                .unwrap()
                .execute(i_s, args, result_context, on_type_error, true);
            Inferred::from_type(Type::Self_)
        }
        Type::Any(cause) => Inferred::new_any(*cause),
        Type::Dataclass(d) => dataclass_initialize(d, i_s, args, result_context, on_type_error),
        Type::TypedDict(td) => initialize_typed_dict(td.clone(), i_s, args),
        Type::NamedTuple(nt) => {
            let calculated_type_vars = calculate_callable_type_vars_and_return(
                i_s,
                Callable::new(&nt.__new__, None),
                args.iter(i_s.mode),
                |issue| args.add_issue(i_s, issue),
                true,
                &mut ResultContext::Unknown,
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
                let mut __new__ = Rc::unwrap_or_clone(__new__);
                __new__.type_vars = i_s.db.python_state.empty_type_var_likes.clone();
                Rc::new(NamedTuple::new(nt.name, __new__))
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
        _ => unreachable!(
            "Did we not handle a type execution for \"{}\"?",
            type_.format_short(i_s.db)
        ),
    }
}
