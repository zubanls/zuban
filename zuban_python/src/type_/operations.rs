use std::rc::Rc;

use super::{
    dataclass_initialize, initialize_typed_dict, lookup_dataclass_symbol, lookup_on_dataclass,
    lookup_on_dataclass_type, lookup_on_enum_class, lookup_on_enum_instance,
    lookup_on_enum_member_instance, lookup_on_typed_dict,
    tuple::{lookup_on_tuple, lookup_tuple_magic_methods},
    AnyCause, Type, TypeVarKind,
};
use crate::{
    arguments::{Arguments, NoArguments},
    debug,
    diagnostics::IssueType,
    getitem::SliceType,
    inference_state::InferenceState,
    inferred::Inferred,
    matching::{
        calculate_callable_type_vars_and_return, ErrorTypes, GotType, IteratorContent, LookupKind,
        LookupResult, Match, Matcher, OnLookupError, OnTypeError, ResultContext,
    },
    node_ref::NodeRef,
    type_::NamedTuple,
    type_helpers::{
        lookup_in_namespace, Callable, Class, Instance, Module, OverloadedFunction, TypeOrClass,
    },
};

impl Type {
    pub fn lookup(
        &self,
        i_s: &InferenceState,
        from: NodeRef,
        name: &str,
        lookup_kind: LookupKind,
        result_context: &mut ResultContext,
        on_lookup_error: OnLookupError,
    ) -> LookupResult {
        let mut result: Option<LookupResult> = None;
        self.run_after_lookup_on_each_union_member(
            i_s,
            None,
            from,
            name,
            lookup_kind,
            result_context,
            &mut |t, _, lookup_result| {
                if matches!(lookup_result, LookupResult::None) {
                    on_lookup_error(t);
                }
                result = Some(if let Some(l) = result.take() {
                    LookupResult::UnknownName(
                        l.into_inferred()
                            .simplified_union(i_s, lookup_result.into_inferred()),
                    )
                } else {
                    lookup_result
                })
            },
        );
        result.unwrap_or_else(|| todo!())
    }

    pub fn lookup_symbol<'db: 'a, 'a>(
        &'a self,
        i_s: &InferenceState<'db, '_>,
        name: &str,
    ) -> (Option<Class<'a>>, LookupResult) {
        match self {
            Type::Class(c) => todo!(),
            Type::Dataclass(d) => lookup_dataclass_symbol(d, i_s, name),
            Type::TypedDict(_) => todo!(),
            Type::Tuple(tuple) => (None, lookup_tuple_magic_methods(tuple.clone(), name)),
            Type::NamedTuple(nt) => (
                Some(i_s.db.python_state.typing_named_tuple_class()),
                nt.type_lookup(i_s, name, None),
            ),
            Type::Callable(t) => todo!(),
            _ => todo!("{name:?} {self:?}"),
        }
    }

    #[inline]
    pub fn run_after_lookup_on_each_union_member(
        &self,
        i_s: &InferenceState,
        from_inferred: Option<&Inferred>,
        from: NodeRef,
        name: &str,
        kind: LookupKind,
        result_context: &mut ResultContext,
        callable: &mut impl FnMut(&Type, Option<TypeOrClass>, LookupResult),
    ) {
        let add_issue = |issue| from.add_issue(i_s, issue);
        match self {
            Type::Class(c) => {
                let inst = Instance::new(c.class(i_s.db), from_inferred);
                let l = inst.lookup_with_details(i_s, add_issue, name, kind);
                callable(self, Some(l.class), l.lookup)
            }
            Type::Any(cause) => callable(self, None, LookupResult::any(*cause)),
            Type::None => callable(
                self,
                None,
                i_s.db
                    .python_state
                    .none_instance()
                    .lookup(i_s, add_issue, name, kind),
            ),
            Type::Literal(literal) => {
                let instance = i_s.db.python_state.literal_instance(&literal.kind);
                let l = instance.lookup_with_details(i_s, add_issue, name, kind);
                callable(self, Some(l.class), l.lookup)
            }
            t @ Type::TypeVar(usage) => match &usage.type_var.kind {
                TypeVarKind::Bound(bound) => {
                    bound.run_after_lookup_on_each_union_member(
                        i_s,
                        None,
                        from,
                        name,
                        kind,
                        result_context,
                        callable,
                    );
                }
                TypeVarKind::Constraints(constraints) => {
                    debug!("TODO type var values");
                    /*
                    for type_ in constraints.iter() {
                        return match type_ {
                            Type::Class(link) => Instance::new(
                                Class::with_undefined_generics(NodeRef::from_link(i_s.db, *link)),
                                &Inferred::from_type(Type::Class(*link, None)),
                            )
                            .lookup(i_s, name),
                            _ => todo!("{:?}", type_),
                        }
                    }
                    */
                    let s = &i_s.db.python_state;
                    // TODO it's kind of stupid that we recreate an instance object here all the time, we
                    // should just use a precreated object() from somewhere.
                    callable(
                        self,
                        None,
                        Instance::new(s.object_class(), None).lookup(i_s, add_issue, name, kind),
                    )
                }
                TypeVarKind::Unrestricted => {
                    let s = &i_s.db.python_state;
                    // TODO it's kind of stupid that we recreate an instance object here all the time, we
                    // should just use a precreated object() from somewhere.
                    callable(
                        self,
                        None,
                        Instance::new(s.object_class(), None).lookup(i_s, add_issue, name, kind),
                    )
                }
            },
            Type::Tuple(tup) => callable(
                self,
                None,
                lookup_on_tuple(tup.clone(), i_s, add_issue, name),
            ),
            Type::Union(union) => {
                for t in union.iter() {
                    t.run_after_lookup_on_each_union_member(
                        i_s,
                        None,
                        from,
                        name,
                        kind,
                        result_context,
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
                None,
                Instance::new(i_s.db.python_state.function_class(), None)
                    .lookup(i_s, add_issue, name, kind),
            ),
            Type::Module(file_index) => {
                let module = Module::from_file_index(i_s.db, *file_index);
                callable(self, None, module.lookup(i_s, add_issue, name))
            }
            Type::Namespace(namespace) => callable(
                self,
                None,
                lookup_in_namespace(i_s.db, from.file_index(), namespace, name),
            ),
            Type::Self_ => {
                let current_class = i_s.current_class().unwrap();
                let type_var_likes = current_class.type_vars(i_s);
                let inst = Instance::new(
                    Class::with_self_generics(
                        i_s.db,
                        current_class.node_ref.to_db_lifetime(i_s.db),
                    ),
                    from_inferred,
                );
                let l = inst.lookup_on_self(i_s, &add_issue, name, kind);
                callable(self, Some(l.class), l.lookup)
            }
            Type::Super { class, mro_index } => {
                let instance = Instance::new(class.class(i_s.db), None);
                let l = instance.lookup_and_maybe_ignore_super_count(
                    i_s,
                    add_issue,
                    name,
                    LookupKind::OnlyType,
                    mro_index + 1,
                );
                if matches!(&l.lookup, LookupResult::None) {
                    add_issue(IssueType::UndefinedInSuperclass { name: name.into() });
                    callable(
                        self,
                        None,
                        LookupResult::UnknownName(Inferred::new_any_from_error()),
                    );
                    return;
                }
                callable(self, Some(l.class), l.lookup)
            }
            Type::Dataclass(d) => callable(
                self,
                None,
                lookup_on_dataclass(d.clone(), i_s, add_issue, name),
            ),
            Type::TypedDict(td) => callable(
                self,
                None,
                lookup_on_typed_dict(td.clone(), i_s, add_issue, name, kind),
            ),
            Type::NamedTuple(nt) => {
                callable(self, None, nt.lookup(i_s, name, Some(&|| self.clone())))
            }
            Type::Never => (),
            Type::NewType(new_type) => new_type.type_(i_s).run_after_lookup_on_each_union_member(
                i_s,
                None,
                from,
                name,
                kind,
                result_context,
                callable,
            ),
            Type::Enum(e) => callable(
                self,
                None,
                lookup_on_enum_instance(i_s, add_issue, e, name, result_context),
            ),
            Type::EnumMember(member) => callable(
                self,
                None,
                lookup_on_enum_member_instance(i_s, add_issue, member, name),
            ),
            Type::RecursiveType(r) => r
                .calculated_type(i_s.db)
                .run_after_lookup_on_each_union_member(
                    i_s,
                    None,
                    from,
                    name,
                    kind,
                    result_context,
                    callable,
                ),
            _ => todo!("{self:?}"),
        }
    }

    pub fn get_item(
        &self,
        i_s: &InferenceState,
        from_inferred: Option<&Inferred>,
        slice_type: &SliceType,
        result_context: &mut ResultContext,
    ) -> Inferred {
        let not_possible = || {
            slice_type
                .as_node_ref()
                .add_issue(i_s, IssueType::OnlyClassTypeApplication);
            slice_type.infer(i_s);
            Inferred::new_any_from_error()
        };
        match self {
            Type::Class(c) => Instance::new(c.class(i_s.db), from_inferred).get_item(
                i_s,
                slice_type,
                result_context,
            ),
            Type::Any(cause) => {
                // Make sure the slices are inferred
                slice_type.infer(i_s);
                Inferred::new_any(*cause)
            }
            Type::Tuple(tup) => tup.get_item(i_s, slice_type, result_context),
            Type::NamedTuple(nt) => nt.get_item(i_s, slice_type, result_context),
            Type::Union(union) => Inferred::gather_simplified_union(i_s, |callable| {
                for t in union.iter() {
                    callable(t.get_item(i_s, None, slice_type, result_context))
                }
            }),
            t @ Type::TypeVar(tv) => match &tv.type_var.kind {
                TypeVarKind::Bound(bound) => bound.get_item(i_s, None, slice_type, result_context),
                TypeVarKind::Constraints(constraints) => todo!(),
                TypeVarKind::Unrestricted => todo!(),
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
                        slice_type.as_node_ref().add_issue(
                            i_s,
                            IssueType::EnumIndexShouldBeAString {
                                actual: enum_index.format_short(i_s),
                            },
                        );
                    }
                    Inferred::from_type(t.clone())
                }
                Type::TypedDict(td) => slice_type
                    .file
                    .inference(i_s)
                    .compute_type_application_on_typed_dict(
                        td,
                        *slice_type,
                        matches!(result_context, ResultContext::AssignmentNewDefinition),
                    ),
                _ => not_possible(),
            },
            Type::NewType(new_type) => {
                new_type
                    .type_(i_s)
                    .get_item(i_s, None, slice_type, result_context)
            }
            Type::RecursiveType(r) => {
                r.calculated_type(i_s.db)
                    .get_item(i_s, None, slice_type, result_context)
            }
            Type::TypedDict(d) => d.get_item(i_s, slice_type, result_context, true),
            Type::Callable(_) => not_possible(),
            Type::FunctionOverload(_) => {
                not_possible();
                todo!("Please write a test that checks this");
            }
            Type::None => {
                debug!("TODO None[...]");
                slice_type.infer(i_s);
                Inferred::new_any(AnyCause::Todo)
            }
            Type::Literal(l) => i_s.db.python_state.literal_type(&l.kind).get_item(
                i_s,
                None,
                slice_type,
                result_context,
            ),
            Type::Self_ => {
                i_s.current_class()
                    .unwrap()
                    .instance()
                    .get_item(i_s, slice_type, result_context)
            }
            _ => todo!("get_item not implemented for {self:?}"),
        }
    }

    pub fn setitem_context(
        &self,
        i_s: &InferenceState,
        slice_type: &SliceType,
    ) -> Option<Inferred> {
        match self {
            Type::TypedDict(td) => {
                Some(td.get_item(i_s, slice_type, &mut ResultContext::Unknown, false))
            }
            _ => None,
        }
    }

    pub(crate) fn execute<'db>(
        &self,
        i_s: &InferenceState<'db, '_>,
        inferred_from: Option<&Inferred>,
        args: &dyn Arguments<'db>,
        result_context: &mut ResultContext,
        on_type_error: OnTypeError<'db, '_>,
    ) -> Inferred {
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
                _ => todo!(),
            },
            Type::Any(cause) => {
                args.iter().calculate_diagnostics(i_s);
                Inferred::new_any(*cause)
            }
            Type::Never => {
                args.iter().calculate_diagnostics(i_s);
                Inferred::new_any(AnyCause::Todo)
            }
            Type::CustomBehavior(custom) => {
                custom.execute(i_s, args, result_context, on_type_error)
            }
            _ => {
                let t = self.format_short(i_s.db);
                args.add_issue(
                    i_s,
                    IssueType::NotCallable {
                        type_: format!("\"{}\"", t).into(),
                    },
                );
                Inferred::new_any_from_error()
            }
        }
    }

    pub fn iter(&self, i_s: &InferenceState, from: NodeRef) -> IteratorContent {
        let on_error = |t: &Type| {
            from.add_issue(
                i_s,
                IssueType::NotIterable {
                    type_: format!("\"{}\"", t.format_short(i_s.db)).into(),
                },
            );
        };
        match self {
            Type::Class(c) => Instance::new(c.class(i_s.db), None).iter(i_s, from),
            Type::Tuple(tuple) => tuple.iter(i_s, from),
            Type::NamedTuple(nt) => nt.iter(i_s, from),
            Type::Union(union) => {
                let mut items = vec![];
                for t in union.iter() {
                    items.push(t.iter(i_s, from));
                }
                IteratorContent::Union(items)
            }
            Type::TypeVar(tv) => match &tv.type_var.kind {
                TypeVarKind::Bound(bound) => bound.iter(i_s, from),
                TypeVarKind::Constraints(_) => todo!(),
                TypeVarKind::Unrestricted => {
                    on_error(self);
                    IteratorContent::Any(AnyCause::FromError)
                }
            },
            Type::NewType(n) => n.type_(i_s).iter(i_s, from),
            Type::Self_ => Instance::new(*i_s.current_class().unwrap(), None).iter(i_s, from),
            _ => IteratorContent::Inferred(
                self.lookup(
                    i_s,
                    from,
                    "__iter__",
                    LookupKind::OnlyType,
                    &mut ResultContext::Unknown,
                    &|t| {
                        on_error(t);
                    },
                )
                .into_inferred()
                .execute(i_s, &NoArguments::new(from))
                .type_lookup_and_execute(
                    i_s,
                    from,
                    "__next__",
                    &NoArguments::new(from),
                    &|_| todo!(),
                ),
            ),
        }
    }
}

pub(crate) fn attribute_access_of_type(
    i_s: &InferenceState,
    add_issue: &dyn Fn(IssueType),
    name: &str,
    kind: LookupKind,
    result_context: &mut ResultContext,
    callable: &mut impl FnMut(&Type, Option<TypeOrClass>, LookupResult),
    in_type: Rc<Type>,
) {
    let lookup_result = match in_type.as_ref() {
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
        Type::TypeVar(t) => {
            match &t.type_var.kind {
                TypeVarKind::Bound(bound) => attribute_access_of_type(
                    i_s,
                    add_issue,
                    name,
                    kind,
                    result_context,
                    callable,
                    Rc::new(bound.clone()),
                ),
                TypeVarKind::Constraints(_) => todo!(),
                TypeVarKind::Unrestricted => todo!(),
            }
            return;
        }
        Type::Class(g) => g.class(i_s.db).lookup(i_s, add_issue, name, kind),
        Type::Literal(l) => i_s
            .db
            .python_state
            .literal_instance(&l.kind)
            .class
            .lookup(i_s, add_issue, name, kind),
        Type::Callable(_) => LookupResult::None,
        Type::Self_ => i_s
            .current_class()
            .unwrap()
            .lookup(i_s, add_issue, name, kind),
        Type::Any(cause) => i_s
            .db
            .python_state
            .bare_type_class()
            .instance()
            .lookup(i_s, |issue| add_issue(issue), name, kind)
            .or_else(|| LookupResult::any(*cause)),
        t @ Type::Enum(e) => lookup_on_enum_class(i_s, add_issue, e, name, result_context),
        Type::Dataclass(d) => lookup_on_dataclass_type(d.clone(), i_s, add_issue, name, kind),
        Type::TypedDict(d) => i_s
            .db
            .python_state
            .typed_dict_class()
            .lookup(i_s, add_issue, name, kind),
        Type::NamedTuple(nt) => nt.type_lookup(i_s, name, Some(&|| (*in_type).clone())),
        Type::Tuple(tup) => i_s
            .db
            .python_state
            .tuple_class(i_s.db, tup)
            .lookup(i_s, add_issue, name, kind),
        Type::Type(_) => i_s
            .db
            .python_state
            .bare_type_class()
            .lookup(i_s, add_issue, name, kind),
        t => todo!("{name} on {t:?}"),
    };
    callable(&Type::Type(in_type.clone()), None, lookup_result)
}

pub(crate) fn execute_type_of_type<'db>(
    i_s: &InferenceState<'db, '_>,
    args: &dyn Arguments<'db>,
    result_context: &mut ResultContext,
    on_type_error: OnTypeError<'db, '_>,
    type_: &Type,
) -> Inferred {
    match type_ {
        #![allow(unreachable_code)]
        // TODO remove this
        tuple @ Type::Tuple(tuple_content) => {
            debug!("TODO this does not check the arguments");
            return Inferred::from_type(tuple.clone());
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
                todo!()
            }
            let other = inferred_tup.as_cow_type(i_s);
            if let Match::False { ref reason, .. } = tuple.is_simple_super_type_of(i_s, &other) {
                let error_types = ErrorTypes {
                    matcher: &Matcher::default(),
                    reason,
                    got: GotType::Type(tuple),
                    expected: &other,
                };
                (on_type_error.callback)(i_s, &|_| todo!(), &arg, error_types);
            }
            Inferred::from_type(tuple.clone())
        }
        Type::Class(c) => c
            .class(i_s.db)
            .execute(i_s, args, result_context, on_type_error, true),
        Type::TypeVar(t) => match &t.type_var.kind {
            TypeVarKind::Bound(bound) => {
                execute_type_of_type(i_s, args, result_context, on_type_error, bound);
                Inferred::from_type(type_.clone())
            }
            TypeVarKind::Constraints(constraints) => todo!(),
            TypeVarKind::Unrestricted => todo!(),
        },
        Type::NewType(n) => {
            let mut iterator = args.iter();
            if let Some(first) = iterator.next() {
                if iterator.next().is_some() {
                    todo!()
                }
                // TODO match
                Inferred::from_type(type_.clone())
            } else {
                todo!()
            }
        }
        Type::Self_ => {
            i_s.current_class()
                .unwrap()
                .execute(i_s, args, result_context, on_type_error, true);
            Inferred::from_type(Type::Self_)
        }
        Type::Any(cause) => Inferred::new_any(*cause),
        Type::Dataclass(d) => dataclass_initialize(d, i_s, args, result_context, on_type_error),
        Type::TypedDict(td) => {
            initialize_typed_dict(td.clone(), i_s, args, result_context, on_type_error)
        }
        Type::NamedTuple(nt) => {
            let calculated_type_vars = calculate_callable_type_vars_and_return(
                i_s,
                Callable::new(&nt.__new__, None),
                args.iter(),
                |issue| args.add_issue(i_s, issue),
                true,
                &mut ResultContext::Unknown,
                Some(on_type_error),
            );
            Inferred::from_type(Type::NamedTuple(if nt.__new__.type_vars.is_empty() {
                nt.clone()
            } else {
                let mut __new__ = Type::replace_type_var_likes_and_self_for_callable(
                    &nt.__new__,
                    i_s.db,
                    &mut |usage| calculated_type_vars.lookup_type_var_usage(i_s, usage),
                    &|| Type::Self_,
                );
                __new__.type_vars = i_s.db.python_state.empty_type_var_likes.clone();
                Rc::new(NamedTuple::new(nt.name, __new__))
            }))
        }
        Type::Enum(_) => {
            debug!("TODO did not check arguments in execution of enum");
            Inferred::from_type(type_.clone())
        }
        Type::Union(union) => Inferred::gather_base_types(i_s, |gather| {
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
        _ => todo!("{:?}", type_),
    }
}
