use std::rc::Rc;

use crate::{
    arguments::{Arguments, NoArguments},
    debug,
    diagnostics::IssueType,
    getitem::SliceType,
    inference_state::InferenceState,
    inferred::Inferred,
    matching::{
        calculate_callable_type_vars_and_return, IteratorContent, LookupKind, LookupResult,
        OnLookupError, OnTypeError, ResultContext, Type,
    },
    node_ref::NodeRef,
    type_helpers::{
        lookup_in_namespace, lookup_on_enum_class, lookup_on_enum_instance,
        lookup_on_enum_member_instance, Callable, Class, DataclassHelper, Instance, Module,
        NamedTupleValue, OverloadedFunction, Tuple, TypedDictHelper,
    },
};

use super::{DbType, TypeVarKind};

impl DbType {
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
            &mut |t, lookup_result| {
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
            DbType::Class(c) => todo!(),
            DbType::Dataclass(d) => DataclassHelper(d).lookup_symbol(i_s, name),
            DbType::TypedDict(_) => todo!(),
            DbType::Tuple(t) => (None, LookupResult::None),
            DbType::NamedTuple(nt) => (None, NamedTupleValue::new(i_s.db, nt).lookup(i_s, name)),
            DbType::Callable(t) => todo!(),
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
        callable: &mut impl FnMut(&DbType, LookupResult),
    ) {
        match self {
            DbType::Class(c) => callable(
                self,
                Instance::new(c.class(i_s.db), from_inferred).lookup(i_s, from, name, kind),
            ),
            DbType::Any => callable(self, LookupResult::any()),
            DbType::None => callable(
                self,
                i_s.db
                    .python_state
                    .none_instance()
                    .lookup(i_s, from, name, kind),
            ),
            DbType::Literal(literal) => {
                let instance = i_s.db.python_state.literal_instance(&literal.kind);
                let result = instance.lookup(i_s, from, name, kind);
                callable(self, result)
            }
            t @ DbType::TypeVar(usage) => match &usage.type_var.kind {
                TypeVarKind::Bound(bound) => {
                    Type::new(bound).run_after_lookup_on_each_union_member(
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
                    for db_type in constraints.iter() {
                        return match db_type {
                            DbType::Class(link) => Instance::new(
                                Class::with_undefined_generics(NodeRef::from_link(i_s.db, *link)),
                                &Inferred::from_type(DbType::Class(*link, None)),
                            )
                            .lookup(i_s, name),
                            _ => todo!("{:?}", db_type),
                        }
                    }
                    */
                    let s = &i_s.db.python_state;
                    // TODO it's kind of stupid that we recreate an instance object here all the time, we
                    // should just use a precreated object() from somewhere.
                    callable(
                        self,
                        Instance::new(s.object_class(), None).lookup(i_s, from, name, kind),
                    )
                }
                TypeVarKind::Unrestricted => {
                    let s = &i_s.db.python_state;
                    // TODO it's kind of stupid that we recreate an instance object here all the time, we
                    // should just use a precreated object() from somewhere.
                    callable(
                        self,
                        Instance::new(s.object_class(), None).lookup(i_s, from, name, kind),
                    )
                }
            },
            DbType::Tuple(tup) => callable(self, Tuple::new(tup).lookup(i_s, from, name)),
            DbType::Union(union) => {
                for t in union.iter() {
                    Type::new(t).run_after_lookup_on_each_union_member(
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
            DbType::Type(t) => {
                attribute_access_of_type(i_s, from, name, kind, result_context, callable, t.clone())
            }
            DbType::Callable(_) | DbType::FunctionOverload(_) => callable(
                self,
                Instance::new(i_s.db.python_state.function_class(), None)
                    .lookup(i_s, from, name, kind),
            ),
            DbType::Module(file_index) => {
                let module = Module::from_file_index(i_s.db, *file_index);
                callable(self, module.lookup(i_s, from, name))
            }
            DbType::Namespace(namespace) => callable(
                self,
                lookup_in_namespace(i_s.db, from.file_index(), namespace, name),
            ),
            DbType::Self_ => {
                let current_class = i_s.current_class().unwrap();
                let type_var_likes = current_class.type_vars(i_s);
                callable(
                    self,
                    Instance::new(
                        Class::with_self_generics(
                            i_s.db,
                            current_class.node_ref.to_db_lifetime(i_s.db),
                        ),
                        from_inferred,
                    )
                    .lookup(i_s, from, name, kind),
                )
            }
            DbType::Super { class, mro_index } => {
                let instance = Instance::new(class.class(i_s.db), None);
                let result = instance
                    .lookup_and_maybe_ignore_super_count(
                        i_s,
                        from,
                        name,
                        LookupKind::OnlyType,
                        mro_index + 1,
                    )
                    .1;
                if matches!(&result, LookupResult::None) {
                    from.add_issue(i_s, IssueType::UndefinedInSuperclass { name: name.into() });
                    callable(self, LookupResult::UnknownName(Inferred::new_any()));
                    return;
                }
                callable(self, result)
            }
            DbType::Dataclass(d) => callable(self, DataclassHelper(d).lookup(i_s, from, name)),
            DbType::TypedDict(d) => {
                callable(self, TypedDictHelper(d).lookup(i_s, from, name, kind))
            }
            DbType::NamedTuple(nt) => {
                callable(self, NamedTupleValue::new(i_s.db, nt).lookup(i_s, name))
            }
            DbType::Never => (),
            DbType::NewType(new_type) => Type::new(new_type.type_(i_s))
                .run_after_lookup_on_each_union_member(
                    i_s,
                    None,
                    from,
                    name,
                    kind,
                    result_context,
                    callable,
                ),
            DbType::Enum(e) => callable(
                self,
                lookup_on_enum_instance(i_s, from, e, name, result_context),
            ),
            DbType::EnumMember(member) => callable(
                self,
                lookup_on_enum_member_instance(i_s, from, member, name),
            ),
            DbType::RecursiveAlias(r) => Type::new(r.calculated_db_type(i_s.db))
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
        let inf = match self {
            DbType::Class(c) => Instance::new(c.class(i_s.db), from_inferred).get_item(
                i_s,
                slice_type,
                result_context,
            ),
            DbType::Any => Inferred::new_any(),
            DbType::Tuple(tup) => Tuple::new(tup).get_item(i_s, slice_type, result_context),
            DbType::NamedTuple(nt) => {
                NamedTupleValue::new(i_s.db, nt).get_item(i_s, slice_type, result_context)
            }
            DbType::Union(union) => Inferred::gather_simplified_union(i_s, |callable| {
                for t in union.iter() {
                    callable(Type::new(t).get_item(i_s, None, slice_type, result_context))
                }
            }),
            t @ DbType::TypeVar(tv) => match &tv.type_var.kind {
                TypeVarKind::Bound(bound) => {
                    Type::new(bound).get_item(i_s, None, slice_type, result_context)
                }
                TypeVarKind::Constraints(constraints) => todo!(),
                TypeVarKind::Unrestricted => todo!(),
            },
            DbType::Type(t) => match t.as_ref() {
                DbType::Class(c) => c.class(i_s.db).get_item(i_s, slice_type, result_context),
                DbType::Dataclass(d) => slice_type
                    .file
                    .inference(i_s)
                    .compute_type_application_on_dataclass(d, *slice_type, false),
                t @ DbType::Enum(_) => {
                    let enum_index = slice_type.infer(i_s);
                    if !enum_index
                        .as_type(i_s)
                        .is_simple_sub_type_of(i_s, &Type::owned(i_s.db.python_state.str_db_type()))
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
                DbType::TypedDict(td) => slice_type
                    .file
                    .inference(i_s)
                    .compute_type_application_on_typed_dict(
                        td,
                        *slice_type,
                        matches!(result_context, ResultContext::AssignmentNewDefinition),
                    ),
                _ => {
                    slice_type
                        .as_node_ref()
                        .add_issue(i_s, IssueType::OnlyClassTypeApplication);
                    Inferred::new_any()
                }
            },
            DbType::NewType(new_type) => {
                Type::new(new_type.type_(i_s)).get_item(i_s, None, slice_type, result_context)
            }
            DbType::RecursiveAlias(r) => Type::new(r.calculated_db_type(i_s.db)).get_item(
                i_s,
                None,
                slice_type,
                result_context,
            ),
            DbType::TypedDict(d) => TypedDictHelper(d).get_item(i_s, slice_type, result_context),
            DbType::Callable(_) => {
                slice_type
                    .as_node_ref()
                    .add_issue(i_s, IssueType::OnlyClassTypeApplication);
                Inferred::new_unknown()
            }
            DbType::FunctionOverload(_) => {
                slice_type
                    .as_node_ref()
                    .add_issue(i_s, IssueType::OnlyClassTypeApplication);
                todo!("Please write a test that checks this");
            }
            DbType::None => {
                debug!("TODO None[...]");
                Inferred::new_any()
            }
            DbType::Literal(l) => i_s.db.python_state.literal_type(&l.kind).get_item(
                i_s,
                None,
                slice_type,
                result_context,
            ),
            _ => todo!("get_item not implemented for {self:?}"),
        };
        // Make sure the slices are inferred
        slice_type.infer(i_s);
        inf
    }

    pub fn execute<'db>(
        &self,
        i_s: &InferenceState<'db, '_>,
        inferred_from: Option<&Inferred>,
        args: &dyn Arguments<'db>,
        result_context: &mut ResultContext,
        on_type_error: OnTypeError<'db, '_>,
    ) -> Inferred {
        match self {
            DbType::Class(c) => {
                let cls = c.class(i_s.db);
                Instance::new(cls, inferred_from).execute(i_s, args, result_context, on_type_error)
            }
            DbType::Type(cls) => {
                execute_type_of_type(i_s, args, result_context, on_type_error, cls.as_ref())
            }
            DbType::Union(union) => Inferred::gather_simplified_union(i_s, |gather| {
                for entry in union.iter() {
                    gather(Type::new(entry).execute(i_s, None, args, result_context, on_type_error))
                }
            }),
            DbType::Callable(content) => {
                Callable::new(content, None).execute(i_s, args, on_type_error, result_context)
            }
            DbType::FunctionOverload(overload) => OverloadedFunction::new(overload, None).execute(
                i_s,
                args,
                result_context,
                on_type_error,
            ),
            DbType::TypeVar(tv) => match &tv.type_var.kind {
                TypeVarKind::Bound(bound) => {
                    Type::new(bound).execute(i_s, None, args, result_context, on_type_error)
                }
                _ => todo!(),
            },
            DbType::Any | DbType::Never => {
                args.iter().calculate_diagnostics(i_s);
                Inferred::new_any()
            }
            DbType::CustomBehavior(custom) => {
                custom.execute(i_s, args, result_context, on_type_error)
            }
            _ => {
                let t = self.format_short(i_s.db);
                args.as_node_ref().add_issue(
                    i_s,
                    IssueType::NotCallable {
                        type_: format!("\"{}\"", t).into(),
                    },
                );
                Inferred::new_unknown()
            }
        }
    }

    pub fn iter(&self, i_s: &InferenceState, from: NodeRef) -> IteratorContent {
        let on_error = |t: &DbType| {
            from.add_issue(
                i_s,
                IssueType::NotIterable {
                    type_: format!("\"{}\"", t.format_short(i_s.db)).into(),
                },
            );
        };
        match self {
            DbType::Class(c) => Instance::new(c.class(i_s.db), None).iter(i_s, from),
            DbType::Tuple(content) => Tuple::new(content).iter(i_s, from),
            DbType::NamedTuple(nt) => NamedTupleValue::new(i_s.db, nt).iter(i_s, from),
            DbType::Union(union) => {
                let mut items = vec![];
                for t in union.iter() {
                    items.push(Type::new(t).iter(i_s, from));
                }
                IteratorContent::Union(items)
            }
            DbType::TypeVar(tv) => match &tv.type_var.kind {
                TypeVarKind::Bound(bound) => Type::new(bound).iter(i_s, from),
                TypeVarKind::Constraints(_) => todo!(),
                TypeVarKind::Unrestricted => {
                    on_error(self);
                    IteratorContent::Any
                }
            },
            DbType::NewType(n) => Type::new(n.type_(i_s)).iter(i_s, from),
            DbType::Self_ => Instance::new(*i_s.current_class().unwrap(), None).iter(i_s, from),
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

pub fn attribute_access_of_type(
    i_s: &InferenceState,
    from: NodeRef,
    name: &str,
    kind: LookupKind,
    result_context: &mut ResultContext,
    callable: &mut impl FnMut(&DbType, LookupResult),
    in_type: Rc<DbType>,
) {
    let lookup_result = match in_type.as_ref() {
        DbType::Union(union) => {
            debug_assert!(union.entries.len() > 1);
            for t in union.iter() {
                attribute_access_of_type(
                    i_s,
                    from,
                    name,
                    kind,
                    result_context,
                    callable,
                    Rc::new(t.clone()),
                )
            }
            return;
        }
        DbType::TypeVar(t) => {
            match &t.type_var.kind {
                TypeVarKind::Bound(bound) => attribute_access_of_type(
                    i_s,
                    from,
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
        DbType::Class(g) => g.class(i_s.db).lookup(i_s, from, name, kind),
        DbType::Literal(l) => i_s
            .db
            .python_state
            .literal_instance(&l.kind)
            .class
            .lookup(i_s, from, name, kind),
        DbType::Callable(_) => LookupResult::None,
        DbType::Self_ => i_s.current_class().unwrap().lookup(i_s, from, name, kind),
        DbType::Any => i_s
            .db
            .python_state
            .bare_type_class()
            .instance()
            .lookup(i_s, from, name, kind)
            .or_else(|| LookupResult::any()),
        t @ DbType::Enum(e) => lookup_on_enum_class(i_s, from, e, name, result_context),
        DbType::Dataclass(d) => DataclassHelper(d).lookup_on_type(i_s, from, name, kind),
        DbType::TypedDict(d) => i_s
            .db
            .python_state
            .typed_dict_class()
            .lookup(i_s, from, name, kind),
        DbType::NamedTuple(nt) => match name {
            "__new__" => {
                LookupResult::UnknownName(Inferred::from_type(DbType::Callable(nt.__new__.clone())))
            }
            _ => todo!(),
        },
        DbType::Tuple(tup) => i_s
            .db
            .python_state
            .tuple_class(i_s.db, tup)
            .lookup(i_s, from, name, kind),
        DbType::Type(_) => i_s
            .db
            .python_state
            .bare_type_class()
            .lookup(i_s, from, name, kind),
        t => todo!("{name} on {t:?}"),
    };
    callable(&Type::owned(DbType::Type(in_type.clone())), lookup_result)
}

pub fn execute_type_of_type<'db>(
    i_s: &InferenceState<'db, '_>,
    args: &dyn Arguments<'db>,
    result_context: &mut ResultContext,
    on_type_error: OnTypeError<'db, '_>,
    type_: &DbType,
) -> Inferred {
    match type_ {
        #![allow(unreachable_code)]
        // TODO remove this
        tuple @ DbType::Tuple(tuple_content) => {
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
            Type::new(tuple).error_if_not_matches(i_s, &inferred_tup, |t1, t2| {
                (on_type_error.callback)(i_s, &|_| todo!(), &arg, t1, t2);
                args.as_node_ref().to_db_lifetime(i_s.db)
            });
            Inferred::from_type(tuple.clone())
        }
        DbType::Class(c) => c
            .class(i_s.db)
            .execute(i_s, args, result_context, on_type_error),
        DbType::TypeVar(t) => match &t.type_var.kind {
            TypeVarKind::Bound(bound) => {
                execute_type_of_type(i_s, args, result_context, on_type_error, bound);
                Inferred::from_type(type_.clone())
            }
            TypeVarKind::Constraints(constraints) => todo!(),
            TypeVarKind::Unrestricted => todo!(),
        },
        DbType::NewType(n) => {
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
        DbType::Self_ => {
            i_s.current_class()
                .unwrap()
                .execute(i_s, args, result_context, on_type_error);
            Inferred::from_type(DbType::Self_)
        }
        DbType::Any => Inferred::new_any(),
        DbType::Dataclass(d) => {
            DataclassHelper(d).initialize(i_s, args, result_context, on_type_error)
        }
        DbType::TypedDict(td) => {
            TypedDictHelper(td).initialize(i_s, args, result_context, on_type_error)
        }
        DbType::NamedTuple(nt) => {
            let calculated_type_vars = calculate_callable_type_vars_and_return(
                i_s,
                Callable::new(&nt.__new__, None),
                args.iter(),
                &|| args.as_node_ref(),
                true,
                &mut ResultContext::Unknown,
                Some(on_type_error),
            );
            debug!("TODO use generics for namedtuple");
            Inferred::from_type(DbType::NamedTuple(nt.clone()))
        }
        DbType::Enum(_) => {
            debug!("TODO did not check arguments in execution of enum");
            Inferred::from_type(type_.clone())
        }
        DbType::Union(union) => Inferred::gather_base_types(i_s, |gather| {
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
