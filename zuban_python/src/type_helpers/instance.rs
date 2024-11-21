use std::{borrow::Cow, cell::Cell, rc::Rc};

use parsa_python_cst::Name;

use super::{
    class::{TypeOrClass, ORDERING_METHODS},
    Class, ClassLookupOptions, FirstParamKind, Function, MroIterator,
};
use crate::{
    arguments::{Args, CombinedArgs, InferredArg, KnownArgs, KnownArgsWithCustomAddIssue},
    database::{ComplexPoint, Database, PointLink, Specific},
    debug,
    diagnostics::IssueKind,
    file::on_argument_type_error,
    getitem::SliceType,
    inference_state::InferenceState,
    inferred::{add_attribute_error, AttributeKind, Inferred, MroIndex},
    matching::{ErrorStrs, IteratorContent, LookupKind, OnTypeError, ResultContext},
    node_ref::NodeRef,
    type_::{
        AnyCause, CallableLike, CallableParams, FunctionKind, IterInfos, LookupResult, Type,
        TypeVarKind,
    },
};

#[derive(Debug, Clone, Copy)]
pub struct Instance<'a> {
    pub class: Class<'a>,
    inferred: Option<&'a Inferred>,
}

impl<'a> Instance<'a> {
    pub fn new(class: Class<'a>, inferred: Option<&'a Inferred>) -> Self {
        Self { class, inferred }
    }

    pub fn as_inferred(&self, i_s: &InferenceState) -> Inferred {
        if let Some(inferred) = self.inferred {
            inferred.clone()
        } else {
            let t = self.class.as_type(i_s.db);
            Inferred::from_type(t)
        }
    }

    pub(crate) fn check_set_descriptor(
        &self,
        i_s: &InferenceState,
        from: NodeRef,
        name: Name,
        value: &Inferred,
    ) -> Result<(), ()> {
        let add_issue = |issue| from.add_issue(i_s, issue);

        let name_str = name.as_str();
        let property_is_read_only = |class_name| {
            add_issue(IssueKind::PropertyIsReadOnly {
                class_name,
                property_name: name_str.into(),
            });
            Err(())
        };
        if let Some(nt) = self.class.maybe_named_tuple_base(i_s.db) {
            if nt.search_param(i_s.db, name_str).is_some() {
                return property_is_read_only(nt.name(i_s.db).into());
            }
        }
        let check_compatible = |t: &Type, value: &_| {
            let mut had_errors = false;
            t.error_if_not_matches(i_s, value, add_issue, |error_types| {
                let ErrorStrs { expected, got } = error_types.as_boxed_strs(i_s.db);
                had_errors = true;
                Some(IssueKind::IncompatibleAssignment { got, expected })
            });
            if had_errors {
                Err(())
            } else {
                Ok(())
            }
        };

        let lookup_details = self
            .class
            .lookup(
                i_s,
                name_str,
                ClassLookupOptions::new(&|issue| from.add_issue(i_s, issue))
                    .without_descriptors()
                    .with_avoid_metaclass(),
            )
            .or_else(|| {
                self.lookup(
                    i_s,
                    name_str,
                    InstanceLookupOptions::new(&add_issue).with_no_check_dunder_getattr(),
                )
            });
        let Some(mut inf) = lookup_details.lookup.maybe_inferred() else {
            let t = self.class.as_type(i_s.db);
            let had_setattr_issue = Cell::new(false);
            let l = self.lookup_with_details(
                i_s,
                |_| had_setattr_issue.set(true),
                "__setattr__",
                LookupKind::OnlyType,
            );
            // setattr issues were probably caused by invalid functions and should have caused an
            // error earlier
            if let Some(setattr) = l
                .lookup
                .into_maybe_inferred()
                .filter(|_| !had_setattr_issue.get())
            {
                // object defines a __getattribute__ that returns Any
                if !l.class.is_object(i_s.db) {
                    // If it's not a callable with the correct signature, diagnostics will be raised
                    // elsewhere.
                    match setattr.as_cow_type(i_s).maybe_callable(i_s) {
                        Some(CallableLike::Callable(c)) => {
                            if let Some(second) = c.second_positional_type() {
                                return check_compatible(&second, value);
                            }
                        }
                        Some(CallableLike::Overload(o)) => {
                            let new_t = Type::from_iter(
                                o.iter_functions()
                                    .filter_map(|c| c.second_positional_type()),
                            );
                            return check_compatible(&new_t, value);
                        }
                        None => (),
                    };
                }
            }
            add_attribute_error(i_s, from, &t, &t, name_str);
            return Err(());
        };
        if inf.maybe_saved_specific(i_s.db) == Some(Specific::AnnotationOrTypeCommentClassVar) {
            add_issue(IssueKind::CannotAssignToClassVarViaInstance {
                name: name_str.into(),
            });
            return Err(());
        }
        if lookup_details.is_final(i_s.db) {
            from.add_issue(
                i_s,
                IssueKind::CannotAssignToFinal {
                    is_attribute: true,
                    name: name_str.into(),
                },
            );
            inf = Cow::Owned(inf.into_owned().avoid_implicit_literal(i_s));
        }

        let assign_to = inf.as_cow_type(i_s);
        match assign_to.as_ref() {
            Type::Class(c) => {
                let descriptor = c.class(i_s.db);
                if let Some(__set__) = Instance::new(descriptor, None)
                    .type_lookup(i_s, add_issue, "__set__")
                    .into_maybe_inferred()
                {
                    let inst = self.as_inferred(i_s);
                    calculate_descriptor(i_s, from, __set__, inst, value);
                    // Return an error regardless so it does not get narrowed.
                    return Err(());
                } else if let Some(inf) = Instance::new(descriptor, None).bind_dunder_get(
                    i_s,
                    add_issue,
                    self.class.as_type(i_s.db),
                ) {
                    // It feels weird that a descriptor that only defines __get__ should
                    // match the value with __get__'s return type. But this makes sense:
                    // When a descriptor does not define __set__, writing Foo().bar = 3 will
                    // write Foo.__dict__['bar'] = true instead of changing anything on
                    // the class attribute Foo.bar.
                    // Here we ensure that the contract that the __get__ descriptor gives us is
                    // not violated.
                    return check_compatible(&inf.as_cow_type(i_s), value);
                }
            }
            Type::Callable(c) if matches!(c.kind, FunctionKind::Property { .. }) => {
                return match c.kind {
                    FunctionKind::Property {
                        writable: false, ..
                    } => property_is_read_only(lookup_details.class.name(i_s.db).into()),
                    FunctionKind::Property { writable: true, .. } => {
                        check_compatible(&c.return_type, value)
                    }
                    _ => unreachable!(),
                }
            }
            Type::Callable(c) => {
                if !matches!(&c.params, CallableParams::Any(_)) {
                    if c.is_final {
                        add_issue(IssueKind::CannotAssignToFinal {
                            name: name_str.into(),
                            is_attribute: true,
                        });
                    } else if !lookup_details.attr_kind.is_overwritable() {
                        add_issue(IssueKind::CannotAssignToAMethod);
                    }
                }
            }
            _ => {}
        }
        if !assign_to
            .iter_with_unpacked_unions(i_s.db)
            .any(|t| t.is_any())
        {
            self.class.check_slots(i_s, add_issue, name_str);
        }
        check_compatible(assign_to.as_ref(), value)
    }

    pub(crate) fn bind_dunder_get(
        &self,
        i_s: &InferenceState,
        add_issue: impl Fn(IssueKind),
        instance: Type,
    ) -> Option<Inferred> {
        self.type_lookup(i_s, &add_issue, "__get__")
            .into_maybe_inferred()
            .map(|inf| {
                let c_t = Type::Type(Rc::new(instance.clone()));
                inf.execute(
                    i_s,
                    &CombinedArgs::new(
                        &KnownArgsWithCustomAddIssue::new(
                            &Inferred::from_type(instance),
                            &add_issue,
                        ),
                        &KnownArgsWithCustomAddIssue::new(&Inferred::from_type(c_t), &add_issue),
                    ),
                )
            })
    }

    pub(crate) fn execute<'db>(
        &self,
        i_s: &InferenceState<'db, '_>,
        args: &dyn Args<'db>,
        result_context: &mut ResultContext,
        on_type_error: OnTypeError,
    ) -> Inferred {
        if let Some(inf) = self
            .type_lookup(i_s, |issue| args.add_issue(i_s, issue), "__call__")
            .into_maybe_inferred()
        {
            inf.execute_with_details(i_s, args, result_context, on_type_error)
        } else {
            let t = self.class.format_short(i_s.db);
            args.add_issue(
                i_s,
                if self.class.node_ref == i_s.db.python_state.function_node_ref() {
                    IssueKind::UnknownFunctionNotCallable
                } else {
                    IssueKind::NotCallable {
                        type_: format!("{:?}", t).into(),
                    }
                },
            );
            Inferred::new_any_from_error()
        }
    }

    pub(crate) fn iter(&self, i_s: &InferenceState, infos: IterInfos) -> IteratorContent {
        if let Some(tup) = self.class.maybe_tuple_base(i_s.db) {
            // TODO this doesn't take care of the mro and could not be the first __iter__
            return tup.iter();
        }
        let mro_iterator = self.class.mro(i_s.db);
        let finder = ClassMroFinder {
            i_s,
            instance: self,
            mro_iterator,
            add_issue: infos.add_issue,
            name: "__iter__",
            as_instance: None,
        };
        for found_on_class in finder {
            match found_on_class {
                FoundOnClass::Attribute(inf) => {
                    let dunder_next = "__next__";
                    return IteratorContent::Inferred(
                        inf.execute(i_s, &infos.as_no_args())
                            .type_lookup_and_execute(
                                i_s,
                                infos.file(),
                                dunder_next,
                                &infos.as_no_args(),
                                &|t| {
                                    infos.add_issue(IssueKind::AttributeError {
                                        object: t.format_short(i_s.db),
                                        name: dunder_next.into(),
                                    })
                                },
                            ),
                    );
                }
                FoundOnClass::UnresolvedType(t) => return t.iter(i_s, infos),
            }
        }
        if !self.class.incomplete_mro(i_s.db) {
            infos.add_issue(IssueKind::NotIterable {
                type_: format!("{:?}", self.class.format_short(i_s.db)).into(),
            });
        }
        IteratorContent::Any(AnyCause::Todo)
    }

    pub(crate) fn lookup(
        &self,
        i_s: &'a InferenceState,
        name: &str,
        options: InstanceLookupOptions,
    ) -> LookupDetails<'a> {
        let mut attr_kind = AttributeKind::Attribute;
        for (mro_index, class) in self
            .class
            .mro_maybe_without_object(i_s.db, options.without_object)
            .skip(options.super_count)
        {
            let (class_of_lookup, lookup) = class.lookup_symbol(i_s, name);
            // First check class infos
            let result = lookup.and_then(|inf| {
                if let Some(c) = class_of_lookup {
                    if c.node_ref == self.class.node_ref {
                        if let Some(named_tuple) = self.class.maybe_named_tuple_base(i_s.db) {
                            if let Some(param) = named_tuple.search_param(i_s.db, name) {
                                attr_kind = AttributeKind::Property {
                                    writable: false,
                                    is_final: false,
                                    is_abstract: true,
                                };
                                return Some(Inferred::from_type(
                                    param.type_.expect_positional_type_as_ref().clone(),
                                ));
                            }
                        }
                    }
                    let i_s = i_s.with_class_context(&self.class);
                    let instance = if let Some(as_self_instance) = options.as_self_instance {
                        as_self_instance()
                    } else {
                        self.class.as_type(i_s.db)
                    };
                    inf.bind_instance_descriptors(
                        &i_s,
                        name,
                        instance,
                        c,
                        options.add_issue,
                        mro_index,
                        options.disallow_lazy_bound_method
                            || matches!(class, TypeOrClass::Type(Cow::Owned(_))),
                    )
                    .map(|inf| {
                        attr_kind = inf.1;
                        inf.0
                    })
                } else {
                    Some(inf)
                }
            });
            match result {
                Some(LookupResult::None) => (),
                // TODO we should add tests for this. This is currently only None if the self
                // annotation does not match and the node_ref is empty.
                None => {
                    return LookupDetails {
                        class,
                        attr_kind,
                        lookup: LookupResult::None,
                        mro_index: Some(mro_index),
                    }
                }
                Some(lookup) => {
                    return LookupDetails {
                        class,
                        attr_kind,
                        lookup,
                        mro_index: Some(mro_index),
                    }
                }
            }
            if options.kind == LookupKind::Normal && !(options.skip_first_self && mro_index.0 == 0)
            {
                // Then check self attributes
                // This is intentionally done in the same loop. Usually calculating the mro isn't
                // expensive, but in some cases it is. It therefore makes sense to avoid using it
                // twice.
                if let TypeOrClass::Class(c) = class {
                    if let Some(self_symbol) = c.class_storage.self_symbol_table.lookup_symbol(name)
                    {
                        let i_s = i_s.with_class_context(&c);
                        let inference = c.node_ref.file.inference(&i_s);
                        let Ok(inf) = inference.self_lookup_with_flow_analysis(
                            c,
                            self_symbol,
                            options.add_issue,
                        ) else {
                            (options.add_issue)(IssueKind::CannotDetermineType {
                                for_: name.into(),
                            });
                            return LookupDetails::any(AnyCause::FromError);
                        };
                        if inf.maybe_saved_specific(i_s.db)
                            == Some(Specific::AnnotationOrTypeCommentFinal)
                        {
                            attr_kind = AttributeKind::Final
                        }
                        return LookupDetails {
                            class: TypeOrClass::Class(c),
                            attr_kind,
                            lookup: LookupResult::GotoName {
                                name: PointLink::new(c.node_ref.file.file_index, self_symbol),
                                inf: inf.resolve_class_type_vars(&i_s, &self.class, &c),
                            },
                            mro_index: Some(mro_index),
                        };
                    }
                }
            }
        }
        if self.class.use_cached_class_infos(i_s.db).total_ordering
            && ORDERING_METHODS.contains(&name)
            && options.super_count == 0
            && options.check_total_ordering
        {
            return self.fill_total_ordering_method(i_s, name, options);
        }
        if options.kind == LookupKind::Normal && options.check_dunder_getattr {
            for method_name in ["__getattr__", "__getattribute__"] {
                let l = self.lookup_with_details(
                    i_s,
                    options.add_issue,
                    method_name,
                    LookupKind::OnlyType,
                );
                if l.class.is_object(i_s.db) {
                    // object defines a __getattribute__ that returns Any
                    continue;
                }
                if let Some(inf) = l.lookup.into_maybe_inferred() {
                    let lookup = LookupResult::UnknownName(inf.execute(
                        i_s,
                        &KnownArgsWithCustomAddIssue::new(
                            &Inferred::new_any(AnyCause::Internal),
                            &options.add_issue,
                        ),
                    ));
                    return LookupDetails {
                        class: TypeOrClass::Class(self.class),
                        lookup,
                        attr_kind: AttributeKind::Property {
                            writable: {
                                let details = self.lookup_with_details(
                                    i_s,
                                    options.add_issue,
                                    "__setattr__",
                                    LookupKind::OnlyType,
                                );
                                details.lookup.is_some() && !details.class.is_object(i_s.db)
                            },
                            // This is abstract, because this is not an actual property.
                            is_abstract: true,
                            is_final: false,
                        },
                        mro_index: None,
                    };
                }
            }
        }
        if self.class.incomplete_mro(i_s.db) {
            LookupDetails {
                class: TypeOrClass::Class(self.class),
                lookup: LookupResult::any(AnyCause::Todo),
                attr_kind,
                mro_index: None,
            }
        } else {
            LookupDetails {
                class: TypeOrClass::Class(self.class),
                lookup: LookupResult::None,
                attr_kind,
                mro_index: None,
            }
        }
    }

    pub fn fill_total_ordering_method(
        &self,
        i_s: &'a InferenceState,
        name: &str,
        options: InstanceLookupOptions,
    ) -> LookupDetails<'a> {
        for n in ORDERING_METHODS {
            if n == name {
                continue;
            }
            // TODO while this is working, the name of the function is obviously not correct.
            let result = self.lookup(i_s, n, options.without_total_ordering_lookup());
            if result.lookup.is_some() {
                return result;
            }
        }
        unreachable!("total ordering should not be enabled without corresponding methods")
    }

    pub(crate) fn lookup_with_details(
        &self,
        i_s: &'a InferenceState,
        add_issue: impl Fn(IssueKind),
        name: &str,
        kind: LookupKind,
    ) -> LookupDetails<'a> {
        self.lookup(
            i_s,
            name,
            InstanceLookupOptions::new(&add_issue).with_kind(kind),
        )
    }

    pub(crate) fn lookup_on_self(
        &self,
        i_s: &'a InferenceState,
        add_issue: &dyn Fn(IssueKind),
        name: &str,
        kind: LookupKind,
    ) -> LookupDetails<'a> {
        self.lookup(
            i_s,
            name,
            InstanceLookupOptions::new(add_issue)
                .with_kind(kind)
                .with_as_self_instance(&|| Type::Self_),
        )
    }

    pub(crate) fn type_lookup(
        &self,
        i_s: &InferenceState,
        add_issue: impl Fn(IssueKind),
        name: &str,
    ) -> LookupResult {
        self.lookup_with_details(i_s, add_issue, name, LookupKind::OnlyType)
            .lookup
    }

    pub fn run_on_symbols(&self, mut callable: impl FnMut(&str)) {
        for table in [
            &self.class.class_storage.class_symbol_table,
            &self.class.class_storage.self_symbol_table,
        ] {
            for (name, _) in table.iter() {
                callable(name)
            }
        }
    }
    pub(crate) fn get_item(
        &self,
        i_s: &InferenceState,
        slice_type: &SliceType,
        result_context: &mut ResultContext,
        as_instance: &Type,
        add_issue: &dyn Fn(IssueKind),
    ) -> Inferred {
        if let Some(named_tuple) = self.class.maybe_named_tuple_base(i_s.db) {
            // TODO this doesn't take care of the mro and could not be the first __getitem__
            return named_tuple.get_item(i_s, slice_type, result_context, add_issue);
        }
        let mro_iterator = self.class.mro(i_s.db);
        let finder = ClassMroFinder {
            i_s,
            instance: self,
            mro_iterator,
            add_issue,
            name: "__getitem__",
            as_instance: Some(as_instance),
        };
        for found_on_class in finder {
            match found_on_class {
                FoundOnClass::Attribute(inf) => {
                    let args = slice_type.as_args(*i_s);
                    return inf.execute_with_details(
                        i_s,
                        &args,
                        &mut ResultContext::Unknown,
                        OnTypeError::new(&|i_s, _, _, types| {
                            let strs = types.as_boxed_strs(i_s.db);
                            add_issue(IssueKind::InvalidGetItem {
                                type_: self.class.format_short(i_s.db),
                                actual: strs.got,
                                expected: strs.expected,
                            })
                        }),
                    );
                }
                FoundOnClass::UnresolvedType(t) => {
                    if let Type::Tuple(t) = t.as_ref() {
                        return t.get_item(i_s, slice_type, result_context, add_issue);
                    }
                }
            }
        }
        add_issue(IssueKind::NotIndexable {
            type_: self.class.format_short(i_s.db),
        });
        Inferred::new_any_from_error()
    }
}

fn calculate_descriptor(
    i_s: &InferenceState,
    from: NodeRef,
    set_method: Inferred,
    instance: Inferred,
    value: &Inferred,
) {
    set_method.execute_with_details(
        i_s,
        &CombinedArgs::new(
            &KnownArgs::new(&instance, from),
            &KnownArgs::new(value, from),
        ),
        &mut ResultContext::ExpectUnused,
        OnTypeError::new(&|i_s, error_text, argument, types| {
            if argument.index == 2 {
                let strs = types.as_boxed_strs(i_s.db);
                from.add_issue(
                    i_s,
                    IssueKind::IncompatibleAssignment {
                        got: strs.got,
                        expected: strs.expected,
                    },
                );
            } else {
                on_argument_type_error(i_s, error_text, argument, types)
            }
        }),
    );
}

enum FoundOnClass<'a> {
    Attribute(Inferred),
    UnresolvedType(Cow<'a, Type>),
}

struct ClassMroFinder<'db, 'a, 'd> {
    i_s: &'d InferenceState<'db, 'd>,
    instance: &'d Instance<'d>,
    mro_iterator: MroIterator<'db, 'a>,
    add_issue: &'d dyn Fn(IssueKind),
    name: &'d str,
    as_instance: Option<&'a Type>,
}

impl<'db: 'a, 'a> Iterator for ClassMroFinder<'db, 'a, '_> {
    type Item = FoundOnClass<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        for (mro_index, t) in self.mro_iterator.by_ref() {
            match t {
                TypeOrClass::Class(class) => {
                    let result = class
                        .lookup_symbol(self.i_s, self.name)
                        .and_then(|inf| {
                            inf.bind_instance_descriptors(
                                self.i_s,
                                self.name,
                                self.as_instance
                                    .cloned()
                                    .unwrap_or_else(|| self.instance.class.as_type(self.i_s.db)),
                                class,
                                |issue| (self.add_issue)(issue),
                                mro_index,
                                false,
                            )
                            .map(|inf| inf.0)
                        })
                        .and_then(|lookup_result| lookup_result.into_maybe_inferred());
                    if let Some(result) = result {
                        return Some(FoundOnClass::Attribute(result));
                    }
                }
                TypeOrClass::Type(t) => {
                    // Types are always precalculated in the class mro.
                    return Some(FoundOnClass::UnresolvedType(t));
                }
            }
        }
        None
    }
}

pub(crate) fn execute_super<'db>(i_s: &InferenceState<'db, '_>, args: &dyn Args<'db>) -> Inferred {
    match execute_super_internal(i_s, args) {
        Ok(inf) => inf,
        Err(issue) => {
            args.add_issue(i_s, issue);
            Inferred::new_any_from_error()
        }
    }
}

fn execute_super_internal<'db>(
    i_s: &InferenceState<'db, '_>,
    args: &dyn Args<'db>,
) -> Result<Inferred, IssueKind> {
    let mut iterator = args.iter(i_s.mode);
    let mut next_arg = || {
        iterator.next().map(|arg| match arg.is_keyword_argument() {
            false => match arg.in_args_or_kwargs_and_arbitrary_len() {
                false => match arg.infer(&mut ResultContext::Unknown) {
                    InferredArg::Inferred(inf) => Ok(inf),
                    _ => Err(IssueKind::SuperOnlyAcceptsPositionalArguments),
                },
                true => Err(IssueKind::SuperVarargsNotSupported),
            },
            true => Err(IssueKind::SuperOnlyAcceptsPositionalArguments),
        })
    };
    let success = |c: &Class, t, mro_index| {
        if c.incomplete_mro(i_s.db) {
            debug!("super() with incomplete base class leads to any");
            return Ok(Inferred::new_any(AnyCause::Todo));
        }
        Ok(Inferred::from_type(Type::Super {
            class: Rc::new(c.as_generic_class(i_s.db)),
            bound_to: Rc::new(t),
            mro_index,
        }))
    };
    let fallback = |assume_instance| {
        if let Some(func) = i_s.current_function() {
            if let Some(cls) = func.class {
                let first_param_kind = func.first_param_kind();
                if first_param_kind == FirstParamKind::InStaticmethod {
                    return Err(
                        IssueKind::SuperRequiresOneOrTwoPositionalArgumentsInEnclosingFunction,
                    );
                }
                let Some(first_param) = func.iter_params().next() else {
                    return Err(
                        IssueKind::SuperRequiresOneOrTwoPositionalArgumentsInEnclosingFunction,
                    );
                };
                let t = if let Some(first_annotation) = first_param.annotation(i_s.db) {
                    first_annotation.into_owned()
                } else {
                    match first_param_kind {
                        FirstParamKind::Self_ => Type::Self_,
                        FirstParamKind::ClassOfSelf if assume_instance => Type::Self_,
                        FirstParamKind::ClassOfSelf => Type::Type(Rc::new(Type::Self_)),
                        FirstParamKind::InStaticmethod => unreachable!(),
                    }
                };
                success(&cls, t, 1)
            } else {
                Err(IssueKind::SuperUsedOutsideClass)
            }
        } else if i_s.in_class_scope().is_some() {
            Err(IssueKind::SuperOutsideOfAMethod)
        } else {
            Err(IssueKind::SuperUsedOutsideClass)
        }
    };
    let first_class = match next_arg() {
        Some(result) => {
            match get_relevant_type_for_super(i_s.db, result?.as_cow_type(i_s).as_ref()) {
                Type::Type(t) => Some(match t.as_ref() {
                    Type::Self_ => i_s.current_class().unwrap().node_ref.as_link(),
                    Type::Class(c) => {
                        if c.link == i_s.db.python_state.object_node_ref().as_link() {
                            return Err(IssueKind::SuperTargetClassHasNoBaseClass);
                        }
                        c.link
                    }
                    Type::Dataclass(d) => d.class.link,
                    _ => return Err(IssueKind::SuperUnsupportedArgument { argument_index: 1 }),
                }),
                Type::Any(_) => None,
                t => {
                    return Err(IssueKind::SuperArgument1MustBeTypeObject {
                        got: match t {
                            Type::Self_
                            | Type::Class(_)
                            | Type::Dataclass(_)
                            | Type::NamedTuple(_) => "a non-type instance".into(),
                            _ => format!("\"{}\"", t.format_short(i_s.db)).into(),
                        },
                    })
                }
            }
        }
        None => {
            // This is the branch where we use super(), which is very much supported while in a
            // method.
            return fallback(false);
        }
    };
    let instance = match next_arg() {
        Some(result) => result?,
        None => return Err(IssueKind::SuperWithSingleArgumentNotSupported),
    };
    if iterator.next().is_some() {
        return Err(IssueKind::TooManyArguments(" for \"super\"".into()));
    }

    let mut relevant = instance.as_cow_type(i_s);
    if let Type::Literal(l) = relevant.as_ref() {
        relevant = Cow::Owned(l.fallback_type(i_s.db));
    };
    let (cls, bound_to) = match relevant.as_ref() {
        Type::Self_ => {
            let cls = i_s.current_class().unwrap();
            (cls, Type::Self_)
        }
        t @ Type::Class(c) => (c.class(i_s.db), t.clone()),
        t @ Type::TypeVar(_) => {
            let Some(cls) = i_s.current_class() else {
                return Err(IssueKind::SuperUnsupportedArgument { argument_index: 2 });
            };
            (cls, t.clone())
        }
        Type::Any(cause) => {
            return match fallback(true) {
                ok @ Ok(_) => ok,
                Err(_) => Ok(Inferred::new_any(*cause)),
            }
        }
        full @ Type::Type(t) => match t.as_ref() {
            Type::Self_ => {
                let cls = i_s.current_class().unwrap();
                (cls, full.clone())
            }
            Type::Class(c) => (c.class(i_s.db), full.clone()),
            Type::TypeVar(_) => {
                let Some(cls) = i_s.current_class() else {
                    return Err(IssueKind::SuperUnsupportedArgument { argument_index: 2 });
                };
                (cls, full.clone())
            }
            Type::Any(cause) => {
                let Some(cls) = i_s.current_class() else {
                    return Ok(Inferred::new_any(*cause));
                };
                (cls, Type::Type(Rc::new(Type::Self_)))
            }
            _ => return Err(IssueKind::SuperUnsupportedArgument { argument_index: 2 }),
        },
        _ => return Err(IssueKind::SuperUnsupportedArgument { argument_index: 2 }),
    };
    let mro_index = if let Some(first_class) = first_class {
        let mut mro_index = None;
        for (index, type_or_class) in cls.mro(i_s.db) {
            let found_link = match type_or_class {
                TypeOrClass::Class(c) => c.node_ref.as_link(),
                TypeOrClass::Type(t) => match t.as_ref() {
                    Type::Dataclass(d) => d.class.link,
                    _ => unreachable!(),
                },
            };
            if first_class == found_link {
                mro_index = Some(index);
                break;
            }
        }
        let Some(mro_index) = mro_index else {
            return Err(IssueKind::SuperArgument2MustBeAnInstanceOfArgument1);
        };
        // The found class is not the class where super is working on.
        mro_index.0 as usize + 1
    } else {
        1
    };
    success(&cls, bound_to, mro_index)
}

pub(crate) fn execute_isinstance<'db>(
    i_s: &InferenceState<'db, '_>,
    args: &dyn Args<'db>,
) -> Inferred {
    execute_isinstance_or_issubclass(i_s, args, false)
}

pub(crate) fn execute_issubclass<'db>(
    i_s: &InferenceState<'db, '_>,
    args: &dyn Args<'db>,
) -> Inferred {
    execute_isinstance_or_issubclass(i_s, args, true)
}

fn execute_isinstance_or_issubclass<'db>(
    i_s: &InferenceState<'db, '_>,
    args: &dyn Args<'db>,
    issubclass: bool,
) -> Inferred {
    if let Some((_, node_ref2)) = args.maybe_two_positional_args(i_s) {
        if node_ref2
            .file
            .inference(i_s)
            .check_isinstance_or_issubclass_type(node_ref2.as_named_expression(), issubclass)
            .is_some()
        {
            return Inferred::from_type(i_s.db.python_state.bool_type());
        }
    };
    let original_func_ref = match issubclass {
        false => i_s.db.python_state.isinstance_node_ref(),
        true => i_s.db.python_state.issubclass_node_ref(),
    };
    Function::new(original_func_ref, None).ensure_cached_func(i_s);
    Inferred::from_saved_node_ref(original_func_ref).execute(i_s, args)
}

fn get_relevant_type_for_super(db: &Database, t: &Type) -> Type {
    if let Type::Literal(l) = t {
        return l.fallback_type(db);
    }
    let Type::TypeVar(usage) = t else {
        return t.clone();
    };
    if let TypeVarKind::Bound(bound) = &usage.type_var.kind {
        return get_relevant_type_for_super(db, bound);
    }
    t.clone()
}

#[derive(Clone)]
pub struct LookupDetails<'a> {
    pub class: TypeOrClass<'a>,
    pub lookup: LookupResult,
    pub attr_kind: AttributeKind,
    pub mro_index: Option<MroIndex>,
}

impl LookupDetails<'_> {
    pub fn any(cause: AnyCause) -> Self {
        Self {
            class: TypeOrClass::Type(Cow::Owned(Type::Any(cause))),
            lookup: LookupResult::any(cause),
            attr_kind: AttributeKind::Attribute,
            mro_index: None,
        }
    }

    pub fn new(type_: Type, lookup: LookupResult, attr_kind: AttributeKind) -> Self {
        Self {
            class: TypeOrClass::Type(Cow::Owned(type_)),
            lookup,
            attr_kind,
            mro_index: None,
        }
    }

    pub fn none() -> Self {
        Self::new(
            Type::Any(AnyCause::Internal),
            LookupResult::None,
            AttributeKind::Attribute,
        )
    }

    pub fn or_else(self, c: impl FnOnce() -> Self) -> Self {
        match self.lookup {
            LookupResult::None => c(),
            _ => self,
        }
    }

    pub fn is_final(&self, db: &Database) -> bool {
        if self.attr_kind == AttributeKind::Final {
            return true;
        }
        self.lookup.maybe_inferred().is_some_and(|inf| {
            matches!(
                inf.maybe_complex_point(db),
                Some(ComplexPoint::IndirectFinal(_))
            )
        })
    }
}

#[derive(Copy, Clone)]
pub struct InstanceLookupOptions<'x> {
    add_issue: &'x dyn Fn(IssueKind),
    kind: LookupKind,
    super_count: usize,
    skip_first_self: bool,
    as_self_instance: Option<&'x dyn Fn() -> Type>,
    check_dunder_getattr: bool,
    disallow_lazy_bound_method: bool,
    without_object: bool,
    check_total_ordering: bool,
}

impl<'x> InstanceLookupOptions<'x> {
    pub(crate) fn new(add_issue: &'x dyn Fn(IssueKind)) -> Self {
        Self {
            add_issue,
            kind: LookupKind::Normal,
            super_count: 0,
            skip_first_self: false,
            as_self_instance: None,
            check_dunder_getattr: true,
            disallow_lazy_bound_method: false,
            without_object: false,
            check_total_ordering: true,
        }
    }

    pub fn with_super_count(mut self, super_count: usize) -> Self {
        self.super_count = super_count;
        // It feels like this is never wanted.
        self.check_dunder_getattr = false;
        self
    }

    pub fn with_skip_first_of_mro(self, db: &Database, cls: &Class) -> Self {
        let class_infos = cls.use_cached_class_infos(db);
        let tuple_or_named_tuple = class_infos
            .mro
            .first()
            .is_some_and(|t| matches!(&t.type_, Type::Tuple(_) | Type::NamedTuple(_)));
        self.with_super_count(1 + tuple_or_named_tuple as usize)
    }

    pub fn with_skip_first_self_variables(mut self) -> Self {
        self.skip_first_self = true;
        // It feels like this is never wanted.
        self.check_dunder_getattr = false;
        self
    }

    pub fn with_no_check_dunder_getattr(mut self) -> Self {
        self.check_dunder_getattr = false;
        self
    }

    pub fn with_as_self_instance(mut self, as_self_instance: &'x dyn Fn() -> Type) -> Self {
        self.as_self_instance = Some(as_self_instance);
        self
    }

    pub fn with_kind(mut self, kind: LookupKind) -> Self {
        self.kind = kind;
        self
    }

    pub fn with_disallowed_lazy_bound_method(mut self) -> Self {
        self.disallow_lazy_bound_method = true;
        self
    }

    pub fn without_object(mut self) -> Self {
        self.without_object = true;
        self
    }

    pub fn without_total_ordering_lookup(mut self) -> Self {
        self.check_total_ordering = false;
        self
    }
}
