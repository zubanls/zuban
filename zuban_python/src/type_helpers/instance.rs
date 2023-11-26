use std::borrow::Cow;
use std::rc::Rc;

use parsa_python_ast::{AtomContent, DictElement, Expression, Name, StarLikeExpression};

use super::class::TypeOrClass;
use super::{Class, MroIterator};
use crate::arguments::{Arguments, CombinedArguments, KnownArguments, NoArguments};
use crate::database::{Database, PointLink, Specific};
use crate::debug;
use crate::diagnostics::IssueType;
use crate::file::{on_argument_type_error, File};
use crate::getitem::SliceType;
use crate::inference_state::InferenceState;
use crate::inferred::{add_attribute_error, Inferred};
use crate::matching::{
    FormatData, IteratorContent, LookupKind, LookupResult, OnTypeError, ResultContext,
};
use crate::node_ref::NodeRef;
use crate::type_::{
    AnyCause, CallableLike, FormatStyle, FunctionKind, GenericClass, Type, TypeVarKind,
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

    pub fn check_set_descriptor(
        &self,
        i_s: &InferenceState,
        from: NodeRef,
        name: Name,
        value: &Inferred,
    ) {
        let name_str = name.as_str();
        let property_is_read_only = |class_name| {
            from.add_issue(
                i_s,
                IssueType::PropertyIsReadOnly {
                    class_name,
                    property_name: name_str.into(),
                },
            );
        };
        let cached_class_infos = self.class.use_cached_class_infos(i_s.db);
        if let Some(nt) = cached_class_infos.maybe_named_tuple() {
            if nt.search_param(i_s.db, name_str).is_some() {
                property_is_read_only(nt.name(i_s.db).into());
                return;
            }
        }
        let check_compatible = |t: &Type, value: &_| {
            self.check_slots(i_s, from, name_str);
            t.error_if_not_matches(i_s, value, |got, expected| {
                from.add_issue(i_s, IssueType::IncompatibleAssignment { got, expected });
                from.to_db_lifetime(i_s.db)
            });
        };

        let (result, class) = self.class.lookup_without_descriptors(i_s, from, name_str);
        let result = result.or_else(|| self.lookup(i_s, from, name_str, LookupKind::Normal));
        let Some(inf) = result.into_maybe_inferred() else {
            let t = self.class.as_type(i_s.db);
            let (defined_in, lookup) = self.lookup_and_defined_in(i_s, from, "__setattr__", LookupKind::OnlyType);
            if let Some(setattr) = lookup.into_maybe_inferred() {
                // object defines a __getattribute__ that returns Any
                if !defined_in.is_object(i_s.db) {
                    // If it's not a callable with the correct signature, diagnostics will be raised
                    // elsewhere.
                    match setattr.as_cow_type(i_s).maybe_callable(i_s) {
                        Some(CallableLike::Callable(c)) => {
                            if let Some(second) = c.second_positional_type() {
                                check_compatible(&second, value);
                                return;
                            }
                        }
                        Some(CallableLike::Overload(_)) => todo!(),
                        None => (),
                    };
                }
            }
            add_attribute_error(
                i_s,
                from,
                &t,
                &t,
                name_str,
            );
            return
        };
        if inf.maybe_saved_specific(i_s.db) == Some(Specific::AnnotationOrTypeCommentClassVar) {
            from.add_issue(
                i_s,
                IssueType::CannotAssignToClassVarViaInstance {
                    name: name_str.into(),
                },
            );
        }

        for t in inf.as_cow_type(i_s).iter_with_unpacked_unions() {
            match t {
                Type::Class(c) => {
                    let descriptor = c.class(i_s.db);
                    if let Some(__set__) = Instance::new(descriptor, None)
                        .type_lookup(i_s, from, "__set__")
                        .into_maybe_inferred()
                    {
                        let inst = self.as_inferred(i_s);
                        calculate_descriptor(i_s, from, __set__, inst, value);
                        continue;
                    } else if let Some(inf) = Instance::new(descriptor, None).bind_dunder_get(
                        i_s,
                        from,
                        self.class.as_type(i_s.db),
                    ) {
                        // It feels weird that a descriptor that only defines __get__ should
                        // match the value with __get__'s return type. But this makes sense:
                        // When a descriptor does not define __set__, writing Foo().bar = 3 will
                        // write Foo.__dict__['bar'] = true instead of changing anything on
                        // the class attribute Foo.bar.
                        // Here we ensure that the contract that the __get__ descriptor gives us is
                        // not violated.
                        check_compatible(&inf.as_cow_type(i_s), value);
                        continue;
                    }
                }
                Type::Callable(c) if matches!(c.kind, FunctionKind::Property { .. }) => {
                    match c.kind {
                        FunctionKind::Property {
                            writable: false, ..
                        } => {
                            if let Some(class) = class {
                                property_is_read_only(class.name().into())
                            } else {
                                todo!()
                            }
                        }
                        FunctionKind::Property { writable: true, .. } => {
                            check_compatible(&c.return_type, value);
                        }
                        _ => unreachable!(),
                    }
                    continue;
                }
                _ => {}
            }

            check_compatible(t, value)
        }
    }

    pub fn check_slots(&self, i_s: &InferenceState, from: NodeRef, name: &str) {
        let storage = &self.class.class_storage;
        let Some(slots_atom_index) = storage.slots_atom_index else {
            return
        };
        if is_in_slots(
            NodeRef::new(self.class.node_ref.file, slots_atom_index),
            name,
        ) {
            return;
        }
        from.add_issue(
            i_s,
            IssueType::AssigningToNameOutsideOfSlots {
                name: name.into(),
                class: self
                    .class
                    .format(&FormatData::with_style(i_s.db, FormatStyle::Qualified)),
            },
        )
    }

    pub fn bind_dunder_get(
        &self,
        i_s: &InferenceState,
        from: NodeRef,
        instance: Type,
    ) -> Option<Inferred> {
        self.type_lookup(i_s, from, "__get__")
            .into_maybe_inferred()
            .map(|inf| {
                let c_t = Type::Type(Rc::new(instance.clone()));
                inf.execute(
                    i_s,
                    &CombinedArguments::new(
                        &KnownArguments::new(&Inferred::from_type(instance), from),
                        &KnownArguments::new(&Inferred::from_type(c_t), from),
                    ),
                )
            })
    }

    pub fn execute<'db>(
        &self,
        i_s: &InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
        result_context: &mut ResultContext,
        on_type_error: OnTypeError<'db, '_>,
    ) -> Inferred {
        let node_ref = args.as_node_ref();
        if let Some(inf) = self
            .type_lookup(i_s, node_ref, "__call__")
            .into_maybe_inferred()
        {
            inf.execute_with_details(i_s, args, result_context, on_type_error)
        } else {
            let t = self.class.format_short(i_s.db);
            node_ref.add_issue(
                i_s,
                if self.class.node_ref == i_s.db.python_state.function_node_ref() {
                    IssueType::UnknownFunctionNotCallable
                } else {
                    IssueType::NotCallable {
                        type_: format!("{:?}", t).into(),
                    }
                },
            );
            Inferred::new_any_from_error()
        }
    }

    pub fn iter(&self, i_s: &InferenceState, from: NodeRef) -> IteratorContent {
        if let Some(tup) = self.class.use_cached_class_infos(i_s.db).maybe_tuple() {
            // TODO this doesn't take care of the mro and could not be the first __iter__
            return tup.iter(i_s, from);
        }
        let mro_iterator = self.class.mro(i_s.db);
        let finder = ClassMroFinder {
            i_s,
            instance: self,
            mro_iterator,
            from,
            name: "__iter__",
        };
        for found_on_class in finder {
            match found_on_class {
                FoundOnClass::Attribute(inf) => {
                    return IteratorContent::Inferred(
                        inf.execute(i_s, &NoArguments::new(from))
                            .type_lookup_and_execute(
                                i_s,
                                from,
                                "__next__",
                                &NoArguments::new(from),
                                &|_| todo!(),
                            ),
                    );
                }
                FoundOnClass::UnresolvedType(t) => {
                    if let Type::Tuple(tup) = t.as_ref() {
                        return tup.iter(i_s, from);
                    } else {
                        todo!();
                    }
                }
            }
        }
        if !self.class.incomplete_mro(i_s.db) {
            from.add_issue(
                i_s,
                IssueType::NotIterable {
                    type_: format!("{:?}", self.class.format_short(i_s.db)).into(),
                },
            );
        }
        IteratorContent::Any(AnyCause::Todo)
    }

    pub fn lookup_with_explicit_self_binding(
        &self,
        i_s: &'a InferenceState,
        node_ref: NodeRef,
        name: &str,
        kind: LookupKind,
        super_count: usize,
        as_self_instance: impl Fn() -> Type,
    ) -> (TypeOrClass, LookupResult) {
        for (mro_index, class) in self.class.mro(i_s.db).skip(super_count) {
            let (class_of_lookup, lookup) = class.lookup_symbol(i_s, name);
            // First check class infos
            let result = lookup.and_then(|inf| {
                if let Some(c) = class_of_lookup {
                    let i_s = i_s.with_class_context(&self.class);
                    inf.bind_instance_descriptors(&i_s, as_self_instance(), c, node_ref, mro_index)
                } else {
                    Some(inf)
                }
            });
            match result {
                Some(LookupResult::None) => (),
                // TODO we should add tests for this. This is currently only None if the self
                // annotation does not match and the node_ref is empty.
                None => return (class, LookupResult::None),
                Some(x) => return (class, x),
            }
            if kind == LookupKind::Normal {
                // Then check self attributes
                if let TypeOrClass::Class(c) = class {
                    if let Some(self_symbol) = c.class_storage.self_symbol_table.lookup_symbol(name)
                    {
                        let i_s = i_s.with_class_context(&c);
                        return (
                            class,
                            LookupResult::GotoName {
                                name: PointLink::new(c.node_ref.file.file_index(), self_symbol),
                                inf: c
                                    .node_ref
                                    .file
                                    .inference(&i_s)
                                    .infer_name_by_index(self_symbol)
                                    .resolve_class_type_vars(&i_s, &self.class, &c),
                            },
                        );
                    }
                }
            }
        }
        if kind == LookupKind::Normal && super_count == 0 {
            for method_name in ["__getattr__", "__getattribute__"] {
                let (defined_in, lookup) =
                    self.lookup_and_defined_in(i_s, node_ref, method_name, LookupKind::OnlyType);
                if defined_in.is_object(i_s.db) {
                    // object defines a __getattribute__ that returns Any
                    continue;
                }
                if let Some(inf) = lookup.into_maybe_inferred() {
                    let result = LookupResult::UnknownName(inf.execute(
                        i_s,
                        &KnownArguments::new(&Inferred::new_any(AnyCause::Internal), node_ref),
                    ));
                    return (TypeOrClass::Class(self.class), result);
                }
            }
        }
        if self.class.incomplete_mro(i_s.db) {
            (
                TypeOrClass::Class(self.class),
                LookupResult::any(AnyCause::Todo),
            )
        } else {
            (TypeOrClass::Class(self.class), LookupResult::None)
        }
    }

    pub fn lookup_and_maybe_ignore_super_count(
        &self,
        i_s: &'a InferenceState,
        node_ref: NodeRef,
        name: &str,
        kind: LookupKind,
        super_count: usize,
    ) -> (TypeOrClass, LookupResult) {
        self.lookup_with_explicit_self_binding(i_s, node_ref, name, kind, super_count, || {
            self.class.as_type(i_s.db)
        })
    }

    pub fn lookup(
        &self,
        i_s: &InferenceState,
        node_ref: NodeRef,
        name: &str,
        kind: LookupKind,
    ) -> LookupResult {
        self.lookup_and_defined_in(i_s, node_ref, name, kind).1
    }

    pub fn lookup_and_defined_in(
        &self,
        i_s: &'a InferenceState,
        node_ref: NodeRef,
        name: &str,
        kind: LookupKind,
    ) -> (TypeOrClass, LookupResult) {
        self.lookup_and_maybe_ignore_super_count(i_s, node_ref, name, kind, 0)
    }

    pub fn lookup_on_self(
        &self,
        i_s: &'a InferenceState,
        node_ref: NodeRef,
        name: &str,
        kind: LookupKind,
    ) -> (TypeOrClass, LookupResult) {
        self.lookup_with_explicit_self_binding(i_s, node_ref, name, kind, 0, || Type::Self_)
    }

    pub fn full_lookup(&self, i_s: &InferenceState, node_ref: NodeRef, name: &str) -> LookupResult {
        self.lookup(i_s, node_ref, name, LookupKind::Normal)
    }

    pub fn type_lookup(&self, i_s: &InferenceState, node_ref: NodeRef, name: &str) -> LookupResult {
        self.lookup(i_s, node_ref, name, LookupKind::OnlyType)
    }

    pub fn run_on_symbols(&self, mut callable: impl FnMut(&str)) {
        for table in [
            &self.class.class_storage.class_symbol_table,
            &self.class.class_storage.self_symbol_table,
        ] {
            for (name, _) in unsafe { table.iter_on_finished_table() } {
                callable(name)
            }
        }
    }
    pub fn get_item(
        &self,
        i_s: &InferenceState,
        slice_type: &SliceType,
        result_context: &mut ResultContext,
    ) -> Inferred {
        if let Some(named_tuple) = self
            .class
            .use_cached_class_infos(i_s.db)
            .maybe_named_tuple()
        {
            // TODO this doesn't take care of the mro and could not be the first __getitem__
            return named_tuple.get_item(i_s, slice_type, result_context);
        }
        let mro_iterator = self.class.mro(i_s.db);
        let from = slice_type.as_node_ref();
        let finder = ClassMroFinder {
            i_s,
            instance: self,
            mro_iterator,
            from,
            name: "__getitem__",
        };
        for found_on_class in finder {
            match found_on_class {
                FoundOnClass::Attribute(inf) => {
                    let args = slice_type.as_args(*i_s);
                    return inf.execute_with_details(
                        i_s,
                        &args,
                        &mut ResultContext::Unknown,
                        OnTypeError::new(&|i_s, function, arg, actual, expected| {
                            arg.as_node_ref().add_issue(
                                i_s,
                                IssueType::InvalidGetItem {
                                    actual,
                                    type_: self.class.format_short(i_s.db),
                                    expected,
                                },
                            )
                        }),
                    );
                }
                FoundOnClass::UnresolvedType(t) => match t.as_ref() {
                    Type::Tuple(t) => {
                        return t.get_item(i_s, slice_type, result_context);
                    }
                    _ => (),
                },
            }
        }
        from.add_issue(
            i_s,
            IssueType::NotIndexable {
                type_: self.class.format_short(i_s.db),
            },
        );
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
        &CombinedArguments::new(
            &KnownArguments::new(&instance, from),
            &KnownArguments::new(value, from),
        ),
        &mut ResultContext::ExpectUnused,
        OnTypeError::new(&|i_s, error_text, argument, got, expected| {
            if argument.index == 2 {
                from.add_issue(i_s, IssueType::IncompatibleAssignment { got, expected });
            } else {
                on_argument_type_error(i_s, error_text, argument, got, expected)
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
    from: NodeRef<'d>,
    name: &'d str,
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
                                self.instance.class.as_type(self.i_s.db),
                                class,
                                self.from,
                                mro_index,
                            )
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

pub fn execute_super<'db>(i_s: &InferenceState<'db, '_>, args: &dyn Arguments<'db>) -> Inferred {
    match execute_super_internal(i_s, args) {
        Ok(inf) => inf,
        Err(issue) => {
            args.as_node_ref().add_issue(i_s, issue);
            Inferred::new_any_from_error()
        }
    }
}

fn execute_super_internal<'db>(
    i_s: &InferenceState<'db, '_>,
    args: &dyn Arguments<'db>,
) -> Result<Inferred, IssueType> {
    let mut iterator = args.iter();
    let mut next_arg = || {
        iterator.next().map(|arg| match arg.is_keyword_argument() {
            false => match arg.in_args_or_kwargs_and_arbitrary_len() {
                false => Ok(arg.infer(i_s, &mut ResultContext::Unknown)),
                true => Err(IssueType::SuperVarargsNotSupported),
            },
            true => Err(IssueType::SuperOnlyAcceptsPositionalArguments),
        })
    };
    let success = |c: GenericClass, mro_index| {
        if c.class(i_s.db).incomplete_mro(i_s.db) {
            debug!("super() with incomplete base class leads to any");
            return Ok(Inferred::new_any(AnyCause::Todo));
        }
        Ok(Inferred::from_type(Type::Super {
            class: Rc::new(c),
            mro_index,
        }))
    };
    let first_type = match next_arg() {
        Some(result) => {
            match get_relevant_type_for_super(i_s.db, result?.as_cow_type(i_s).as_ref()) {
                Type::Type(t) => {
                    if !matches!(t.as_ref(), Type::Class(..)) {
                        return Err(IssueType::SuperUnsupportedArgument { argument_index: 1 });
                    }
                    if matches!(t.as_ref(), Type::Class(c)
                            if c.link == i_s.db.python_state.object_node_ref().as_link())
                    {
                        return Err(IssueType::SuperTargetClassHasNoBaseClass);
                    }
                    t.as_ref().clone()
                }
                Type::Any(cause) => Type::Any(cause),
                _ => return Err(IssueType::SuperArgument1MustBeTypeObject),
            }
        }
        None => {
            // This is the branch where we use super(), which is very much supported while in a
            // method.
            if let Some(cls) = i_s.current_class() {
                return success(cls.as_generic_class(i_s.db), 0);
            } else {
                return Err(IssueType::SuperUsedOutsideClass);
            }
        }
    };
    let instance = match next_arg() {
        Some(result) => result?,
        None => return Err(IssueType::SuperWithSingleArgumentNotSupported),
    };
    let cls = match get_relevant_type_for_super(i_s.db, &instance.as_cow_type(i_s)) {
        Type::Self_ => i_s.current_class().unwrap().as_generic_class(i_s.db),
        Type::Class(g) => g,
        Type::Any(cause) => return Ok(Inferred::new_any(cause)),
        _ => return Err(IssueType::SuperUnsupportedArgument { argument_index: 2 }),
    };
    if !first_type
        .is_simple_super_type_of(i_s, &instance.as_cow_type(i_s))
        .bool()
    {
        return Err(IssueType::SuperArgument2MustBeAnInstanceOfArgument1);
    }
    if iterator.next().is_some() {
        return Err(IssueType::TooManyArguments(" for \"super\"".into()));
    }
    success(cls, 0)
}

fn get_relevant_type_for_super(db: &Database, t: &Type) -> Type {
    if let Type::Literal(l) = t {
        return db.python_state.literal_type(&l.kind);
    }
    let Type::TypeVar(usage) = t else {
        return t.clone()
    };
    if let TypeVarKind::Bound(bound) = &usage.type_var.kind {
        return get_relevant_type_for_super(db, bound);
    }
    t.clone()
}

fn is_in_slots(slots_atom_node_ref: NodeRef, name: &str) -> bool {
    let check_expr = |expr: Expression| {
        let Some(s) = expr.maybe_single_string_literal() else {
            return true
        };
        let string = s.as_python_string();
        let Some(s) = string.as_str() else  {
            return true;
        };
        if s == name {
            return true;
        }
        false
    };
    match slots_atom_node_ref.expect_atom().unpack() {
        AtomContent::Dict(dict) => {
            for dict_element in dict.iter_elements() {
                match dict_element {
                    DictElement::KeyValue(key_value) => {
                        if check_expr(key_value.key()) {
                            return true;
                        }
                    }
                    DictElement::Star(_) => return true,
                }
            }
            false
        }
        AtomContent::Set(set) => {
            for element in set.unpack() {
                let result = match element {
                    StarLikeExpression::Expression(expr) => check_expr(expr),
                    StarLikeExpression::NamedExpression(n) => check_expr(n.expression()),
                    StarLikeExpression::StarNamedExpression(_)
                    | StarLikeExpression::StarExpression(_) => todo!(),
                };
                if result {
                    return true;
                }
            }
            false
        }
        // Invalid __slots__ will be checked elsewhere.
        _ => true,
    }
}
