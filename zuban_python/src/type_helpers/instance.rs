use std::rc::Rc;

use parsa_python_ast::Name;

use super::class::TypeOrClass;
use super::{Class, MroIterator, NamedTupleValue, Tuple};
use crate::arguments::{ArgumentKind, Arguments, CombinedArguments, KnownArguments, NoArguments};
use crate::database::{ClassType, DbType, FunctionKind, GenericClass, PointLink};
use crate::debug;
use crate::diagnostics::IssueType;
use crate::file::{on_argument_type_error, File};
use crate::getitem::SliceType;
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::matching::{IteratorContent, LookupResult, OnTypeError, ResultContext, Type};
use crate::node_ref::NodeRef;

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
            let t = self.class.as_db_type(i_s.db);
            Inferred::from_type(t)
        }
    }

    pub fn checked_set_descriptor(
        &self,
        i_s: &InferenceState,
        from: NodeRef,
        name: Name,
        value: &Inferred,
    ) -> bool {
        let mut had_set = false;
        let mut had_no_set = false;
        for (mro_index, t) in self.class.mro(i_s.db) {
            if let TypeOrClass::Class(class) = t {
                if let Some(inf) = class
                    .lookup_symbol(i_s, name.as_str())
                    .into_maybe_inferred()
                {
                    inf.resolve_class_type_vars(i_s, &self.class, &class)
                        .as_type(i_s)
                        .run_on_each_union_type(&mut |t| {
                            if had_no_set {
                                todo!()
                            }
                            match t.as_ref() {
                                DbType::Class(l, g) => {
                                    let descriptor = Class::from_db_type(i_s.db, *l, g);
                                    if let Some(set) = Instance::new(descriptor, None)
                                        .lookup(i_s, Some(from), "__set__")
                                        .into_maybe_inferred()
                                    {
                                        had_set = true;
                                        let inst = self.as_inferred(i_s);
                                        calculate_descriptor(i_s, from, set, inst, value)
                                    }
                                }
                                DbType::Callable(c)
                                    if matches!(c.kind, FunctionKind::Property { .. }) =>
                                {
                                    if had_no_set || had_set {
                                        unreachable!()
                                    }
                                    match c.kind {
                                        FunctionKind::Property { writable: false } => from
                                            .add_issue(
                                                i_s,
                                                IssueType::PropertyIsReadOnly {
                                                    class_name: class.name().into(),
                                                    property_name: name.as_str().into(),
                                                },
                                            ),
                                        FunctionKind::Property { writable: true } => {}
                                        _ => unreachable!(),
                                    }
                                    had_no_set = true;
                                }
                                _ => {
                                    if had_set {
                                        todo!()
                                    }
                                    had_no_set = true;
                                }
                            }
                        });
                    break;
                }
            }
        }
        had_set
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
            .lookup(i_s, Some(node_ref), "__call__")
            .into_maybe_inferred()
        {
            inf.execute_with_details(i_s, args, result_context, on_type_error)
        } else {
            let t = self.class.format_short(i_s.db);
            node_ref.add_issue(
                i_s,
                IssueType::NotCallable {
                    type_: format!("{:?}", t).into(),
                },
            );
            Inferred::new_unknown()
        }
    }

    pub fn iter(&self, i_s: &InferenceState<'a, '_>, from: NodeRef) -> IteratorContent<'a> {
        if let ClassType::NamedTuple(ref named_tuple) =
            self.class.use_cached_class_infos(i_s.db).class_type
        {
            // TODO this doesn't take care of the mro and could not be the first __iter__
            return NamedTupleValue::new(i_s.db, named_tuple).iter(i_s, from);
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
                            .lookup_and_execute(
                                i_s,
                                from,
                                "__next__",
                                &NoArguments::new(from),
                                &|_| todo!(),
                            ),
                    );
                }
                FoundOnClass::UnresolvedType(t) => {
                    if let Some(DbType::Tuple(tup)) = t.maybe_borrowed_db_type() {
                        return Tuple::new(tup).iter(i_s, from);
                    } else {
                        // Might happen when generics are passed to a tuple
                        todo!("TODO Owned tuples won't work with iter currently");
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
        IteratorContent::Any
    }

    pub fn lookup_and_maybe_ignore_super_count(
        &self,
        i_s: &'a InferenceState,
        node_ref: Option<NodeRef>,
        name: &str,
        super_count: usize,
    ) -> (TypeOrClass, LookupResult) {
        for (mro_index, class) in self.class.mro(i_s.db).skip(super_count) {
            // First check class infos
            let result = class.lookup_symbol(i_s, name).and_then(|inf| {
                if let TypeOrClass::Class(c) = class {
                    let i_s = i_s.with_class_context(&self.class);
                    inf.resolve_class_type_vars(&i_s.with_class_context(&c), &self.class, &c)
                        .bind_instance_descriptors(
                            &i_s,
                            self,
                            c,
                            |i_s| self.as_inferred(i_s),
                            node_ref,
                            mro_index,
                        )
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
            // Then check self attributes
            if let TypeOrClass::Class(c) = class {
                if let Some(self_symbol) = c.class_storage.self_symbol_table.lookup_symbol(name) {
                    let i_s = i_s.with_class_context(&c);
                    return (
                        class,
                        LookupResult::GotoName(
                            PointLink::new(c.node_ref.file.file_index(), self_symbol),
                            c.node_ref
                                .file
                                .inference(&i_s)
                                .infer_name_by_index(self_symbol)
                                .resolve_class_type_vars(&i_s, &self.class, &c),
                        ),
                    );
                }
            }
        }
        if self.class.incomplete_mro(i_s.db) {
            (TypeOrClass::Class(self.class), LookupResult::any())
        } else {
            (TypeOrClass::Class(self.class), LookupResult::None)
        }
    }

    pub fn lookup(
        &self,
        i_s: &InferenceState,
        node_ref: Option<NodeRef>,
        name: &str,
    ) -> LookupResult {
        self.lookup_and_maybe_ignore_super_count(i_s, node_ref, name, 0)
            .1
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
        if let ClassType::NamedTuple(named_tuple) =
            &self.class.use_cached_class_infos(i_s.db).class_type
        {
            // TODO this doesn't take care of the mro and could not be the first __getitem__
            return NamedTupleValue::new(i_s.db, named_tuple).get_item(
                i_s,
                slice_type,
                result_context,
            );
        }
        let mro_iterator = self.class.mro(i_s.db);
        let node_ref = slice_type.as_node_ref();
        let finder = ClassMroFinder {
            i_s,
            instance: self,
            mro_iterator,
            from: slice_type.as_node_ref(),
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
                        OnTypeError::new(&|i_s, class, function, arg, actual, expected| {
                            arg.as_node_ref().add_issue(
                                i_s,
                                IssueType::InvalidGetItem {
                                    actual,
                                    type_: class.unwrap().format_short(i_s.db),
                                    expected,
                                },
                            )
                        }),
                    );
                }
                FoundOnClass::UnresolvedType(t) => match t.as_ref() {
                    DbType::Tuple(t) => {
                        return Tuple::new(t).get_item(i_s, slice_type, result_context);
                    }
                    _ => (),
                },
            }
        }
        node_ref.add_issue(
            i_s,
            IssueType::NotIndexable {
                type_: self.class.format_short(i_s.db),
            },
        );
        Inferred::new_any()
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
        &mut ResultContext::Unknown,
        OnTypeError::new(&|i_s, class, error_text, argument, got, expected| {
            if argument.index == 2 {
                from.add_issue(i_s, IssueType::IncompatibleAssignment { got, expected });
            } else {
                on_argument_type_error(i_s, class, error_text, argument, got, expected)
            }
        }),
    );
}

enum FoundOnClass<'a> {
    Attribute(Inferred),
    UnresolvedType(Type<'a>),
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
                            inf.resolve_class_type_vars(self.i_s, &self.instance.class, &class)
                                .bind_instance_descriptors(
                                    self.i_s,
                                    self.instance,
                                    class,
                                    |i_s| self.instance.as_inferred(i_s),
                                    Some(self.from),
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
            Inferred::new_any()
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
    let first_type = match next_arg() {
        Some(result) => match result?.as_type(i_s).as_ref() {
            DbType::Type(t) => t.as_ref().clone(),
            DbType::Any => DbType::Any,
            _ => return Err(IssueType::SuperArgument1MustBeTypeObject),
        },
        None => {
            // This is the branch where we use super(), which is very much supported while in a
            // method.
            if let Some(cls) = i_s.current_class() {
                return Ok(Inferred::from_type(DbType::Super {
                    class: Rc::new(cls.as_generic_class(i_s.db)),
                    mro_index: 0,
                }));
            } else {
                return Err(IssueType::SuperUsedOutsideClass);
            }
        }
    };
    let instance = match next_arg() {
        Some(result) => result?,
        None => return Err(IssueType::SuperWithSingleArgumentNotSupported),
    };
    if !Type::owned(first_type)
        .is_simple_super_type_of(i_s, &instance.as_type(i_s))
        .bool()
    {
        return Err(IssueType::SuperArgument2MustBeAnInstanceOfArgument1);
    }
    let cls = match instance.as_type(i_s).as_ref() {
        DbType::Self_ => i_s.current_class().unwrap().as_generic_class(i_s.db),
        DbType::Class(link, generics) => GenericClass {
            link: *link,
            generics: generics.clone(),
        },
        DbType::Any => return Ok(Inferred::new_any()),
        _ => return Err(IssueType::SuperUnsupportedArgument2),
    };
    if iterator.next().is_some() {
        return Err(IssueType::TooManyArguments(" for \"super\"".into()));
    }
    Ok(Inferred::from_type(DbType::Super {
        class: Rc::new(cls),
        mro_index: 0,
    }))
}
