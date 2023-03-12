use std::borrow::Cow;

use parsa_python_ast::Name;

use super::{
    Class, IteratorContent, LookupResult, MroIterator, OnTypeError, Tuple, Value, ValueKind,
};
use crate::arguments::{Arguments, CombinedArguments, KnownArguments, NoArguments};
use crate::database::{Database, DbType, PointLink};
use crate::diagnostics::IssueType;
use crate::file::{on_argument_type_error, File};
use crate::getitem::SliceType;
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::matching::{Generics, ResultContext, Type};
use crate::node_ref::NodeRef;

#[derive(Debug, Clone, Copy)]
pub struct Instance<'a> {
    pub class: Class<'a>,
    inferred_link: Option<NodeRef<'a>>,
}

impl<'a> Instance<'a> {
    pub fn new(class: Class<'a>, inferred_link: Option<NodeRef<'a>>) -> Self {
        Self {
            class,
            inferred_link,
        }
    }

    pub fn as_inferred(&self, i_s: &mut InferenceState) -> Inferred {
        if let Some(inferred_link) = self.inferred_link {
            Inferred::from_saved_node_ref(inferred_link)
        } else {
            let t = self.class.as_db_type(i_s.db);
            Inferred::execute_db_type(i_s, t)
        }
    }

    pub fn checked_set_descriptor(
        &self,
        i_s: &mut InferenceState,
        from: NodeRef,
        name: Name,
        value: &Inferred,
    ) -> bool {
        let mut had_set = false;
        let mut had_no_set = false;
        for (mro_index, t) in self.class.mro(i_s.db) {
            if let Some(class) = t.maybe_class(i_s.db) {
                if let Some(inf) = class
                    .lookup_symbol(i_s, name.as_str())
                    .into_maybe_inferred()
                {
                    inf.resolve_class_type_vars(i_s, &self.class).run_mut(
                        i_s,
                        &mut |i_s, v| {
                            if had_no_set {
                                todo!()
                            }
                            if let Some(descriptor) = v.as_instance() {
                                if let Some(set) = descriptor
                                    .lookup_internal(i_s, Some(from), "__set__")
                                    .into_maybe_inferred()
                                {
                                    had_set = true;
                                    let inst = self.as_inferred(i_s);
                                    set.execute_with_details(
                                        i_s,
                                        &CombinedArguments::new(
                                            &KnownArguments::new(&inst, from),
                                            &KnownArguments::new(value, from),
                                        ),
                                        &mut ResultContext::Unknown,
                                        OnTypeError::new(
                                            &|i_s, class, error_text, argument, got, expected| {
                                                if argument.index == 2 {
                                                    from.add_typing_issue(
                                                        i_s.db,
                                                        IssueType::IncompatibleAssignment {
                                                            got,
                                                            expected,
                                                        },
                                                    );
                                                } else {
                                                    on_argument_type_error(
                                                        i_s, class, error_text, argument, got,
                                                        expected,
                                                    )
                                                }
                                            },
                                        ),
                                    );
                                }
                            } else {
                                if had_set {
                                    todo!()
                                }
                                had_no_set = true;
                            }
                        },
                        || (),
                    );
                }
            }
        }
        had_set
    }
}

impl<'db: 'a, 'a> Value<'db, 'a> for Instance<'a> {
    fn kind(&self) -> ValueKind {
        ValueKind::Object
    }

    fn name(&self) -> &str {
        self.class.name()
    }

    fn lookup_internal(
        &self,
        i_s: &mut InferenceState,
        node_ref: Option<NodeRef>,
        name: &str,
    ) -> LookupResult {
        for (mro_index, class) in self.class.mro(i_s.db) {
            // First check class infos
            let result = class.lookup_symbol(i_s, name).and_then(|inf| {
                if let Some(c) = class.maybe_class(i_s.db) {
                    let mut i_s = i_s.with_class_context(&self.class);
                    inf.resolve_class_type_vars(&mut i_s.with_class_context(&c), &self.class)
                        .bind_instance_descriptors(
                            &mut i_s,
                            self,
                            c,
                            |i_s| self.as_inferred(i_s),
                            node_ref,
                            mro_index,
                        )
                } else {
                    todo!()
                }
            });
            match result {
                Some(LookupResult::None) => (),
                // TODO we should add tests for this. This is currently only None if the self
                // annotation does not match and the node_ref is empty.
                None => return LookupResult::None,
                Some(x) => return x,
            }
            // Then check self attributes
            if let Some(c) = class.maybe_class(i_s.db) {
                if let Some(self_symbol) = c.class_storage.self_symbol_table.lookup_symbol(name) {
                    let mut i_s = i_s.with_class_context(&c);
                    return LookupResult::GotoName(
                        PointLink::new(c.node_ref.file.file_index(), self_symbol),
                        c.node_ref
                            .file
                            .inference(&mut i_s)
                            .infer_name_by_index(self_symbol)
                            .resolve_class_type_vars(&mut i_s, &self.class),
                    );
                }
            }
        }
        LookupResult::None
    }

    fn should_add_lookup_error(&self, db: &Database) -> bool {
        !self.class.use_cached_class_infos(db).incomplete_mro
    }

    fn execute(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
        result_context: &mut ResultContext,
        on_type_error: OnTypeError<'db, '_>,
    ) -> Inferred {
        let node_ref = args.as_node_ref();
        if let Some(inf) = self
            .lookup_internal(i_s, Some(node_ref), "__call__")
            .into_maybe_inferred()
        {
            inf.execute_with_details(i_s, args, result_context, on_type_error)
        } else {
            node_ref.add_typing_issue(
                i_s.db,
                IssueType::NotCallable {
                    type_: format!("{:?}", self.name()).into(),
                },
            );
            Inferred::new_unknown()
        }
    }

    fn get_item(
        &self,
        i_s: &mut InferenceState,
        slice_type: &SliceType,
        result_context: &mut ResultContext,
    ) -> Inferred {
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
                    let args = slice_type.as_args(i_s.context);
                    return inf.execute_with_details(
                        i_s,
                        &args,
                        &mut ResultContext::Unknown,
                        OnTypeError::new(&|i_s, class, function, arg, actual, expected| {
                            arg.as_node_ref().add_typing_issue(
                                i_s.db,
                                IssueType::InvalidGetItem {
                                    actual,
                                    type_: class.unwrap().format_short(i_s.db),
                                    expected,
                                },
                            )
                        }),
                    );
                }
                FoundOnClass::UnresolvedDbType(db_type @ DbType::Tuple(t)) => {
                    return Tuple::new(db_type, t).get_item(i_s, slice_type, result_context);
                }
                _ => (),
            }
        }
        node_ref.add_typing_issue(
            i_s.db,
            IssueType::NotIndexable {
                type_: self.class.format_short(i_s.db),
            },
        );
        Inferred::new_any()
    }

    fn iter(&self, i_s: &mut InferenceState<'db, '_>, from: NodeRef) -> IteratorContent<'a> {
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
                            .execute_function(i_s, "__next__", from),
                    );
                }
                FoundOnClass::UnresolvedDbType(db_type @ DbType::Tuple(t)) => {
                    return Tuple::new(db_type, t).iter(i_s, from);
                }
                _ => (),
            }
        }
        from.add_typing_issue(
            i_s.db,
            IssueType::NotIterable {
                type_: format!("{:?}", self.class.format_short(i_s.db)).into(),
            },
        );
        IteratorContent::Any
    }

    fn as_instance(&self) -> Option<&Instance<'a>> {
        Some(self)
    }

    fn as_type(&self, i_s: &mut InferenceState<'db, '_>) -> Type<'a> {
        if matches!(self.class.generics, Generics::Self_ { .. }) {
            // The generics are only ever self for our own instance, because Generics::Self_ is
            // only used for the current class.
            debug_assert_eq!(i_s.current_class().unwrap().node_ref, self.class.node_ref);
            Type::owned(DbType::Self_)
        } else {
            Type::Class(self.class)
        }
    }

    fn description(&self, i_s: &mut InferenceState) -> String {
        format!(
            "{} {}",
            format!("{:?}", self.kind()).to_lowercase(),
            self.class.format_short(i_s.db),
        )
    }
}

enum FoundOnClass<'a> {
    Attribute(Inferred),
    UnresolvedDbType(&'a DbType),
}

struct ClassMroFinder<'db, 'a, 'c, 'd> {
    i_s: &'d mut InferenceState<'db, 'c>,
    instance: &'d Instance<'d>,
    mro_iterator: MroIterator<'db, 'a>,
    from: NodeRef<'d>,
    name: &'d str,
}

impl<'db: 'a, 'a> Iterator for ClassMroFinder<'db, 'a, '_, '_> {
    type Item = FoundOnClass<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        for (mro_index, t) in self.mro_iterator.by_ref() {
            if let Some(class) = t.maybe_class(self.i_s.db) {
                let result = class
                    .lookup_symbol(self.i_s, self.name)
                    .and_then(|inf| {
                        inf.resolve_class_type_vars(self.i_s, &self.instance.class)
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
            } else {
                match t {
                    // Types are always precalculated in the class mro.
                    Type::Type(Cow::Borrowed(t)) => return Some(FoundOnClass::UnresolvedDbType(t)),
                    _ => unreachable!(),
                }
            }
        }
        None
    }
}
