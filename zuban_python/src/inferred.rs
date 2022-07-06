use parsa_python_ast::{NodeIndex, Primary, PrimaryContent, PythonString};
use std::fmt;

use crate::arguments::{
    Arguments, CombinedArguments, KnownArguments, NoArguments, SimpleArguments,
};
use crate::database::{
    AnyLink, ComplexPoint, Database, DbType, FileIndex, GenericsList, Locality, MroIndex, Point,
    PointLink, PointType, Specific, TypeVar, TypeVarType,
};
use crate::debug;
use crate::file::PythonFile;
use crate::file_state::File;
use crate::generics::{Generics, Type};
use crate::inference_state::InferenceState;
use crate::name::{ValueName, ValueNameIterator, WithValueName};
use crate::node_ref::NodeRef;
use crate::value::{
    BoundMethod, Callable, CallableClass, Class, ClassLike, DictLiteral, Function, Instance,
    IteratorContent, ListLiteral, Module, NoneInstance, OverloadedFunction, RevealTypeFunction,
    Tuple, TupleClass, TypeAlias, TypeVarInstance, TypingCast, TypingClass, TypingClassVar,
    TypingType, TypingWithGenerics, Value,
};

pub enum FunctionOrOverload<'db, 'a> {
    Function(Function<'db, 'a>),
    Overload(OverloadedFunction<'db, 'a>),
}

#[derive(Debug, Clone, PartialEq)]
enum InferredState<'db> {
    Saved(NodeRef<'db>, Point),
    UnsavedFileReference(FileIndex),
    UnsavedComplex(ComplexPoint),
    UnsavedSpecific(Specific),
    Unknown,
}

#[derive(Clone)]
pub struct Inferred<'db> {
    state: InferredState<'db>,
}

impl<'db> Inferred<'db> {
    pub fn new_and_save(file: &'db PythonFile, node_index: NodeIndex, point: Point) -> Self {
        file.points.set(node_index, point);
        Self::new_saved(file, node_index, point)
    }

    pub fn from_saved_node_ref(node_ref: NodeRef<'db>) -> Self {
        Self {
            state: InferredState::Saved(node_ref, node_ref.point()),
        }
    }

    pub fn new_saved2(file: &'db PythonFile, node_index: NodeIndex) -> Self {
        // TODO rethink this method and new_saved
        let node_ref = NodeRef { file, node_index };
        Self {
            state: InferredState::Saved(node_ref, node_ref.point()),
        }
    }

    pub fn new_saved(file: &'db PythonFile, node_index: NodeIndex, point: Point) -> Self {
        Self {
            state: InferredState::Saved(NodeRef { file, node_index }, point),
        }
    }

    pub fn new_unsaved_complex(complex: ComplexPoint) -> Self {
        Self {
            state: InferredState::UnsavedComplex(complex),
        }
    }

    pub fn new_unsaved_specific(specific: Specific) -> Self {
        Self {
            state: InferredState::UnsavedSpecific(specific),
        }
    }

    pub fn new_unknown() -> Self {
        Self {
            state: InferredState::Unknown,
        }
    }

    pub fn new_none() -> Self {
        Self {
            state: InferredState::UnsavedSpecific(Specific::None),
        }
    }

    pub fn new_any() -> Self {
        Self {
            state: InferredState::UnsavedSpecific(Specific::TypingAny),
        }
    }

    pub fn new_file_reference(index: FileIndex) -> Self {
        // TODO maybe remove this and UnsavedFileReference??? unused??
        Self {
            state: InferredState::UnsavedFileReference(index),
        }
    }

    pub fn execute_db_type(i_s: &mut InferenceState<'db, '_>, generic: DbType) -> Self {
        let state = match generic {
            DbType::Class(link) => {
                InferredState::UnsavedComplex(ComplexPoint::Instance(link, None))
            }
            DbType::GenericClass(l, g) => {
                InferredState::UnsavedComplex(ComplexPoint::Instance(l, Some(g)))
            }
            DbType::Union(multiple) => {
                let mut multiple = multiple.iter();
                let mut inferred = Self::execute_db_type(i_s, multiple.next().unwrap().clone());
                for m in multiple {
                    inferred = inferred.union(Self::execute_db_type(i_s, m.clone()));
                }
                return inferred;
            }
            DbType::Tuple(_) | DbType::Callable(_) => {
                InferredState::UnsavedComplex(ComplexPoint::TypeInstance(Box::new(generic)))
            }
            DbType::Type(c) => match *c {
                DbType::Class(link) => {
                    let node_reference = NodeRef::from_link(i_s.db, link);
                    InferredState::Saved(node_reference, node_reference.point())
                }
                DbType::GenericClass(l, g) => {
                    InferredState::UnsavedComplex(ComplexPoint::GenericClass(l, g))
                }
                DbType::Union(multiple) => {
                    todo!()
                }
                DbType::Tuple(content) => {
                    todo!()
                }
                DbType::Any => return Self::new_any(),
                DbType::Type(_) => InferredState::UnsavedComplex(ComplexPoint::TypeInstance(
                    Box::new(DbType::Type(c)),
                )),
                _ => todo!("{c:?}"),
            },
            DbType::None => return Inferred::new_none(),
            DbType::Any => return Inferred::new_any(),
            DbType::Never => todo!(),
            DbType::TypeVar(ref t) => {
                if t.type_ == TypeVarType::Class {
                    if let Some(class) = i_s.current_class {
                        let g = class.generics().nth(i_s, t.index);
                        return Inferred::execute_db_type(i_s, g);
                    }
                }
                InferredState::UnsavedComplex(ComplexPoint::TypeInstance(Box::new(generic)))
            }
            DbType::Unknown => InferredState::Unknown,
        };
        Self { state }
    }

    pub fn create_instance(class: PointLink, generics: Option<&[DbType]>) -> Self {
        Self::new_unsaved_complex(ComplexPoint::Instance(
            class,
            generics.map(|lst| GenericsList::generics_from_vec(lst.to_vec())),
        ))
    }

    pub fn as_db_type(&self, i_s: &mut InferenceState<'db, '_>) -> DbType {
        self.internal_run(
            i_s,
            &mut |i_s, v| {
                v.as_class_like()
                    .map(|c| c.as_db_type(i_s))
                    .unwrap_or_else(|| {
                        debug!("Type not resolvable: {}", v.description(i_s));
                        DbType::Any
                    })
            },
            &|_, g1, g2| g1.union(g2),
            &mut |i_s| {
                debug!("Type not found: {}", self.description(i_s));
                DbType::Any
            },
        )
    }

    pub fn class_as_type(&self, i_s: &mut InferenceState<'db, '_>) -> Type<'db, '_> {
        self.internal_run(
            i_s,
            // TODO is this is_none necessary? It was added because None class was not implemented
            &mut |i_s, v| match v.is_none() {
                true => Type::None,
                false => Type::ClassLike(v.class(i_s)),
            },
            &|i_s, g1, g2| g1.union(i_s, g2),
            &mut |i_s| Type::Any,
        )
    }

    pub fn class_as_db_type(&self, i_s: &mut InferenceState<'db, '_>) -> DbType {
        self.internal_run(
            i_s,
            &mut |i_s, v| v.class(i_s).as_db_type(i_s),
            &|_, g1, g2| g1.union(g2),
            &mut |i_s| DbType::Any,
        )
    }

    #[inline]
    pub fn internal_run<'a, T>(
        &'a self,
        i_s: &mut InferenceState<'db, '_>,
        callable: &mut impl FnMut(&mut InferenceState<'db, '_>, &dyn Value<'db, 'a>) -> T,
        reducer: &impl Fn(&mut InferenceState<'db, '_>, T, T) -> T,
        on_missing: &mut impl FnMut(&mut InferenceState<'db, '_>) -> T,
    ) -> T {
        match &self.state {
            InferredState::Saved(definition, point) => {
                self.run_on_saved(i_s, definition, *point, callable, reducer, on_missing)
            }
            InferredState::UnsavedComplex(complex) => {
                self.run_on_complex(i_s, complex, None, callable, reducer, on_missing)
            }
            InferredState::UnsavedSpecific(specific) => todo!("{:?}", specific),
            InferredState::UnsavedFileReference(file_index) => {
                let f = i_s.db.loaded_python_file(*file_index);
                callable(i_s, &Module::new(i_s.db, f))
            }
            InferredState::Unknown => on_missing(i_s),
        }
    }

    #[inline]
    fn run_on_saved<'a, T>(
        &'a self,
        i_s: &mut InferenceState<'db, '_>,
        definition: &NodeRef<'db>,
        point: Point,
        callable: &mut impl FnMut(&mut InferenceState<'db, '_>, &dyn Value<'db, 'a>) -> T,
        reducer: &impl Fn(&mut InferenceState<'db, '_>, T, T) -> T,
        on_missing: &mut impl FnMut(&mut InferenceState<'db, '_>) -> T,
    ) -> T {
        match point.type_() {
            PointType::Specific => self.run_on_specific(
                i_s,
                definition,
                point.specific(),
                callable,
                reducer,
                on_missing,
            ),
            PointType::Complex => {
                let complex = definition.file.complex_points.get(point.complex_index());
                if let ComplexPoint::Class(cls_storage) = complex {
                    let class = Class::new(*definition, cls_storage, Generics::None, None);
                    callable(i_s, &class)
                } else {
                    self.run_on_complex(
                        i_s,
                        complex,
                        Some(definition),
                        callable,
                        reducer,
                        on_missing,
                    )
                }
            }
            PointType::Unknown => on_missing(i_s),
            PointType::FileReference => {
                let f = i_s.db.loaded_python_file(point.file_index());
                callable(i_s, &Module::new(i_s.db, f))
            }
            _ => unreachable!(),
        }
    }

    #[inline]
    fn run_on_specific<'a, T>(
        &'a self,
        i_s: &mut InferenceState<'db, '_>,
        definition: &NodeRef<'db>,
        specific: Specific,
        callable: &mut impl FnMut(&mut InferenceState<'db, '_>, &dyn Value<'db, 'a>) -> T,
        reducer: &impl Fn(&mut InferenceState<'db, '_>, T, T) -> T,
        on_missing: &mut impl FnMut(&mut InferenceState<'db, '_>) -> T,
    ) -> T {
        match specific {
            Specific::Function => callable(i_s, &Function::new(*definition, None)),
            Specific::AnnotationClassInstance => {
                let expr_def = definition.add_to_node_index(2);
                let inferred = expr_def
                    .file
                    .inference(i_s)
                    .check_point_cache(expr_def.node_index)
                    .unwrap();
                inferred.with_instance(i_s, definition, None, |i_s, instance| {
                    callable(&mut i_s.with_annotation_instance(), instance)
                })
            }
            Specific::InstanceWithArguments => {
                let inf_cls = self.infer_instance_with_arguments_cls(i_s, definition);
                let class = inf_cls.maybe_class(i_s).unwrap();
                let args = SimpleArguments::from_primary(
                    definition.file,
                    definition.as_primary(),
                    None,
                    Some(class),
                );
                let init = class.simple_init_func(i_s, &args);
                inf_cls.with_instance(i_s, definition, None, |i_s, instance| {
                    // TODO is this MroIndex correct?
                    let instance_arg = KnownArguments::new(self, None);
                    let args = CombinedArguments::new(&instance_arg, &args);
                    callable(&mut i_s.with_func_and_args(&init, &args), instance)
                })
            }
            Specific::SimpleGeneric => {
                let class = self.maybe_class(i_s).unwrap();
                callable(i_s, &class)
            }
            Specific::List => callable(i_s, &ListLiteral::new(*definition)),
            Specific::Dict => callable(i_s, &DictLiteral::new(*definition)),
            Specific::AnnotationWithTypeVars => {
                let db_type = definition
                    .file
                    .inference(i_s)
                    .use_db_type_of_annotation(definition.node_index);
                self.run_on_db_type(i_s, db_type, callable, reducer, on_missing)
            }
            Specific::TypingProtocol
            | Specific::TypingGeneric
            | Specific::TypingTuple
            | Specific::TypingUnion
            | Specific::TypingOptional
            | Specific::TypingType
            | Specific::TypingCallable => callable(i_s, &TypingClass::new(specific)),
            Specific::TypingWithGenerics => {
                let inf = definition
                    .file
                    .inference(i_s)
                    .infer_primary_or_atom(definition.as_primary().first());
                if let InferredState::Saved(_, p) = inf.state {
                    callable(i_s, &TypingWithGenerics::new(*definition, p.specific()))
                } else {
                    unreachable!()
                }
            }
            Specific::TypingAny | Specific::Cycle => on_missing(i_s),
            Specific::TypingCast => callable(i_s, &TypingCast()),
            Specific::TypingClassVar => callable(i_s, &TypingClassVar()),
            Specific::RevealTypeFunction => callable(i_s, &RevealTypeFunction()),
            Specific::None => callable(i_s, &NoneInstance()),
            _ => {
                let instance = self.resolve_specific(i_s.db, specific);
                callable(i_s, &instance)
            }
        }
    }

    fn run_on_complex<'a, T>(
        &'a self,
        i_s: &mut InferenceState<'db, '_>,
        complex: &'a ComplexPoint,
        definition: Option<&NodeRef<'db>>,
        callable: &mut impl FnMut(&mut InferenceState<'db, '_>, &dyn Value<'db, 'a>) -> T,
        reducer: &impl Fn(&mut InferenceState<'db, '_>, T, T) -> T,
        on_missing: &mut impl FnMut(&mut InferenceState<'db, '_>) -> T,
    ) -> T {
        match complex {
            ComplexPoint::ExecutionInstance(cls_definition, execution) => {
                let def = NodeRef::from_link(i_s.db, *cls_definition);
                let init = Function::from_execution(i_s.db, execution, None);
                let complex = def.complex().unwrap();
                if let ComplexPoint::Class(cls_storage) = complex {
                    let args = SimpleArguments::from_execution(i_s.db, execution);
                    let class = Class::new(def, cls_storage, Generics::None, None);
                    debug_assert!(class.type_vars(i_s).is_empty());
                    let instance = Instance::new(class, None);
                    // TODO is this MroIndex fine? probably not!
                    let instance_arg = KnownArguments::new(self, None);
                    let args = CombinedArguments::new(&instance_arg, &args);
                    callable(&mut i_s.with_func_and_args(&init, &args), &instance)
                } else {
                    unreachable!()
                }
            }
            ComplexPoint::Union(lst) => {
                let mut previous = None;
                for any_link in lst.iter() {
                    let result = match any_link {
                        AnyLink::Reference(link) => {
                            let reference = NodeRef::from_link(i_s.db, *link);
                            self.run_on_saved(
                                i_s,
                                &reference,
                                reference.point(),
                                callable,
                                reducer,
                                on_missing,
                            )
                        }
                        AnyLink::Complex(c) => {
                            self.run_on_complex(i_s, c, definition, callable, reducer, on_missing)
                        }
                        AnyLink::SimpleSpecific(specific) => match specific {
                            Specific::None => callable(i_s, &NoneInstance()),
                            Specific::TypingAny => on_missing(i_s),
                            _ => todo!(
                                "not even sure if this should be a separate class {specific:?}"
                            ),
                        },
                        AnyLink::Unknown => on_missing(i_s),
                    };
                    if let Some(p) = previous {
                        previous = Some(reducer(i_s, p, result))
                    } else {
                        previous = Some(result)
                    }
                }
                previous.unwrap()
            }
            ComplexPoint::BoundMethod(instance_link, mro_index, func_link) => {
                let reference = NodeRef::from_link(i_s.db, *func_link);

                // TODO this is potentially not needed, a class could lazily be fetched with a
                // closure
                let inf = Inferred::from_any_link(i_s.db, instance_link);
                let instance = inf.expect_instance(i_s);

                let class = instance.class.mro(i_s).nth(mro_index.0 as usize).unwrap().1;
                let class = match class {
                    ClassLike::Class(c) => c,
                    _ => unreachable!(),
                };
                if let Some(ComplexPoint::FunctionOverload(overload)) = reference.complex() {
                    let func = OverloadedFunction::new(reference, overload, Some(class));
                    callable(i_s, &BoundMethod::new(&instance, *mro_index, &func))
                } else {
                    let func = Function::new(reference, Some(class));
                    callable(i_s, &BoundMethod::new(&instance, *mro_index, &func))
                }
            }
            ComplexPoint::Closure(function, execution) => {
                let f = i_s.db.loaded_python_file(function.file);
                let func = Function::from_execution(i_s.db, execution, None);
                let args = SimpleArguments::from_execution(i_s.db, execution);
                callable(
                    &mut i_s.with_func_and_args(&func, &args),
                    &Function::new(NodeRef::from_link(i_s.db, *function), None),
                )
            }
            ComplexPoint::Instance(cls, generics_list) => {
                let generics = generics_list
                    .as_ref()
                    .map(Generics::new_list)
                    .unwrap_or(Generics::None);
                let instance = use_instance(NodeRef::from_link(i_s.db, *cls), generics, None);
                callable(i_s, &instance)
            }
            ComplexPoint::FunctionOverload(overload) => callable(
                i_s,
                &OverloadedFunction::new(*definition.unwrap(), overload, None),
            ),
            ComplexPoint::GenericClass(link, generics) => {
                let class = Class::from_position(
                    NodeRef::from_link(i_s.db, *link),
                    Generics::new_list(generics),
                    None,
                )
                .unwrap();
                callable(i_s, &class)
            }
            ComplexPoint::TypeInstance(t) => {
                self.run_on_db_type(i_s, t, callable, reducer, on_missing)
            }
            ComplexPoint::TypeAlias(alias) => callable(i_s, &TypeAlias::new(alias)),
            _ => {
                unreachable!("Classes are handled earlier {complex:?}")
            }
        }
    }

    fn run_on_db_type<'a, T>(
        &'a self,
        i_s: &mut InferenceState<'db, '_>,
        db_type: &'a DbType,
        callable: &mut impl FnMut(&mut InferenceState<'db, '_>, &dyn Value<'db, 'a>) -> T,
        reducer: &impl Fn(&mut InferenceState<'db, '_>, T, T) -> T,
        on_missing: &mut impl FnMut(&mut InferenceState<'db, '_>) -> T,
    ) -> T {
        match db_type {
            DbType::Class(link) => {
                let inst = use_instance(NodeRef::from_link(i_s.db, *link), Generics::None, None);
                callable(i_s, &inst)
            }
            DbType::GenericClass(link, generics) => {
                let g = Generics::new_list(generics);
                let inst = use_instance(NodeRef::from_link(i_s.db, *link), g, None);
                callable(i_s, &inst)
            }
            DbType::Union(lst) => lst
                .iter()
                .fold(None, |input, t| match input {
                    None => Some(self.run_on_db_type(i_s, t, callable, reducer, on_missing)),
                    Some(t1) => {
                        let t2 = self.run_on_db_type(i_s, t, callable, reducer, on_missing);
                        Some(reducer(i_s, t1, t2))
                    }
                })
                .unwrap(),
            DbType::TypeVar(t) => callable(i_s, &TypeVarInstance::new(i_s.db, db_type, t)),
            DbType::Tuple(content) => callable(i_s, &Tuple::new(content)),
            DbType::Callable(content) => callable(i_s, &Callable::new(db_type, content)),
            DbType::None => callable(i_s, &NoneInstance()),
            DbType::Any => on_missing(i_s),
            DbType::Unknown => todo!(),
            DbType::Never => todo!(),
            DbType::Type(t) => {
                self.run_on_db_type_type(i_s, db_type, t, callable, reducer, on_missing)
            }
        }
    }

    fn run_on_db_type_type<'a, T>(
        &'a self,
        i_s: &mut InferenceState<'db, '_>,
        db_type: &'a DbType,
        type_: &'a DbType,
        callable: &mut impl FnMut(&mut InferenceState<'db, '_>, &dyn Value<'db, 'a>) -> T,
        reducer: &impl Fn(&mut InferenceState<'db, '_>, T, T) -> T,
        on_missing: &mut impl FnMut(&mut InferenceState<'db, '_>) -> T,
    ) -> T {
        match type_ {
            DbType::Class(link) => {
                let node_ref = NodeRef::from_link(i_s.db, *link);
                callable(
                    i_s,
                    &Class::from_position(node_ref, Generics::None, None).unwrap(),
                )
            }
            DbType::GenericClass(link, generics) => {
                let class = Class::from_position(
                    NodeRef::from_link(i_s.db, *link),
                    Generics::new_list(generics),
                    None,
                )
                .unwrap();
                callable(i_s, &class)
            }
            DbType::Union(lst) => lst
                .iter()
                .fold(None, |input, t| match input {
                    None => Some(
                        self.run_on_db_type_type(i_s, db_type, t, callable, reducer, on_missing),
                    ),
                    Some(t1) => {
                        let t2 = self
                            .run_on_db_type_type(i_s, db_type, t, callable, reducer, on_missing);
                        Some(reducer(i_s, t1, t2))
                    }
                })
                .unwrap(),
            DbType::TypeVar(t) => todo!(),
            DbType::Type(g) => callable(i_s, &TypingType::new(i_s.db, g)),
            DbType::Tuple(content) => callable(i_s, &TupleClass::new(content)),
            DbType::Callable(content) => {
                debug!("TODO the db_type can be wrong if it was part of a union");
                callable(i_s, &CallableClass::new(db_type, content))
            }
            DbType::None => {
                debug!("TODO this should be NoneType instead of None");
                callable(i_s, &NoneInstance())
            }
            // TODO it is wrong that this uses TypingType like Type(Type(Any))
            DbType::Any => callable(i_s, &TypingType::new(i_s.db, db_type)),
            DbType::Unknown => todo!(),
            DbType::Never => todo!(),
        }
    }

    pub fn run_on_value(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        callable: &mut impl Fn(&mut InferenceState<'db, '_>, &dyn Value<'db, '_>) -> Self,
    ) -> Self {
        self.internal_run(i_s, callable, &|i_s, i1, i2| i1.union(i2), &mut |i_s| {
            Inferred::new_unknown()
        })
    }

    pub fn run_on_value_names<C, T>(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        callable: &C,
    ) -> ValueNameIterator<T>
    where
        C: Fn(&dyn ValueName<'db>) -> T,
    {
        self.internal_run(
            i_s,
            &mut |i_s, value| {
                ValueNameIterator::Single(callable(&WithValueName::new(i_s.db, value)))
            },
            &|_, iter1, iter2| {
                // Reducer
                match iter1 {
                    ValueNameIterator::Single(element1) => match iter2 {
                        ValueNameIterator::Single(element2) => {
                            ValueNameIterator::Multiple(vec![element1, element2])
                        }
                        ValueNameIterator::Multiple(mut list2) => {
                            list2.push(element1);
                            ValueNameIterator::Multiple(list2)
                        }
                        ValueNameIterator::Finished => ValueNameIterator::Single(element1),
                    },
                    ValueNameIterator::Multiple(mut list1) => match iter2 {
                        ValueNameIterator::Single(element2) => {
                            list1.push(element2);
                            ValueNameIterator::Multiple(list1)
                        }
                        ValueNameIterator::Multiple(mut list2) => {
                            list1.append(&mut list2);
                            ValueNameIterator::Multiple(list1)
                        }
                        ValueNameIterator::Finished => ValueNameIterator::Multiple(list1),
                    },
                    ValueNameIterator::Finished => iter2,
                }
            },
            &mut |i_s| ValueNameIterator::Finished,
        )
    }

    pub fn run_mut(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        callable: &mut impl for<'a, 'b, 'c> FnMut(&mut InferenceState<'db, 'c>, &'b dyn Value<'db, 'a>),
        mut on_missing: impl FnMut(),
    ) {
        self.internal_run(i_s, callable, &|_, i1, i2| (), &mut |i_s| on_missing())
    }

    fn resolve_specific(&self, db: &'db Database, specific: Specific) -> Instance<'db, '_> {
        self.load_builtin_instance_from_str(
            db,
            match specific {
                Specific::String => "str",
                Specific::Integer => "int",
                Specific::Float => "float",
                Specific::Boolean => "bool",
                Specific::Bytes => "bytes",
                Specific::Complex => "complex",
                Specific::Ellipsis => "ellipsis", // TODO this should not even be public
                actual => todo!("{actual:?}"),
            },
        )
    }

    fn load_builtin_instance_from_str(
        &self,
        db: &'db Database,
        name: &'static str,
    ) -> Instance<'db, '_> {
        let builtins = db.python_state.builtins();
        let node_index = builtins.lookup_global(name).unwrap().node_index - 1;
        let v = builtins.points.get(node_index);
        debug_assert_eq!(v.type_(), PointType::Redirect);
        debug_assert_eq!(v.file_index(), builtins.file_index());
        use_instance(NodeRef::new(builtins, v.node_index()), Generics::None, None)
    }

    pub fn maybe_type_var(&self, i_s: &mut InferenceState<'db, '_>) -> Option<TypeVar> {
        if let InferredState::Saved(definition, point) = self.state {
            if point.type_() == PointType::Specific
                && point.specific() == Specific::InstanceWithArguments
            {
                // TODO this check can/should be optimized by comparing node pointers that are cached
                // in python_state
                let cls = self.infer_instance_with_arguments_cls(i_s, &definition);
                if let InferredState::Saved(cls_definition, _) = cls.state {
                    if cls_definition.file.file_index() == i_s.db.python_state.typing().file_index()
                        && cls_definition
                            .maybe_class()
                            .map(|cls| cls.name().as_str() == "TypeVar")
                            .unwrap_or(false)
                    {
                        let args = SimpleArguments::from_primary(
                            definition.file,
                            definition.as_primary(),
                            None,
                            None,
                        );
                        return args.maybe_type_var(i_s);
                    }
                }
            }
        }
        None
    }

    pub fn resolve_function_return(self, i_s: &mut InferenceState<'db, '_>) -> Self {
        if let InferredState::Saved(definition, point) = self.state {
            if point.type_() == PointType::Specific {
                match point.specific() {
                    Specific::InstanceWithArguments => {
                        let inf_cls = self
                            .infer_instance_with_arguments_cls(i_s, &definition)
                            .resolve_function_return(i_s);
                        let class = inf_cls.maybe_class(i_s).unwrap();
                        debug_assert!(class.type_vars(i_s).is_empty());
                        let args = SimpleArguments::from_primary(
                            definition.file,
                            definition.as_primary(),
                            None,
                            Some(class),
                        );
                        let init = class.simple_init_func(i_s, &args);
                        return Inferred::new_unsaved_complex(match args.as_execution(&init) {
                            Some(execution) => ComplexPoint::ExecutionInstance(
                                inf_cls.get_saved().unwrap().0.as_link(),
                                Box::new(execution),
                            ),
                            None => ComplexPoint::Instance(
                                inf_cls.get_saved().unwrap().0.as_link(),
                                None,
                            ),
                        });
                    }
                    Specific::Closure => {
                        return Inferred::new_unsaved_complex(ComplexPoint::Closure(
                            PointLink::new(definition.file.file_index(), definition.node_index),
                            Box::new(i_s.args_as_execution().unwrap()),
                        ));
                    }
                    Specific::Param => {
                        todo!("might not even happen - remove")
                        //return i_s.infer_param(&definition);
                    }
                    _ => (),
                }
            }
        }
        self
    }

    fn infer_instance_with_arguments_cls(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        definition: &NodeRef<'db>,
    ) -> Self {
        definition
            .file
            .inference(i_s)
            .infer_primary_or_atom(definition.as_primary().first())
    }

    fn with_instance<'a, T>(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        instance: &NodeRef<'db>,
        generics: Option<Generics<'db, 'a>>,
        callable: impl FnOnce(&mut InferenceState<'db, '_>, &Instance<'db, 'a>) -> T,
    ) -> T {
        match &self.state {
            InferredState::Saved(definition, point) => {
                if point.type_() == PointType::Specific {
                    if let Specific::SimpleGeneric = point.specific() {
                        let p = Primary::by_index(&definition.file.tree, definition.node_index);
                        let cls = definition
                            .file
                            .inference(i_s)
                            .infer_primary_or_atom(p.first());
                        cls.with_instance(
                            i_s,
                            instance,
                            Some(Generics::new_slice(definition.file, p.expect_slice())),
                            callable,
                        )
                    } else {
                        unreachable!("{point:?}")
                    }
                } else {
                    callable(
                        i_s,
                        &use_instance(
                            *definition,
                            generics.unwrap_or(Generics::None),
                            Some(*instance),
                        ),
                    )
                }
            }
            _ => unreachable!("{:?}", self.state),
        }
    }

    fn expect_instance(&self, i_s: &mut InferenceState<'db, '_>) -> Instance<'db, '_> {
        let mut instance = None;
        self.run_mut(
            i_s,
            &mut |i_s, v| {
                // TODO this is a weird issue, probably a compiler bug...
                // https://github.com/rust-lang/rust/issues/91942
                let v: &dyn Value = unsafe { std::mem::transmute(v) };
                if let Some(i) = v.as_instance() {
                    instance = Some(*i);
                } else {
                    unreachable!()
                }
            },
            || unreachable!(),
        );
        instance.unwrap()
    }

    pub fn maybe_class(&self, i_s: &mut InferenceState<'db, '_>) -> Option<Class<'db, 'db>> {
        let mut generics = Generics::None;
        if let InferredState::Saved(definition, point) = &self.state {
            if point.type_() == PointType::Specific {
                generics = Self::expect_generics(*definition, *point).unwrap_or(Generics::None);
            }
        }
        self.maybe_class_internal(i_s, generics)
    }

    fn maybe_class_internal<'a>(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        generics: Generics<'db, 'a>,
    ) -> Option<Class<'db, 'a>> {
        match &self.state {
            InferredState::Saved(definition, point) => match point.type_() {
                PointType::Complex => {
                    let complex = definition.file.complex_points.get(point.complex_index());
                    if let ComplexPoint::Class(c) = complex {
                        Some(Class::new(*definition, c, generics, None))
                    } else {
                        None
                    }
                }
                PointType::Specific => match point.specific() {
                    Specific::SimpleGeneric => {
                        let inferred = definition
                            .file
                            .inference(i_s)
                            .infer_primary_or_atom(definition.as_primary().first());
                        inferred.maybe_class_internal(i_s, generics)
                    }
                    _ => None,
                },
                _ => None,
            },
            InferredState::UnsavedComplex(complex) => {
                if let ComplexPoint::TypeInstance(g) = complex {
                    todo!() // This was originally a return None for tuple class
                }
                todo!("{complex:?}")
            }
            InferredState::UnsavedSpecific(specific) => todo!(),
            InferredState::UnsavedFileReference(file_index) => todo!(),
            InferredState::Unknown => None,
        }
    }

    pub fn expect_int(&self) -> Option<i64> {
        if let InferredState::Saved(definition, point) = self.state {
            if let Some(Specific::Integer) = point.maybe_specific() {
                return definition.infer_int();
            }
        }
        None
    }

    pub fn maybe_str(&self) -> Option<PythonString<'db>> {
        if let InferredState::Saved(definition, point) = self.state {
            if let Some(Specific::String) = point.maybe_specific() {
                return definition.infer_str();
            }
        }
        None
    }

    pub fn save_redirect(self, file: &'db PythonFile, index: NodeIndex) -> Self {
        // TODO this locality should be calculated in a more correct way
        let p = file.points.get(index);
        if p.calculated() && p.maybe_specific() == Some(Specific::Cycle) {
            return Self::new_saved(file, index, file.points.get(index));
        }
        let point = match &self.state {
            InferredState::Saved(definition, point) => {
                // Overwriting strings needs to be possible, because of string annotations
                if p.calculated()
                    && p.maybe_specific() != Some(Specific::String)
                    && point.maybe_specific() != Some(Specific::Cycle)
                {
                    todo!(
                        "{self:?} {:?} {index:?}, {}",
                        file.points.get(index),
                        file.tree.short_debug_of_index(index)
                    );
                }
                file.points.set(
                    index,
                    Point::new_redirect(
                        definition.file.file_index(),
                        definition.node_index,
                        Locality::Todo,
                    ),
                );
                return self;
            }
            InferredState::UnsavedComplex(complex) => {
                file.complex_points
                    .insert(&file.points, index, complex.clone(), Locality::Todo);
                return Self::new_saved(file, index, file.points.get(index));
            }
            InferredState::UnsavedSpecific(specific) => {
                Point::new_simple_specific(*specific, Locality::Todo)
            }
            InferredState::UnsavedFileReference(file_index) => {
                Point::new_file_reference(*file_index, Locality::Todo)
            }
            InferredState::Unknown => Point::new_unknown(file.file_index(), Locality::Todo),
        };
        file.points.set(index, point);
        Self::new_saved(file, index, point)
    }

    pub fn save_if_unsaved(self, file: &'db PythonFile, index: NodeIndex) -> Self {
        if matches!(self.state, InferredState::Saved(_, _)) {
            self
        } else {
            self.save_redirect(file, index)
        }
    }

    pub fn init_as_function<'a>(
        &self,
        class: Class<'db, 'a>,
    ) -> Option<FunctionOrOverload<'db, 'a>> {
        if let InferredState::Saved(definition, point) = &self.state {
            if let Some(Specific::Function) = point.maybe_specific() {
                return Some(FunctionOrOverload::Function(Function::new(
                    *definition,
                    Some(class),
                )));
            }
            if let Some(ComplexPoint::FunctionOverload(overload)) = definition.complex() {
                return Some(FunctionOrOverload::Overload(OverloadedFunction::new(
                    *definition,
                    overload,
                    Some(class),
                )));
            }
        }
        None
    }

    fn get_saved(&self) -> Option<(NodeRef<'db>, Point)> {
        match self.state {
            InferredState::Saved(definition, point) => Some((definition, point)),
            _ => None,
        }
    }

    pub fn union(self, other: Self) -> Self {
        if self.state == other.state {
            self
        } else {
            let mut list = vec![];
            let insert = |list: &mut Vec<AnyLink>, state| {
                match state {
                    InferredState::Saved(definition, _) => {
                        list.push(AnyLink::Reference(definition.as_link()));
                    }
                    InferredState::UnsavedComplex(complex) => match complex {
                        ComplexPoint::Union(lst) => {
                            list.extend(lst.iter().cloned());
                        }
                        _ => list.push(AnyLink::Complex(Box::new(complex))),
                    },
                    InferredState::UnsavedSpecific(specific) => {
                        list.push(AnyLink::SimpleSpecific(specific))
                    }
                    InferredState::UnsavedFileReference(file_index) => todo!(),
                    InferredState::Unknown => list.push(AnyLink::Unknown),
                };
            };
            insert(&mut list, self.state);
            insert(&mut list, other.state);
            Self::new_unsaved_complex(ComplexPoint::Union(list.into_boxed_slice()))
        }
    }

    #[inline]
    pub fn gather_union(mut callable: impl FnMut(&mut dyn FnMut(Self))) -> Self {
        let mut result: Option<Self> = None;
        let r = &mut result;
        callable(&mut |inferred| {
            *r = Some(match r.take() {
                Some(i) => i.union(inferred),
                None => inferred,
            });
        });
        result.unwrap_or_else(|| todo!())
    }

    #[inline]
    pub fn bind(
        self,
        i_s: &mut InferenceState<'db, '_>,
        instance: &Instance<'db, '_>,
        mro_index: MroIndex,
    ) -> Self {
        match &self.state {
            InferredState::Saved(definition, point) => match point.type_() {
                PointType::Specific => {
                    if point.specific() == Specific::Function {
                        let complex = ComplexPoint::BoundMethod(
                            instance.as_inferred(i_s).as_any_link(i_s),
                            mro_index,
                            definition.as_link(),
                        );
                        return Self::new_unsaved_complex(complex);
                    }
                }
                PointType::Complex => {
                    if let ComplexPoint::FunctionOverload(o) =
                        definition.file.complex_points.get(point.complex_index())
                    {
                        let complex = ComplexPoint::BoundMethod(
                            instance.as_inferred(i_s).as_any_link(i_s),
                            mro_index,
                            definition.as_link(),
                        );
                        return Self::new_unsaved_complex(complex);
                    }
                }
                _ => (),
            },
            InferredState::UnsavedComplex(complex) => (),
            InferredState::UnsavedSpecific(specific) => todo!(),
            InferredState::UnsavedFileReference(file_index) => todo!(),
            InferredState::Unknown => (),
        }
        self
    }

    pub fn description(&self, i_s: &mut InferenceState<'db, '_>) -> String {
        self.internal_run(
            i_s,
            &mut |i_s, v| v.description(i_s),
            &|_, i1, i2| format!("{i1}|{i2}"),
            &mut |i_s| "Unknown".to_owned(),
        )
    }

    pub fn debug_info(&self, i_s: &mut InferenceState<'db, '_>) -> String {
        let details = match &self.state {
            InferredState::Saved(definition, point) => {
                format!(
                    "{} (complex?: {:?})",
                    definition.file.file_path(i_s.db),
                    definition.complex(),
                )
            }
            _ => "".to_owned(),
        };
        format!(
            "description = {}\ndebug = {self:?}\ndetails = {details}",
            self.description(i_s),
        )
    }

    pub fn as_any_link(&self, i_s: &InferenceState<'db, '_>) -> AnyLink {
        match &self.state {
            InferredState::Saved(definition, _) => AnyLink::Reference(definition.as_link()),
            InferredState::UnsavedComplex(complex) => AnyLink::Complex(Box::new(complex.clone())),
            InferredState::UnsavedSpecific(specific) => todo!(),
            InferredState::UnsavedFileReference(file_index) => todo!(),
            InferredState::Unknown => todo!(),
        }
    }

    fn from_any_link(db: &'db Database, any: &AnyLink) -> Self {
        match any {
            AnyLink::Reference(def) => {
                let file = db.loaded_python_file(def.file);
                Self::new_saved(file, def.node_index, file.points.get(def.node_index))
            }
            AnyLink::Complex(complex) => Self::new_unsaved_complex(*complex.clone()),
            AnyLink::SimpleSpecific(_) => todo!(),
            AnyLink::Unknown => todo!(),
        }
    }

    fn expect_generics(definition: NodeRef<'db>, point: Point) -> Option<Generics<'db, 'db>> {
        if point.type_() == PointType::Specific && point.specific() == Specific::SimpleGeneric {
            let primary = definition.as_primary();
            match primary.second() {
                PrimaryContent::GetItem(slice_type) => {
                    return Some(Generics::new_slice(definition.file, slice_type))
                }
                _ => {
                    unreachable!()
                }
            }
        }
        None
    }

    pub fn maybe_simple<'a, T>(
        &'a self,
        i_s: &mut InferenceState<'db, '_>,
        c: impl Fn(&dyn Value<'db, 'a>) -> Option<T>,
    ) -> Option<T> {
        self.internal_run(i_s, &mut |i_s, v| c(v), &|_, i1, i2| None, &mut |i_s| None)
    }

    pub fn is_unknown(&self) -> bool {
        match &self.state {
            InferredState::Saved(_, point) => matches!(point.type_(), PointType::Unknown),
            InferredState::Unknown => true,
            _ => false,
        }
    }

    pub fn is_union(&self) -> bool {
        match &self.state {
            InferredState::Saved(reference, point) => reference
                .complex()
                .map(|c| matches!(c, ComplexPoint::Union(_)))
                .unwrap_or(false),
            InferredState::UnsavedComplex(ComplexPoint::Union(_)) => true,
            _ => false,
        }
    }

    pub fn execute_function(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        name: &str,
        from: NodeRef<'db>,
    ) -> Inferred<'db> {
        self.run_on_value(i_s, &mut |i_s, value| {
            value.lookup_implicit(i_s, name, &|i_s| todo!())
        })
        .run_on_value(i_s, &mut |i_s, value| {
            value.execute(i_s, &NoArguments::new(from), &|_, _, _, _, _, _, _| {
                todo!("currently only used for __next__")
            })
        })
    }

    pub fn iter(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        from: NodeRef<'db>,
    ) -> IteratorContent<'db, '_> {
        self.internal_run(
            i_s,
            &mut |i_s, v| v.iter(i_s, from),
            &|_, i1, i2| todo!(),
            &mut |i_s| IteratorContent::Any,
        )
    }
}

impl fmt::Debug for Inferred<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut s = f.debug_struct("Inferred");
        match &self.state {
            InferredState::Saved(definition, point) => {
                s.field("definition", &definition).field("point", &point)
            }
            InferredState::UnsavedComplex(complex) => s.field("complex", &complex),
            InferredState::UnsavedSpecific(specific) => s.field("specific", &specific),
            InferredState::UnsavedFileReference(file_index) => todo!(),
            InferredState::Unknown => s.field("unknown", &true),
        }
        .finish()
    }
}

fn use_instance<'db, 'a>(
    class_reference: NodeRef<'db>,
    generics: Generics<'db, 'a>,
    instance_reference: Option<NodeRef<'db>>,
) -> Instance<'db, 'a> {
    let class = Class::from_position(class_reference, generics, None).unwrap();
    Instance::new(class, instance_reference)
}

// TODO unused -> delete?!
enum Exact<'db> {
    Int(bool),
    Str(&'db str),
    Bool(bool),
    Bytes(&'db str),
    Float(f64),
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_sizes() {
        use super::*;
        use std::mem::size_of;
        assert_eq!(size_of::<Inferred>(), 40);
    }
}
