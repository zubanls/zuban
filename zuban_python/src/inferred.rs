use parsa_python_ast::{
    debug_info, Atom, AtomContent, ClassDef, Expression, Name, NamedExpression, NodeIndex, Primary,
    PrimaryContent,
};
use std::fmt;

use crate::arguments::{Arguments, InstanceArguments, NoArguments, SimpleArguments};
use crate::database::{
    AnyLink, ComplexPoint, Database, FileIndex, GenericPart, GenericsList, Locality, MroIndex,
    Point, PointLink, PointType, Specific, TypeVarIndex,
};
use crate::debug;
use crate::file::PythonFile;
use crate::file_state::File;
use crate::generics::{GenericOption, Generics};
use crate::inference_state::InferenceState;
use crate::name::{ValueName, ValueNameIterator, WithValueName};
use crate::value::{
    BoundMethod, Callable, CallableClass, Class, ClassLike, DictLiteral, Function, Instance,
    IteratorContent, ListLiteral, Module, NoneInstance, OverloadedFunction, Tuple, TupleClass,
    TypingCast, TypingClass, TypingClassVar, TypingType, TypingWithGenerics, Value,
};

pub trait Inferrable<'db> {
    fn infer(&self, i_s: &mut InferenceState<'db, '_>) -> Inferred<'db>;
}

#[derive(Debug, Clone, Copy)]
pub struct NodeReference<'db> {
    pub file: &'db PythonFile,
    pub node_index: NodeIndex,
}

impl<'db> std::cmp::PartialEq for NodeReference<'db> {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self.file, other.file) && self.node_index == other.node_index
    }
}

impl<'db> NodeReference<'db> {
    pub fn new(file: &'db PythonFile, node_index: NodeIndex) -> Self {
        Self { file, node_index }
    }

    pub fn from_link(database: &'db Database, point: PointLink) -> Self {
        let file = database.loaded_python_file(point.file);
        Self {
            file,
            node_index: point.node_index,
        }
    }

    pub fn add_to_node_index(&self, add: NodeIndex) -> Self {
        Self::new(self.file, self.node_index + add)
    }

    pub fn point(&self) -> Point {
        self.file.points.get(self.node_index)
    }

    pub fn set_point(&self, point: Point) {
        self.file.points.set(self.node_index, point)
    }

    pub fn complex(&self) -> Option<&'db ComplexPoint> {
        let point = self.point();
        if let PointType::Complex = point.type_() {
            Some(self.file.complex_points.get(point.complex_index()))
        } else {
            None
        }
    }

    pub fn insert_complex(&self, complex: ComplexPoint) {
        self.file
            .complex_points
            .insert(&self.file.points, self.node_index, complex);
    }

    pub fn as_link(&self) -> PointLink {
        PointLink::new(self.file.file_index(), self.node_index)
    }

    fn as_expression(&self) -> Expression<'db> {
        Expression::by_index(&self.file.tree, self.node_index)
    }

    pub fn as_primary(&self) -> Primary<'db> {
        Primary::by_index(&self.file.tree, self.node_index)
    }

    pub fn as_name(&self) -> Name<'db> {
        Name::by_index(&self.file.tree, self.node_index)
    }

    pub fn infer_int(&self) -> Option<i64> {
        Atom::maybe_by_index(&self.file.tree, self.node_index).and_then(|atom| {
            match atom.unpack() {
                AtomContent::Int(i) => i.as_str().parse().ok(),
                _ => None,
            }
        })
    }

    pub fn maybe_class(&self) -> Option<ClassDef<'db>> {
        ClassDef::maybe_by_index(&self.file.tree, self.node_index)
    }

    pub fn as_named_expression(&self) -> NamedExpression<'db> {
        NamedExpression::by_index(&self.file.tree, self.node_index)
    }

    pub fn debug_info(&self, db: &Database) -> String {
        format!(
            "{}: {}",
            self.file.file_path(db),
            debug_info(&self.file.tree, self.node_index)
        )
    }
}

pub enum FunctionOrOverload<'db, 'a> {
    Function(Function<'db, 'a>),
    Overload(OverloadedFunction<'db, 'a>),
}

#[derive(Debug, Clone, PartialEq)]
enum InferredState<'db> {
    Saved(NodeReference<'db>, Point),
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

    pub fn new_saved(file: &'db PythonFile, node_index: NodeIndex, point: Point) -> Self {
        Self {
            state: InferredState::Saved(NodeReference { file, node_index }, point),
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

    pub fn execute_generic_part(db: &'db Database, generic: GenericPart) -> Self {
        let state = match generic {
            GenericPart::Class(link) => {
                InferredState::UnsavedComplex(ComplexPoint::Instance(link, None))
            }
            GenericPart::GenericClass(l, g) => {
                InferredState::UnsavedComplex(ComplexPoint::Instance(l, Some(g)))
            }
            GenericPart::Union(multiple) => {
                let mut multiple = multiple.iter();
                let mut inferred = Self::execute_generic_part(db, multiple.next().unwrap().clone());
                for m in multiple {
                    inferred = inferred.union(Self::execute_generic_part(db, m.clone()));
                }
                return inferred;
            }
            GenericPart::Tuple(content) => {
                InferredState::UnsavedComplex(ComplexPoint::Tuple(content))
            }
            GenericPart::Callable(content) => {
                InferredState::UnsavedComplex(ComplexPoint::Callable(content))
            }
            GenericPart::Type(c) => match *c {
                GenericPart::Class(link) => {
                    let node_reference = NodeReference::from_link(db, link);
                    InferredState::Saved(node_reference, node_reference.point())
                }
                GenericPart::GenericClass(l, g) => {
                    InferredState::UnsavedComplex(ComplexPoint::GenericClass(l, g))
                }
                GenericPart::Union(multiple) => {
                    todo!()
                }
                GenericPart::Tuple(content) => {
                    todo!()
                }
                _ => todo!(),
            },
            GenericPart::TypeVar(_, _) | GenericPart::Unknown => InferredState::Unknown,
        };
        Self { state }
    }

    pub fn create_instance(class: PointLink, generics: Option<&[GenericPart]>) -> Self {
        Self::new_unsaved_complex(ComplexPoint::Instance(
            class,
            generics.map(|lst| GenericsList::new(lst.to_vec().into_boxed_slice())),
        ))
    }

    pub fn as_generic_part(&self, i_s: &mut InferenceState<'db, '_>) -> GenericPart {
        self.internal_run(
            i_s,
            &mut |i_s, v| {
                v.as_class_like()
                    .map(|c| c.as_generic_part(i_s))
                    .unwrap_or_else(|| {
                        debug!("Generic part not resolvable: {}", v.description(i_s));
                        GenericPart::Unknown
                    })
            },
            &|g1, g2| g1.union(g2),
            &mut |i_s, inf| {
                debug!("Generic part not found: {}", inf.description(i_s));
                GenericPart::Unknown
            },
            &mut |type_var_index, node_ref| {
                GenericPart::TypeVar(type_var_index, node_ref.as_link())
            },
        )
    }

    pub fn as_generic_option(&self, i_s: &mut InferenceState<'db, '_>) -> GenericOption<'db, '_> {
        self.internal_run(
            i_s,
            &mut |i_s, v| {
                v.as_class_like()
                    .map(GenericOption::ClassLike)
                    .or_else(|| v.is_none().then(|| GenericOption::None))
                    .unwrap_or_else(|| {
                        debug!("Generic option not resolvable: {}", v.description(i_s));
                        GenericOption::Invalid
                    })
            },
            &|g1, g2| g1.union(g2),
            &mut |i_s, inf| {
                debug!("Generic option is invalid: {}", inf.description(i_s));
                GenericOption::Invalid
            },
            &mut GenericOption::TypeVar,
        )
    }

    pub fn class_as_generic_option(
        &self,
        i_s: &mut InferenceState<'db, '_>,
    ) -> GenericOption<'db, '_> {
        self.internal_run(
            i_s,
            &mut |i_s, v| GenericOption::ClassLike(v.class(i_s)),
            &|g1, g2| g1.union(g2),
            &mut |i_s, inf| {
                debug!("Generic class option is invalid: {}", inf.description(i_s));
                GenericOption::Invalid
            },
            &mut GenericOption::TypeVar,
        )
    }

    #[inline]
    pub fn internal_run<'a, T>(
        &'a self,
        i_s: &mut InferenceState<'db, '_>,
        callable: &mut impl FnMut(&mut InferenceState<'db, '_>, &dyn Value<'db, 'a>) -> T,
        reducer: &impl Fn(T, T) -> T,
        on_missing: &mut impl FnMut(&mut InferenceState<'db, '_>, Self) -> T,
        on_type_var: &mut impl FnMut(TypeVarIndex, NodeReference<'db>) -> T,
    ) -> T {
        match &self.state {
            InferredState::Saved(definition, point) => self.run_on_saved(
                i_s,
                definition,
                *point,
                callable,
                reducer,
                on_missing,
                on_type_var,
            ),
            InferredState::UnsavedComplex(complex) => self.run_on_complex(
                i_s,
                complex,
                None,
                callable,
                reducer,
                on_missing,
                on_type_var,
            ),
            InferredState::UnsavedSpecific(specific) => todo!(),
            InferredState::Unknown => on_missing(i_s, self.clone()),
        }
    }

    #[inline]
    fn run_on_saved<'a, T>(
        &'a self,
        i_s: &mut InferenceState<'db, '_>,
        definition: &NodeReference<'db>,
        point: Point,
        callable: &mut impl FnMut(&mut InferenceState<'db, '_>, &dyn Value<'db, 'a>) -> T,
        reducer: &impl Fn(T, T) -> T,
        on_missing: &mut impl FnMut(&mut InferenceState<'db, '_>, Self) -> T,
        on_type_var: &mut impl FnMut(TypeVarIndex, NodeReference<'db>) -> T,
    ) -> T {
        match point.type_() {
            PointType::Specific => self.run_on_specific(
                i_s,
                definition,
                point.specific(),
                callable,
                reducer,
                on_missing,
                on_type_var,
            ),
            PointType::Complex => {
                let complex = definition.file.complex_points.get(point.complex_index());
                if let ComplexPoint::Class(cls_storage) = complex {
                    let class =
                        Class::new(*definition, &cls_storage.symbol_table, Generics::None, None);
                    callable(i_s, &class)
                } else {
                    self.run_on_complex(
                        i_s,
                        complex,
                        Some(definition),
                        callable,
                        reducer,
                        on_missing,
                        on_type_var,
                    )
                }
            }
            PointType::Unknown => on_missing(i_s, self.clone()),
            PointType::FileReference => {
                let f = i_s.database.loaded_python_file(point.file_index());
                callable(i_s, &Module::new(i_s.database, f))
            }
            _ => unreachable!(),
        }
    }

    #[inline]
    fn run_on_specific<'a, T>(
        &'a self,
        i_s: &mut InferenceState<'db, '_>,
        definition: &NodeReference<'db>,
        specific: Specific,
        callable: &mut impl FnMut(&mut InferenceState<'db, '_>, &dyn Value<'db, 'a>) -> T,
        reducer: &impl Fn(T, T) -> T,
        on_missing: &mut impl FnMut(&mut InferenceState<'db, '_>, Self) -> T,
        on_type_var: &mut impl FnMut(TypeVarIndex, NodeReference<'db>) -> T,
    ) -> T {
        match specific {
            Specific::Function => callable(i_s, &Function::new(*definition, None)),
            Specific::AnnotationInstance => {
                let inferred = definition
                    .file
                    .inference(i_s)
                    .infer_annotation_expression_class(definition.as_expression());
                inferred.with_instance(i_s, self, None, |i_s, instance| {
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
                let (init, generics) = class.init_func(i_s, &args);
                debug_assert!(generics.is_none());
                inf_cls.with_instance(i_s, self, None, |i_s, instance| {
                    // TODO is this MroIndex correct?
                    let args = InstanceArguments::new(instance, MroIndex(0), &args);
                    callable(&mut i_s.with_func_and_args(&init, &args), instance)
                })
            }
            Specific::SimpleGeneric => {
                let class = self.maybe_class(i_s).unwrap();
                callable(i_s, &class)
            }
            Specific::List => callable(i_s, &ListLiteral::new(*definition)),
            Specific::Dict => callable(i_s, &DictLiteral::new(*definition)),
            Specific::TypingProtocol
            | Specific::TypingGeneric
            | Specific::TypingTuple
            | Specific::TypingUnion
            | Specific::TypingOptional
            | Specific::TypingType
            | Specific::TypingCallable => callable(i_s, &TypingClass::new(*definition, specific)),
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
            Specific::TypingCast => callable(i_s, &TypingCast()),
            Specific::TypingClassVar => callable(i_s, &TypingClassVar()),
            Specific::ClassTypeVar | Specific::FunctionTypeVar | Specific::FreeTypeVar => {
                on_type_var(definition.point().type_var_index(), *definition)
            }
            Specific::None => callable(i_s, &NoneInstance()),
            _ => {
                let instance = self.resolve_specific(i_s.database, specific);
                callable(i_s, &instance)
            }
        }
    }

    fn run_on_complex<'a, T>(
        &'a self,
        i_s: &mut InferenceState<'db, '_>,
        complex: &'a ComplexPoint,
        definition: Option<&NodeReference<'db>>,
        callable: &mut impl FnMut(&mut InferenceState<'db, '_>, &dyn Value<'db, 'a>) -> T,
        reducer: &impl Fn(T, T) -> T,
        on_missing: &mut impl FnMut(&mut InferenceState<'db, '_>, Self) -> T,
        on_type_var: &mut impl FnMut(TypeVarIndex, NodeReference<'db>) -> T,
    ) -> T {
        match complex {
            ComplexPoint::ExecutionInstance(cls_definition, execution) => {
                let def = NodeReference::from_link(i_s.database, *cls_definition);
                let init = Function::from_execution(i_s.database, execution, None);
                let complex = def.complex().unwrap();
                if let ComplexPoint::Class(cls_storage) = complex {
                    let args = SimpleArguments::from_execution(i_s.database, execution);
                    let class = Class::new(def, &cls_storage.symbol_table, Generics::None, None);
                    debug_assert!(class.type_vars(i_s).is_empty());
                    let instance = Instance::new(class, self);
                    // TODO is this MroIndex fine? probably not!
                    let args = InstanceArguments::new(&instance, MroIndex(0), &args);
                    callable(&mut i_s.with_func_and_args(&init, &args), &instance)
                } else {
                    unreachable!()
                }
            }
            ComplexPoint::Union(lst) => lst
                .iter()
                .map(|any_link| match any_link {
                    AnyLink::Reference(link) => {
                        let reference = NodeReference::from_link(i_s.database, *link);
                        self.run_on_saved(
                            i_s,
                            &reference,
                            reference.point(),
                            callable,
                            reducer,
                            on_missing,
                            on_type_var,
                        )
                    }
                    AnyLink::Complex(c) => self.run_on_complex(
                        i_s,
                        c,
                        definition,
                        callable,
                        reducer,
                        on_missing,
                        on_type_var,
                    ),
                    AnyLink::SimpleSpecific(specific) => match specific {
                        Specific::None => callable(i_s, &NoneInstance()),
                        _ => todo!("not even sure if this should be a separate class"),
                    },
                })
                .reduce(reducer)
                .unwrap(),
            ComplexPoint::BoundMethod(instance_link, mro_index, func_link) => {
                let reference = NodeReference::from_link(i_s.database, *func_link);

                // TODO this is potentially not needed, a class could lazily be fetched with a
                // closure
                let inf = Inferred::from_any_link(i_s.database, instance_link);
                let instance = inf.expect_instance(i_s);

                let class = instance.class.mro(i_s).nth(mro_index.0 as usize).unwrap().1;
                let class = match class {
                    ClassLike::Class(c) => c,
                    _ => unreachable!(),
                };
                if let Some(ComplexPoint::FunctionOverload(overload)) = reference.complex() {
                    let func = OverloadedFunction::new(reference, overload, Some(&class));
                    callable(i_s, &BoundMethod::new(&instance, *mro_index, &func))
                } else {
                    let func = Function::new(reference, Some(&class));
                    callable(i_s, &BoundMethod::new(&instance, *mro_index, &func))
                }
            }
            ComplexPoint::Closure(function, execution) => {
                let f = i_s.database.loaded_python_file(function.file);
                let func = Function::from_execution(i_s.database, execution, None);
                let args = SimpleArguments::from_execution(i_s.database, execution);
                callable(
                    &mut i_s.with_func_and_args(&func, &args),
                    &Function::new(NodeReference::from_link(i_s.database, *function), None),
                )
            }
            ComplexPoint::Instance(cls, generics_list) => {
                let generics = generics_list
                    .as_ref()
                    .map(Generics::List)
                    .unwrap_or(Generics::None);
                let instance =
                    self.use_instance(NodeReference::from_link(i_s.database, *cls), generics);
                callable(i_s, &instance)
            }
            ComplexPoint::FunctionOverload(overload) => callable(
                i_s,
                &OverloadedFunction::new(*definition.unwrap(), overload, None),
            ),
            ComplexPoint::GenericClass(link, generics) => {
                let class = Class::from_position(
                    NodeReference::from_link(i_s.database, *link),
                    Generics::List(generics),
                    None,
                )
                .unwrap();
                callable(i_s, &class)
            }
            ComplexPoint::TupleClass(content) => callable(i_s, &TupleClass::new(content)),
            ComplexPoint::Tuple(content) => callable(i_s, &Tuple::new(content)),
            ComplexPoint::CallableClass(content) => callable(i_s, &CallableClass::new(content)),
            ComplexPoint::Callable(content) => callable(i_s, &Callable::new(content)),
            ComplexPoint::Type(generic_part) => {
                callable(i_s, &TypingType::new(i_s.database, generic_part))
            }
            _ => {
                unreachable!("Classes are handled earlier {:?}", complex)
            }
        }
    }

    pub fn run_on_value(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        callable: &mut impl Fn(&mut InferenceState<'db, '_>, &dyn Value<'db, '_>) -> Self,
    ) -> Self {
        self.internal_run(
            i_s,
            callable,
            &|i1, i2| i1.union(i2),
            &mut |i_s, inferred| inferred,
            &mut |_, point| todo!(),
        )
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
                ValueNameIterator::Single(callable(&WithValueName::new(i_s.database, value)))
            },
            &|iter1, iter2| {
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
            &mut |i_s, inferred| ValueNameIterator::Finished,
            &mut |_, p| todo!(),
        )
    }

    pub fn run_mut(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        callable: &mut impl for<'a, 'b, 'c> FnMut(&mut InferenceState<'db, 'c>, &'b dyn Value<'db, 'a>),
        mut on_missing: impl FnMut(),
    ) {
        self.internal_run(
            i_s,
            callable,
            &|i1, i2| (),
            &mut |i_s, inferred| on_missing(),
            &mut |_, p| todo!(),
        )
    }

    fn resolve_specific(&self, database: &'db Database, specific: Specific) -> Instance<'db, '_> {
        self.load_builtin_instance_from_str(
            database,
            match specific {
                Specific::String => "str",
                Specific::Integer => "int",
                Specific::Float => "float",
                Specific::Boolean => "bool",
                Specific::Bytes => "bytes",
                Specific::Complex => "complex",
                Specific::Ellipsis => "ellipsis", // TODO this should not even be public
                actual => todo!("{:?}", actual),
            },
        )
    }

    fn load_builtin_instance_from_str(
        &self,
        database: &'db Database,
        name: &'static str,
    ) -> Instance<'db, '_> {
        let builtins = database.python_state.builtins();
        let node_index = builtins.lookup_global(name).unwrap().node_index;
        let v = builtins.points.get(node_index);
        debug_assert_eq!(v.type_(), PointType::Redirect);
        debug_assert_eq!(v.file_index(), builtins.file_index());
        self.use_instance(NodeReference::new(builtins, v.node_index()), Generics::None)
    }

    pub fn maybe_type_var(&self, i_s: &mut InferenceState<'db, '_>) -> Option<NodeReference<'db>> {
        if let InferredState::Saved(definition, point) = self.state {
            if point.type_() == PointType::Specific
                && point.specific() == Specific::InstanceWithArguments
            {
                // TODO this check can/should be optimized by comparing node pointers that are cached
                // in python_state
                let cls = self.infer_instance_with_arguments_cls(i_s, &definition);
                if let InferredState::Saved(cls_definition, _) = cls.state {
                    if cls_definition.file.file_index()
                        == i_s.database.python_state.typing().file_index()
                        && cls_definition
                            .maybe_class()
                            .map(|cls| cls.name().as_str() == "TypeVar")
                            .unwrap_or(false)
                    {
                        return Some(definition);
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
                        let (init, generics) = class.init_func(i_s, &args);
                        debug_assert!(generics.is_none());
                        return Inferred::new_unsaved_complex(ComplexPoint::ExecutionInstance(
                            inf_cls.get_saved().unwrap().0.as_link(),
                            Box::new(args.as_execution(&init)),
                        ));
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
        definition: &NodeReference<'db>,
    ) -> Self {
        definition
            .file
            .inference(i_s)
            .infer_primary_or_atom(definition.as_primary().first())
    }

    fn with_instance<'a, T>(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        instance: &'a Self,
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
                        unreachable!("{:?}", point)
                    }
                } else {
                    callable(
                        i_s,
                        &instance.use_instance(*definition, generics.unwrap_or(Generics::None)),
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

    fn use_instance<'a>(
        &'a self,
        reference: NodeReference<'db>,
        generics: Generics<'db, 'a>,
    ) -> Instance<'db, 'a> {
        let class = Class::from_position(reference, generics, None).unwrap();
        Instance::new(class, self)
    }

    pub fn maybe_class(&self, i_s: &mut InferenceState<'db, '_>) -> Option<Class<'db, '_>> {
        let mut generics = Generics::None;
        if let InferredState::Saved(definition, point) = &self.state {
            if point.type_() == PointType::Specific {
                generics = self.expect_generics().unwrap_or(Generics::None);
            }
        }
        self.maybe_class_internal(i_s, generics)
    }

    pub fn maybe_class_like(
        &self,
        i_s: &mut InferenceState<'db, '_>,
    ) -> Option<ClassLike<'db, '_>> {
        let mut generics = Generics::None;
        if let InferredState::Saved(definition, point) = &self.state {
            if point.type_() == PointType::Specific {
                generics = self.expect_generics().unwrap_or(Generics::None);
            }
        }
        self.maybe_class_internal(i_s, generics)
            .map(ClassLike::Class)
            .or_else(|| match &self.state {
                InferredState::Saved(definition, point) if point.type_() == PointType::Complex => {
                    let complex = definition.file.complex_points.get(point.complex_index());
                    if let ComplexPoint::TupleClass(content) = complex {
                        Some(ClassLike::Tuple(TupleClass::new(content)))
                    } else {
                        None
                    }
                }
                InferredState::UnsavedComplex(ComplexPoint::Tuple(content)) => {
                    Some(ClassLike::Tuple(TupleClass::new(content)))
                }
                _ => None,
            })
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
                        Some(Class::new(*definition, &c.symbol_table, generics, None))
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
                _ => todo!(),
            },
            InferredState::UnsavedComplex(complex) => {
                if let ComplexPoint::TupleClass(_) = complex {
                    return None;
                }
                todo!("{:?}", complex)
            }
            InferredState::UnsavedSpecific(specific) => todo!(),
            InferredState::Unknown => None,
        }
    }

    pub fn expect_int(&self) -> Option<i64> {
        if let InferredState::Saved(definition, point) = self.state {
            if let PointType::Specific = point.type_() {
                if let Specific::Integer = point.specific() {
                    return definition.infer_int();
                }
            }
        }
        None
    }

    pub fn save_redirect(self, file: &'db PythonFile, index: NodeIndex) -> Self {
        // TODO this locality should be calculated in a more correct way
        match &self.state {
            InferredState::Saved(definition, point) => {
                if file.points.get(index).calculated() {
                    todo!("{:?} {:?}", file.points.get(index), index);
                }
                file.points.set(
                    index,
                    Point::new_redirect(
                        definition.file.file_index(),
                        definition.node_index,
                        Locality::Stmt,
                    ),
                );
                self
            }
            InferredState::UnsavedComplex(complex) => {
                file.complex_points
                    .insert(&file.points, index, complex.clone());
                Self::new_saved(file, index, file.points.get(index))
            }
            InferredState::UnsavedSpecific(specific) => {
                let point = Point::new_simple_specific(*specific, Locality::Stmt);
                file.points.set(index, point);
                Self::new_saved(file, index, point)
            }
            InferredState::Unknown => todo!(),
        }
    }

    pub fn init_as_function<'a>(
        &self,
        class: &'a Class<'db, 'a>,
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

    fn get_saved(&self) -> Option<(NodeReference<'db>, Point)> {
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
                    InferredState::Unknown => todo!(),
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

    pub fn as_file_index(&self) -> Option<FileIndex> {
        if let InferredState::Saved(reference, point) = self.state {
            if matches!(point.type_(), PointType::FileReference) {
                return Some(point.file_index());
            }
        }
        None
    }

    #[inline]
    pub fn bind(
        self,
        i_s: &InferenceState<'db, '_>,
        instance: &Instance<'db, '_>,
        mro_index: MroIndex,
    ) -> Self {
        match &self.state {
            InferredState::Saved(definition, point) => match point.type_() {
                PointType::Specific => {
                    if point.specific() == Specific::Function {
                        let complex = ComplexPoint::BoundMethod(
                            instance.as_inferred().as_any_link(i_s),
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
                            instance.as_inferred().as_any_link(i_s),
                            mro_index,
                            definition.as_link(),
                        );
                        return Self::new_unsaved_complex(complex);
                    } else {
                        todo!()
                    }
                }
                _ => (),
            },
            InferredState::UnsavedComplex(complex) => {
                todo!()
            }
            InferredState::UnsavedSpecific(specific) => todo!(),
            InferredState::Unknown => (),
        }
        self
    }

    pub fn description(&self, i_s: &mut InferenceState<'db, '_>) -> String {
        self.internal_run(
            i_s,
            &mut |i_s, v| v.description(i_s),
            &|i1, i2| format!("{}|{}", i1, i2),
            &mut |i_s, inferred| "Unknown".to_owned(),
            &mut |_, node_ref| {
                format!(
                    "{:?} {:?}",
                    node_ref.point().specific(),
                    node_ref.point().type_var_index()
                )
            },
        )
    }

    pub fn debug_info(&self, i_s: &mut InferenceState<'db, '_>) -> String {
        let details = match &self.state {
            InferredState::Saved(definition, point) => {
                format!(
                    "{} (complex?: {:?})",
                    definition.file.file_path(i_s.database),
                    definition.complex(),
                )
            }
            _ => "".to_owned(),
        };
        format!(
            "description = {}\ndebug = {:?}\ndetails = {}",
            self.description(i_s),
            self,
            details
        )
    }

    pub fn as_any_link(&self, i_s: &InferenceState<'db, '_>) -> AnyLink {
        match &self.state {
            InferredState::Saved(definition, _) => AnyLink::Reference(definition.as_link()),
            InferredState::UnsavedComplex(complex) => AnyLink::Complex(Box::new(complex.clone())),
            InferredState::UnsavedSpecific(specific) => todo!(),
            InferredState::Unknown => todo!(),
        }
    }

    fn from_any_link(database: &'db Database, any: &AnyLink) -> Self {
        match any {
            AnyLink::Reference(def) => {
                let file = database.loaded_python_file(def.file);
                Self::new_saved(file, def.node_index, file.points.get(def.node_index))
            }
            AnyLink::Complex(complex) => Self::new_unsaved_complex(*complex.clone()),
            AnyLink::SimpleSpecific(_) => todo!(),
        }
    }

    fn expect_generics(&self) -> Option<Generics<'db, '_>> {
        if let InferredState::Saved(definition, point) = self.state {
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
        }
        None
    }

    pub fn is_simple_class(&self, i_s: &mut InferenceState<'db, '_>) -> bool {
        self.internal_run(
            i_s,
            &mut |i_s, v| v.as_class().is_some(),
            &|i1, i2| false,
            &mut |i_s, inferred| false,
            &mut |_, p| false,
        )
    }

    pub fn is_unknown(&self) -> bool {
        match &self.state {
            InferredState::Saved(_, point) => matches!(point.type_(), PointType::Unknown),
            InferredState::Unknown => true,
            _ => false,
        }
    }

    pub fn execute_function(&self, i_s: &mut InferenceState<'db, '_>, name: &str) -> Inferred<'db> {
        self.run_on_value(i_s, &mut |i_s, value| value.lookup(i_s, name))
            .run_on_value(i_s, &mut |i_s, value| value.execute(i_s, &NoArguments()))
    }

    pub fn iter(&self, i_s: &mut InferenceState<'db, '_>) -> IteratorContent<'db> {
        self.internal_run(
            i_s,
            &mut |i_s, v| v.iter(i_s),
            &|i1, i2| todo!(),
            &mut |i_s, inferred| IteratorContent::Inferred(inferred),
            &mut |_, p| IteratorContent::Inferred(Self::new_unknown()),
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
            InferredState::UnsavedSpecific(specific) => todo!(),
            InferredState::Unknown => s.field("unknown", &true),
        }
        .finish()
    }
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
