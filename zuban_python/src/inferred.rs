use parsa_python_ast::{
    Atom, AtomContent, ClassDef, Expression, Name, NamedExpression, NodeIndex, Primary,
    PrimaryContent, SimpleParamType,
};
use std::fmt;

use crate::arguments::{Arguments, InstanceArguments, SimpleArguments};
use crate::database::{
    AnyLink, ComplexPoint, Database, FileIndex, GenericPart, GenericsList, Locality, Point,
    PointLink, PointType, Specific,
};
use crate::debug;
use crate::file::PythonFile;
use crate::file_state::File;
use crate::generics::Generics;
use crate::inference_state::InferenceState;
use crate::name::{ValueName, ValueNameIterator, WithValueName};
use crate::value::{
    BoundMethod, Class, ClassLike, DictLiteral, Function, Instance, ListLiteral, Module,
    OverloadedFunction, Tuple, TupleClass, TypingClass, TypingWithGenerics, Value,
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

    pub fn maybe_infer_param_annotation(
        &self,
        i_s: &mut InferenceState<'db, '_>,
    ) -> Option<Inferred<'db>> {
        let name = self.as_name();
        name.maybe_param_annotation().map(|annotation| {
            let expression = annotation.expression();
            let mut inference = self.file.inference(i_s);
            match name.simple_param_type() {
                SimpleParamType::Normal => inference.infer_annotation_expression(expression),
                SimpleParamType::MultiArgs => {
                    let inf = inference.infer_expression(expression);
                    Inferred::create_instance(
                        i_s.database.python_state.builtins_point_link("tuple"),
                        Some(&[inf.as_generic_part(i_s)]),
                    )
                }
                SimpleParamType::MultiKwargs => {
                    let inf = inference.infer_expression(expression);
                    Inferred::create_instance(
                        i_s.database.python_state.builtins_point_link("dict"),
                        Some(&[
                            GenericPart::Class(
                                i_s.database.python_state.builtins_point_link("str"),
                            ),
                            inf.as_generic_part(i_s),
                        ]),
                    )
                }
            }
        })
    }
}

pub enum FunctionOrOverload<'db, 'a> {
    Function(Function<'db>),
    Overload(OverloadedFunction<'db, 'a>),
}

#[derive(Debug, Clone, PartialEq)]
enum InferredState<'db> {
    Saved(NodeReference<'db>, Point),
    UnsavedComplex(ComplexPoint),
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

    pub fn from_generic_class(db: &'db Database, generic: &GenericPart) -> Self {
        let state = match generic {
            GenericPart::Class(link) => {
                let node_reference = NodeReference::from_link(db, *link);
                InferredState::Saved(node_reference, node_reference.point())
            }
            GenericPart::GenericClass(l, g) => {
                InferredState::UnsavedComplex(ComplexPoint::GenericClass(*l, g.clone()))
            }
            GenericPart::Union(multiple) => {
                let mut multiple = multiple.iter();
                let mut inferred = Self::from_generic_class(db, multiple.next().unwrap());
                for m in multiple {
                    inferred = inferred.union(Self::from_generic_class(db, m));
                }
                return inferred;
            }
            GenericPart::Tuple(content) => {
                todo!()
            }
            GenericPart::Callable(content) => {
                todo!()
            }
            GenericPart::Type(_) => {
                todo!()
            }
            GenericPart::Unknown | GenericPart::TypeVar(_) => InferredState::Unknown,
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
        self.maybe_numbered_type_var()
            .map(|p| GenericPart::TypeVar(p.type_var_index()))
            .unwrap_or_else(|| {
                self.internal_run(
                    i_s,
                    &mut |i_s, v| {
                        v.as_class()
                            .map(|c| c.as_generic_part(i_s))
                            .or_else(|| v.as_tuple_class().map(|c| c.as_generic_part()))
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
                )
            })
    }

    #[inline]
    pub fn internal_run<T>(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        callable: &mut impl FnMut(&mut InferenceState<'db, '_>, &dyn Value<'db>) -> T,
        reducer: &impl Fn(T, T) -> T,
        on_missing: &mut impl FnMut(&mut InferenceState<'db, '_>, Self) -> T,
    ) -> T {
        match &self.state {
            InferredState::Saved(definition, point) => match point.type_() {
                PointType::Specific => {
                    let specific = point.specific();
                    match specific {
                        Specific::Function => callable(i_s, &Function::new(*definition)),
                        Specific::AnnotationInstance => {
                            let inferred = definition
                                .file
                                .inference(i_s)
                                .infer_expression_no_save(definition.as_expression());
                            let annotation_generics = inferred.expect_generics();
                            let generics = annotation_generics.unwrap_or(Generics::None);
                            inferred.with_instance(i_s, self, generics, |i_s, instance| {
                                callable(&mut i_s.with_annotation_instance(), instance)
                            })
                        }
                        Specific::InstanceWithArguments => {
                            let inf_cls = self.infer_instance_with_arguments_cls(i_s, definition);
                            let class = inf_cls.expect_class(i_s).unwrap();
                            let args = SimpleArguments::from_primary(
                                definition.file,
                                definition.as_primary(),
                                None,
                                Some(&class),
                            );
                            let (init, generics) = class.init_func(i_s, &args);
                            debug_assert!(generics.is_none());
                            inf_cls.with_instance(i_s, self, Generics::None, |i_s, instance| {
                                let args = InstanceArguments::new(instance, &args);
                                callable(&mut i_s.with_func_and_args(&init, &args), instance)
                            })
                        }
                        Specific::SimpleGeneric => {
                            let class = self.expect_class(i_s).unwrap();
                            callable(i_s, &class)
                        }
                        Specific::Param => i_s
                            .infer_param(definition)
                            .internal_run(i_s, callable, reducer, on_missing),
                        Specific::List => callable(i_s, &ListLiteral::new(definition)),
                        Specific::Dict => callable(i_s, &DictLiteral::new(definition)),
                        Specific::TypingProtocol
                        | Specific::TypingGeneric
                        | Specific::TypingTuple
                        | Specific::TypingCallable => {
                            callable(i_s, &TypingClass::new(*definition, specific))
                        }
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
                        Specific::ClassTypeVar | Specific::FunctionTypeVar => {
                            on_missing(i_s, self.clone())
                        }
                        _ => {
                            let instance = self.resolve_specific(i_s.database, specific);
                            callable(i_s, &instance)
                        }
                    }
                }
                PointType::Complex => {
                    let complex = definition.file.complex_points.get(point.complex_index());
                    if let ComplexPoint::Class(cls_storage) = complex {
                        let class = Class::new(
                            *definition,
                            &cls_storage.symbol_table,
                            Generics::None,
                            None,
                        );
                        callable(i_s, &class)
                    } else {
                        self.run_on_complex(i_s, complex, Some(definition), callable, reducer)
                    }
                }
                PointType::Unknown => on_missing(i_s, self.clone()),
                PointType::FileReference => {
                    let f = i_s.database.loaded_python_file(point.file_index());
                    callable(i_s, &Module::new(f))
                }
                _ => unreachable!(),
            },
            InferredState::UnsavedComplex(complex) => {
                self.run_on_complex(i_s, complex, None, callable, reducer)
            }
            InferredState::Unknown => on_missing(i_s, self.clone()),
        }
    }

    #[inline]
    fn run_on_complex<T>(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        complex: &ComplexPoint,
        definition: Option<&NodeReference<'db>>,
        callable: &mut impl FnMut(&mut InferenceState<'db, '_>, &dyn Value<'db>) -> T,
        reducer: &impl Fn(T, T) -> T,
    ) -> T {
        match complex {
            ComplexPoint::ExecutionInstance(cls_definition, execution) => {
                let def = NodeReference::from_link(i_s.database, *cls_definition);
                let init = Function::from_execution(i_s.database, execution);
                let complex = def.complex().unwrap();
                if let ComplexPoint::Class(cls_storage) = complex {
                    let args = SimpleArguments::from_execution(i_s.database, execution);
                    let class = Class::new(def, &cls_storage.symbol_table, Generics::None, None);
                    debug_assert!(class.type_vars(i_s).is_empty());
                    let instance = Instance::new(class, self);
                    let args = InstanceArguments::new(&instance, &args);
                    callable(&mut i_s.with_func_and_args(&init, &args), &instance)
                } else {
                    unreachable!()
                }
            }
            ComplexPoint::Union(lst) => lst
                .iter()
                .map(|&p| {
                    let node_ref = NodeReference::from_link(i_s.database, p);
                    let point = node_ref.point();
                    Inferred {
                        state: InferredState::Saved(node_ref, point),
                    }
                    .internal_run(
                        i_s,
                        callable,
                        reducer,
                        &mut |i_s, i| unreachable!(),
                    )
                })
                .reduce(reducer)
                .unwrap(),
            ComplexPoint::BoundMethod(instance_link, func_link) => {
                let reference = NodeReference::from_link(i_s.database, *func_link);

                if let Some(ComplexPoint::FunctionOverload(overload)) = reference.complex() {
                    let func = OverloadedFunction::new(reference, overload);
                    callable(i_s, &BoundMethod::new(instance_link, &func))
                } else {
                    let func = Function::new(reference);
                    callable(i_s, &BoundMethod::new(instance_link, &func))
                }
            }
            ComplexPoint::Closure(function, execution) => {
                let f = i_s.database.loaded_python_file(function.file);
                let func = Function::from_execution(i_s.database, execution);
                let args = SimpleArguments::from_execution(i_s.database, execution);
                callable(
                    &mut i_s.with_func_and_args(&func, &args),
                    &Function::new(NodeReference::from_link(i_s.database, *function)),
                )
            }
            ComplexPoint::Instance(cls, generics_list) => {
                let generics = generics_list
                    .as_ref()
                    .map(|l| Generics::List(l))
                    .unwrap_or(Generics::None);
                let instance =
                    self.use_instance(NodeReference::from_link(i_s.database, *cls), generics);
                callable(i_s, &instance)
            }
            ComplexPoint::FunctionOverload(overload) => callable(
                i_s,
                &OverloadedFunction::new(*definition.unwrap(), overload),
            ),
            ComplexPoint::GenericClass(cls, bla) => {
                todo!()
            }
            ComplexPoint::TupleClass(content) => callable(i_s, &TupleClass::new(content)),
            ComplexPoint::Tuple(content) => callable(i_s, &Tuple::new(content)),
            _ => {
                unreachable!("Classes are handled earlier {:?}", complex)
            }
        }
    }

    #[inline]
    pub fn run_on_value(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        callable: &mut impl Fn(&mut InferenceState<'db, '_>, &dyn Value<'db>) -> Self,
    ) -> Self {
        self.internal_run(
            i_s,
            callable,
            &|i1, i2| i1.union(i2),
            &mut |i_s, inferred| inferred,
        )
    }

    #[inline]
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
        )
    }

    #[inline]
    pub fn run(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        callable: &mut impl FnMut(&mut InferenceState<'db, '_>, &dyn Value<'db>),
        mut on_missing: impl FnMut(),
    ) {
        self.internal_run(i_s, callable, &|i1, i2| (), &mut |i_s, inferred| {
            on_missing()
        })
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

    pub fn maybe_numbered_type_var(&self) -> Option<Point> {
        if let InferredState::Saved(definition, point) = self.state {
            if point.type_() == PointType::Specific {
                if matches!(
                    point.specific(),
                    Specific::FunctionTypeVar | Specific::ClassTypeVar
                ) {
                    return Some(point);
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
                        let class = inf_cls.expect_class(i_s).unwrap();
                        debug_assert!(class.type_vars(i_s).is_empty());
                        let args = SimpleArguments::from_primary(
                            definition.file,
                            definition.as_primary(),
                            None,
                            Some(&class),
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
                        return i_s.infer_param(&definition);
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

    fn with_instance<T>(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        instance: &Self,
        generics: Generics<'db, '_>,
        callable: impl FnOnce(&mut InferenceState<'db, '_>, &Instance<'db, '_>) -> T,
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
                        cls.with_instance(i_s, instance, generics, callable)
                    } else {
                        unreachable!("{:?}", point)
                    }
                } else {
                    callable(i_s, &instance.use_instance(*definition, generics))
                }
            }
            InferredState::UnsavedComplex(complex) => {
                todo!("{:?}", complex)
            }
            InferredState::Unknown => unreachable!(),
        }
    }

    fn use_instance<'a>(
        &'a self,
        reference: NodeReference<'db>,
        generics: Generics<'db, 'a>,
    ) -> Instance<'db, 'a> {
        let class = Class::from_position(reference, generics, None).unwrap();
        Instance::new(class, self)
    }

    pub fn expect_class(&self, i_s: &mut InferenceState<'db, '_>) -> Option<Class<'db, '_>> {
        let mut generics = Generics::None;
        if let InferredState::Saved(definition, point) = &self.state {
            if point.type_() == PointType::Specific {
                generics = self.expect_generics().unwrap_or(Generics::None);
            }
        }
        self.expect_class_internal(i_s, generics)
    }

    pub fn expect_class_like(
        &self,
        i_s: &mut InferenceState<'db, '_>,
    ) -> Option<ClassLike<'db, '_>> {
        let mut generics = Generics::None;
        if let InferredState::Saved(definition, point) = &self.state {
            if point.type_() == PointType::Specific {
                generics = self.expect_generics().unwrap_or(Generics::None);
            }
        }
        self.expect_class_internal(i_s, generics)
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

    fn expect_class_internal<'a>(
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
                        inferred.expect_class_internal(i_s, generics)
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
            InferredState::Unknown => unreachable!(),
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
            InferredState::Unknown => todo!(),
        }
    }

    pub fn init_as_function(&self) -> Option<FunctionOrOverload<'db, '_>> {
        if let InferredState::Saved(definition, point) = &self.state {
            if let Some(Specific::Function) = point.maybe_specific() {
                return Some(FunctionOrOverload::Function(Function::new(*definition)));
            }
            if let Some(ComplexPoint::FunctionOverload(overload)) = definition.complex() {
                return Some(FunctionOrOverload::Overload(OverloadedFunction::new(
                    *definition,
                    overload,
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
            let insert = |list: &mut Vec<PointLink>, state| {
                match state {
                    InferredState::Saved(definition, _) => {
                        list.push(definition.as_link());
                    }
                    InferredState::UnsavedComplex(complex) => match complex {
                        ComplexPoint::Union(lst) => {
                            list.extend(lst.iter());
                        }
                        _ => todo!("{:?}", complex),
                    },
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
        // TODO currently unused?!
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
    pub fn bind(self, i_s: &InferenceState<'db, '_>, instance: &Instance<'db, '_>) -> Self {
        match &self.state {
            InferredState::Saved(definition, point) => match point.type_() {
                PointType::Specific => {
                    if point.specific() == Specific::Function {
                        let complex = ComplexPoint::BoundMethod(
                            instance.as_inferred().as_any_link(i_s),
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
            InferredState::Unknown => todo!(),
        }
    }

    pub fn from_any_link(database: &'db Database, any: &AnyLink) -> Self {
        match any {
            AnyLink::Reference(def) => {
                let file = database.loaded_python_file(def.file);
                Self::new_saved(file, def.node_index, file.points.get(def.node_index))
            }
            AnyLink::Complex(complex) => Self::new_unsaved_complex(*complex.clone()),
            AnyLink::Specific(_) => todo!(),
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

    pub fn is_class(&self, i_s: &mut InferenceState<'db, '_>) -> bool {
        self.internal_run(
            i_s,
            &mut |i_s, v| v.as_class().is_some(),
            &|i1, i2| i1 & i2,
            &mut |i_s, inferred| false,
        )
    }

    pub fn is_unknown(&self) -> bool {
        match &self.state {
            InferredState::Saved(_, point) => matches!(point.type_(), PointType::Unknown),
            InferredState::Unknown => true,
            _ => false,
        }
    }

    pub fn execute_annotation_class(&self, i_s: &mut InferenceState<'db, '_>) -> Self {
        match &self.state {
            InferredState::Saved(definition, point) => match point.type_() {
                PointType::Specific => {
                    let specific = point.specific();
                    match specific {
                        Specific::SimpleGeneric => {
                            let class = self.expect_class(i_s).unwrap();
                            class.reference.as_link();
                            todo!()
                        }
                        _ => {
                            todo!("{:?}", self)
                        }
                    }
                }
                PointType::Complex => {
                    let complex = definition.file.complex_points.get(point.complex_index());
                    match complex {
                        ComplexPoint::Class(cls_storage) => {
                            let class = Class::new(
                                *definition,
                                &cls_storage.symbol_table,
                                Generics::None,
                                None,
                            );
                            if class.type_vars(i_s).is_empty() {
                                Inferred::new_unsaved_complex(ComplexPoint::Instance(
                                    definition.as_link(),
                                    None,
                                ))
                            } else {
                                todo!();
                            }
                        }
                        ComplexPoint::GenericClass(foo, bla) => {
                            todo!()
                        }
                        _ => todo!(),
                    }
                }
                _ => todo!("{}", self.debug_info(i_s)),
            },
            InferredState::UnsavedComplex(complex) => {
                todo!("{}", self.debug_info(i_s))
            }
            InferredState::Unknown => self.clone(),
        }
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
