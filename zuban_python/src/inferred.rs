use once_cell::unsync::OnceCell;
use parsa_python_ast::{
    Atom, AtomContent, ClassDef, Expression, NamedExpression, NodeIndex, Primary, PrimaryContent,
};
use std::fmt;

use crate::arguments::{Arguments, InstanceArguments, SimpleArguments};
use crate::database::{
    AnyLink, ComplexPoint, Database, FileIndex, GenericPart, Locality, Point, PointLink, PointType,
    Specific,
};
use crate::file::PythonFile;
use crate::file_state::File;
use crate::generics::Generics;
use crate::inference_state::InferenceState;
use crate::name::{ValueName, ValueNameIterator, WithValueName};
use crate::value::{
    BoundMethod, Class, Function, Instance, ListLiteral, Module, TypingClass, TypingWithGenerics,
    Value, ValueKind,
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
    pub fn from_link(database: &'db Database, point: PointLink) -> Self {
        let file = database.get_loaded_python_file(point.file);
        Self {
            file,
            node_index: point.node_index,
        }
    }

    fn get_point(&self) -> Point {
        self.file.points.get(self.node_index)
    }

    fn get_complex(&self) -> Option<&'db ComplexPoint> {
        let point = self.get_point();
        if let PointType::Complex = point.get_type() {
            Some(self.file.complex_points.get(point.get_complex_index()))
        } else {
            None
        }
    }

    pub fn as_link(&self) -> PointLink {
        PointLink::new(self.file.get_file_index(), self.node_index)
    }

    fn as_expression(&self) -> Expression<'db> {
        Expression::by_index(&self.file.tree, self.node_index)
    }

    pub fn as_primary(&self) -> Primary<'db> {
        Primary::by_index(&self.file.tree, self.node_index)
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
}

#[derive(Debug, Clone, PartialEq)]
enum InferredState<'db> {
    Saved(NodeReference<'db>, Point),
    UnsavedComplex(ComplexPoint),
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

    pub fn from_generic_class(db: &'db Database, generic: &'db GenericPart) -> Self {
        let state = match generic {
            GenericPart::Class(link) => {
                let node_reference = NodeReference::from_link(db, *link);
                InferredState::Saved(node_reference, node_reference.get_point())
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
            GenericPart::Unknown => {
                todo!()
            }
        };
        Self { state }
    }

    #[inline]
    pub fn internal_run<T>(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        callable: &mut impl FnMut(&mut InferenceState<'db, '_>, &dyn Value<'db>) -> T,
        reducer: &impl Fn(T, T) -> T,
        on_missing: &impl Fn(Inferred<'db>) -> T,
    ) -> T {
        match &self.state {
            InferredState::Saved(definition, point) => match point.get_type() {
                PointType::Specific => {
                    let specific = point.specific();
                    match specific {
                        Specific::Function => {
                            callable(i_s, &Function::new(definition.file, definition.node_index))
                        }
                        Specific::AnnotationInstance => {
                            let inferred = definition
                                .file
                                .get_inference(i_s)
                                .infer_expression_no_save(definition.as_expression());
                            let annotation_generics = inferred.expect_generics();
                            let generics = annotation_generics.unwrap_or(Generics::None);
                            inferred.with_instance(i_s, self, generics, |i_s, instance| {
                                callable(&mut i_s.with_annotation_instance(), instance)
                            })
                        }
                        Specific::InstanceWithArguments => {
                            let cls = self.infer_instance_with_arguments_cls(i_s, definition);
                            let args = SimpleArguments::from_primary(
                                definition.file,
                                definition.as_primary(),
                                None,
                            );
                            let init = cls.expect_class(i_s).unwrap().get_init_func(i_s, &args);
                            cls.with_instance(
                                i_s,
                                self,
                                Generics::InstanceWithArguments(*definition),
                                |i_s, instance| {
                                    let args = InstanceArguments::new(instance, &args);
                                    callable(&mut i_s.with_func_and_args(&init, &args), instance)
                                },
                            )
                        }
                        Specific::SimpleGeneric => {
                            let class = self.expect_class(i_s).unwrap();
                            callable(i_s, &class)
                        }
                        Specific::Param => i_s
                            .infer_param(definition)
                            .internal_run(i_s, callable, reducer, on_missing),
                        Specific::List => callable(i_s, &ListLiteral::new(definition)),
                        Specific::TypingProtocol | Specific::TypingGeneric => {
                            callable(i_s, &TypingClass::new(*definition, specific))
                        }
                        Specific::TypingWithGenerics => {
                            let inf = definition
                                .file
                                .get_inference(i_s)
                                .infer_primary_or_atom(definition.as_primary().first());
                            if let InferredState::Saved(_, p) = inf.state {
                                callable(i_s, &TypingWithGenerics::new(*definition, p.specific()))
                            } else {
                                unreachable!()
                            }
                        }
                        _ => {
                            let instance = self.resolve_specific(i_s.database, specific);
                            callable(i_s, &instance)
                        }
                    }
                }
                PointType::Complex => {
                    let complex = definition
                        .file
                        .complex_points
                        .get(point.get_complex_index());
                    if let ComplexPoint::Class(cls_storage) = complex {
                        let class = Class::new(
                            definition.file,
                            definition.node_index,
                            &cls_storage.symbol_table,
                            Generics::None,
                            None,
                        );
                        callable(i_s, &class)
                    } else {
                        self.run_on_complex(i_s, complex, Some(definition), callable, reducer)
                    }
                }
                PointType::Unknown => on_missing(self.clone()),
                PointType::FileReference => {
                    let f = i_s.database.get_loaded_python_file(point.get_file_index());
                    callable(i_s, &Module::new(f))
                }
                _ => unreachable!(),
            },
            InferredState::UnsavedComplex(complex) => {
                self.run_on_complex(i_s, complex, None, callable, reducer)
            }
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
            ComplexPoint::Instance(cls_definition, generics, execution) => {
                let def = NodeReference::from_link(i_s.database, *cls_definition);
                let init = Function::from_execution(i_s.database, execution);
                let complex = def.get_complex().unwrap();
                if let ComplexPoint::Class(cls_storage) = complex {
                    let args = SimpleArguments::from_execution(i_s.database, execution);
                    let class = Class::new(
                        def.file,
                        def.node_index,
                        &cls_storage.symbol_table,
                        Generics::OnceCell(generics),
                        None,
                    );
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
                    let point = node_ref.get_point();
                    Inferred {
                        state: InferredState::Saved(node_ref, point),
                    }
                    .internal_run(i_s, callable, reducer, &|i| unreachable!())
                })
                .reduce(reducer)
                .unwrap(),
            ComplexPoint::BoundMethod(instance_link, func_link) => {
                let file = i_s.database.get_loaded_python_file(func_link.file);
                let func = Function::new(file, func_link.node_index);
                callable(i_s, &BoundMethod::new(instance_link, &func))
            }
            ComplexPoint::Closure(function, execution) => {
                let f = i_s.database.get_loaded_python_file(function.file);
                let func = Function::from_execution(i_s.database, execution);
                let args = SimpleArguments::from_execution(i_s.database, execution);
                callable(
                    &mut i_s.with_func_and_args(&func, &args),
                    &Function::new(f, function.node_index),
                )
                /*
                // TODO WHY IS THIS NOT WORKING???
                i_s.run_with_execution(execution, |closure_i_s| {
                    let x: () = closure_i_s;
                    //callable(closure_i_s, &Function::new(f, function.node_index));
                    todo!()
                })
                */
            }
            ComplexPoint::GenericClass(foo, bla) => {
                todo!()
            }
            _ => {
                unreachable!("Classes are handled earlier {:?}", complex)
            }
        }
    }

    #[inline]
    pub fn run_on_value(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        callable: &mut impl Fn(&mut InferenceState<'db, '_>, &dyn Value<'db>) -> Inferred<'db>,
    ) -> Inferred<'db> {
        self.internal_run(i_s, callable, &|i1, i2| i1.union(i2), &|inferred| inferred)
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
            &|inferred| ValueNameIterator::Finished,
        )
    }

    #[inline]
    pub fn run(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        callable: &mut impl FnMut(&mut InferenceState<'db, '_>, &dyn Value<'db>),
    ) {
        self.internal_run(i_s, callable, &|i1, i2| (), &|inferred| ())
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
        let builtins = database.python_state.get_builtins();
        let node_index = builtins.lookup_global(name).unwrap().node_index;
        let v = builtins.points.get(node_index);
        debug_assert_eq!(v.get_type(), PointType::Redirect);
        debug_assert_eq!(v.get_file_index(), builtins.get_file_index());
        self.use_instance(builtins, v.get_node_index(), Generics::None)
    }

    pub fn maybe_type_var(&self, i_s: &mut InferenceState<'db, '_>) -> Option<NodeReference<'db>> {
        if let InferredState::Saved(definition, point) = self.state {
            if point.get_type() == PointType::Specific
                && point.specific() == Specific::InstanceWithArguments
            {
                // TODO this check can/should be optimized by comparing node pointers that are cached
                // in python_state
                let cls = self.infer_instance_with_arguments_cls(i_s, &definition);
                if let InferredState::Saved(cls_definition, _) = cls.state {
                    if cls_definition.file.get_file_index()
                        == i_s.database.python_state.get_typing().get_file_index()
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

    pub fn resolve_function_return(self, i_s: &mut InferenceState<'db, '_>) -> Inferred<'db> {
        if let InferredState::Saved(definition, point) = self.state {
            if point.get_type() == PointType::Specific {
                match point.specific() {
                    Specific::InstanceWithArguments => {
                        let cls = self
                            .infer_instance_with_arguments_cls(i_s, &definition)
                            .resolve_function_return(i_s);
                        let args = SimpleArguments::from_primary(
                            definition.file,
                            definition.as_primary(),
                            None,
                        );
                        let init = cls.expect_class(i_s).unwrap().get_init_func(i_s, &args);
                        return Inferred::new_unsaved_complex(ComplexPoint::Instance(
                            cls.get_saved().unwrap().0.as_link(),
                            OnceCell::new(),
                            Box::new(args.as_execution(&init)),
                        ));
                    }
                    Specific::Closure => {
                        return Inferred::new_unsaved_complex(ComplexPoint::Closure(
                            PointLink::new(definition.file.get_file_index(), definition.node_index),
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
            .get_inference(i_s)
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
                if point.get_type() == PointType::Specific {
                    if let Specific::SimpleGeneric = point.specific() {
                        let p = Primary::by_index(&definition.file.tree, definition.node_index);
                        let cls = definition
                            .file
                            .get_inference(i_s)
                            .infer_primary_or_atom(p.first());
                        cls.with_instance(i_s, instance, generics, callable)
                    } else {
                        unreachable!("{:?}", point)
                    }
                } else {
                    callable(
                        i_s,
                        &instance.use_instance(definition.file, definition.node_index, generics),
                    )
                }
            }
            InferredState::UnsavedComplex(complex) => {
                todo!("{:?}", complex)
            }
        }
    }

    fn use_instance<'a>(
        &'a self,
        file: &'db PythonFile,
        node_index: NodeIndex,
        generics: Generics<'db, 'a>,
    ) -> Instance<'db, 'a> {
        let class = Class::from_position(file, node_index, generics, None).unwrap();
        let point = file.points.get(node_index);
        let complex = file.complex_points.get(point.get_complex_index() as usize);
        match complex {
            ComplexPoint::Class(c) => Instance::new(class, self),
            _ => unreachable!("Probably an issue with indexing: {:?}", &complex),
        }
    }

    pub fn expect_class(&self, i_s: &mut InferenceState<'db, '_>) -> Option<Class<'db, '_>> {
        let mut generics = Generics::None;
        if let InferredState::Saved(definition, point) = &self.state {
            if point.get_type() == PointType::Specific {
                generics = self.expect_generics().unwrap();
            }
        }
        self.expect_class_internal(i_s, generics)
    }

    fn expect_class_internal<'a>(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        generics: Generics<'db, 'a>,
    ) -> Option<Class<'db, 'a>> {
        match &self.state {
            InferredState::Saved(definition, point) => match point.get_type() {
                PointType::Complex => {
                    Class::from_position(definition.file, definition.node_index, generics, None)
                }
                PointType::Specific => match point.specific() {
                    Specific::SimpleGeneric => {
                        let inferred = definition
                            .file
                            .get_inference(i_s)
                            .infer_primary_or_atom(definition.as_primary().first());
                        inferred.expect_class_internal(i_s, generics)
                    }
                    _ => todo!("{:?}", point),
                },
                _ => unreachable!(),
            },
            InferredState::UnsavedComplex(complex) => {
                todo!("{:?}", complex)
            }
        }
    }

    pub fn expect_int(&self) -> Option<i64> {
        if let InferredState::Saved(definition, point) = self.state {
            if let PointType::Specific = point.get_type() {
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
                if file.points.get(index).is_calculated() {
                    todo!("{:?} {:?}", file.points.get(index), index);
                }
                file.points.set(
                    index,
                    Point::new_redirect(
                        definition.file.get_file_index(),
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
        }
    }

    pub fn find_function_alternative(&self) -> Function<'db> {
        if let InferredState::Saved(definition, point) = &self.state {
            if let PointType::Specific = point.get_type() {
                if let Specific::Function = point.specific() {
                    return Function::new(definition.file, definition.node_index);
                }
            }
        }
        todo!("In general this function should probably not be here")
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
            if matches!(point.get_type(), PointType::FileReference) {
                return Some(point.get_file_index());
            }
        }
        None
    }

    #[inline]
    pub fn bind(self, i_s: &InferenceState<'db, '_>, instance: &Instance<'db, '_>) -> Self {
        match &self.state {
            InferredState::Saved(definition, point) => match point.get_type() {
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
                    todo!()
                }
                _ => (),
            },
            InferredState::UnsavedComplex(complex) => {
                todo!()
            }
        }
        self
    }

    pub fn description(&self, i_s: &mut InferenceState<'db, '_>) -> String {
        self.internal_run(
            i_s,
            &mut |i_s, v| v.description(i_s),
            &|i1, i2| format!("{}|{}", i1, i2),
            &|inferred| "Unknown".to_owned(),
        )
    }

    pub fn as_any_link(&self, i_s: &InferenceState<'db, '_>) -> AnyLink {
        match &self.state {
            InferredState::Saved(definition, _) => AnyLink::Reference(definition.as_link()),
            InferredState::UnsavedComplex(complex) => AnyLink::Complex(Box::new(complex.clone())),
        }
    }

    pub fn from_any_link(database: &'db Database, any: &AnyLink) -> Self {
        match any {
            AnyLink::Reference(def) => {
                let file = database.get_loaded_python_file(def.file);
                Self::new_saved(file, def.node_index, file.points.get(def.node_index))
            }
            AnyLink::Complex(complex) => Self::new_unsaved_complex(*complex.clone()),
            AnyLink::Specific(_) => todo!(),
        }
    }

    fn expect_generics(&self) -> Option<Generics<'db, '_>> {
        if let InferredState::Saved(definition, point) = self.state {
            if point.get_type() == PointType::Specific
                && point.specific() == Specific::SimpleGeneric
            {
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
            &mut |i_s, v| v.get_kind() == ValueKind::Class,
            &|i1, i2| i1 & i2,
            &|inferred| false,
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
