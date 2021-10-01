use crate::arguments::{Arguments, InstanceArguments, SimpleArguments};
use crate::database::{ComplexPoint, Database, Locality, Point, PointLink, PointType, Specific};
use crate::file::PythonFile;
use crate::file_state::File;
use crate::inference_state::InferenceState;
use crate::name::{ValueName, ValueNameIterator, WithValueName};
use crate::value::{Class, Function, Instance, ListLiteral, Module, Value};
use parsa_python::PyNode;
use parsa_python_ast::{NodeIndex, Primary};
use std::fmt;

pub trait Inferrable<'db> {
    fn infer(&self) -> Inferred<'db>;
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
    fn from_link(database: &'db Database, point: PointLink) -> Self {
        let file = database.get_loaded_python_file(point.file);
        Self {
            file,
            node_index: point.node_index,
        }
    }

    fn get_point(&self) -> Point {
        self.file.get_point(self.node_index)
    }

    fn get_complex(&self) -> Option<&'db ComplexPoint> {
        let point = self.get_point();
        if let PointType::Complex = point.get_type() {
            Some(self.file.complex_points.get(point.get_complex_index()))
        } else {
            None
        }
    }

    fn as_link(&self) -> PointLink {
        PointLink::new(self.file.get_file_index(), self.node_index)
    }

    pub fn node(&self) -> PyNode<'db> {
        self.file.tree.get_node_by_index(self.node_index)
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
        file.set_point(node_index, point);
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

    #[inline]
    fn run<T>(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        callable: &impl Fn(&mut InferenceState<'db, '_>, &dyn Value<'db>) -> T,
        reducer: &impl Fn(T, T) -> T,
        on_missing: &impl Fn(Inferred<'db>) -> T,
    ) -> T {
        use PointType::*;
        match &self.state {
            InferredState::Saved(definition, point) => match point.get_type() {
                LanguageSpecific => {
                    let specific = point.get_language_specific();
                    match specific {
                        Specific::Function => {
                            callable(i_s, &Function::new(definition.file, definition.node_index))
                        }
                        Specific::AnnotationInstance => {
                            let inferred = definition
                                .file
                                .get_inference(i_s)
                                .infer_expression(definition.node().get_nth_child(1));
                            callable(i_s, &inferred.instantiate())
                        }
                        Specific::InstanceWithArguments => {
                            let cls = self.infer_instance_with_arguments_cls(i_s, definition);
                            let instance = cls.instantiate();
                            let args = InstanceArguments::new(
                                &instance,
                                definition.file,
                                Primary(definition.node()),
                                None,
                            );
                            let init = cls.expect_class().unwrap().get_init_func(i_s, &args);
                            callable(&mut i_s.with_func_and_args(&init, &args), &instance)
                        }
                        Specific::Param => i_s
                            .infer_param(definition)
                            .run(i_s, callable, reducer, on_missing),
                        Specific::List => callable(i_s, &ListLiteral::new(definition)),
                        _ => {
                            let instance = self.resolve_specific(i_s.database, specific);
                            callable(i_s, &instance)
                        }
                    }
                }
                Complex => {
                    let complex = definition
                        .file
                        .complex_points
                        .get(point.get_complex_index());
                    if let ComplexPoint::Class(cls_storage) = complex {
                        let class = Class::new(
                            definition.file,
                            definition.node_index,
                            &cls_storage.symbol_table,
                        );
                        callable(i_s, &class)
                    } else {
                        self.run_on_complex(i_s, complex, Some(definition), callable, reducer)
                    }
                }
                MissingOrUnknown => on_missing(self.clone()),
                FileReference => {
                    let f = i_s.database.get_loaded_python_file(point.get_file_index());
                    callable(i_s, &Module::new(f, &f.symbol_table))
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
        callable: &impl Fn(&mut InferenceState<'db, '_>, &dyn Value<'db>) -> T,
        reducer: &impl Fn(T, T) -> T,
    ) -> T {
        match complex {
            ComplexPoint::Instance(cls_definition, execution) => {
                let def = NodeReference::from_link(i_s.database, *cls_definition);
                let complex = def.get_complex().unwrap();
                if let ComplexPoint::Class(cls_storage) = complex {
                    let instance =
                        Instance::new(def.file, def.node_index, &cls_storage.symbol_table);
                    let args =
                        InstanceArguments::from_execution(i_s.database, &instance, execution);
                    let init = Function::from_execution(i_s.database, execution);
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
                    .run(i_s, callable, reducer, &|i| unreachable!())
                })
                .reduce(reducer)
                .unwrap(),
            ComplexPoint::Method(bla, bar) => {
                todo!()
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
            ComplexPoint::Generic(bla) => {
                todo!()
            }
            ComplexPoint::Class(cls_storage) => {
                unreachable!("Class is handled earlier")
            }
        }
    }

    #[inline]
    pub fn run_on_value(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        callable: &impl Fn(&mut InferenceState<'db, '_>, &dyn Value<'db>) -> Inferred<'db>,
    ) -> Inferred<'db> {
        self.run(i_s, callable, &|i1, i2| i1.union(i2), &|inferred| inferred)
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
        self.run(
            i_s,
            &|i_s, value| {
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

    fn resolve_specific(&self, database: &'db Database, specific: Specific) -> Instance<'db> {
        load_builtin_instance_from_str(
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

    pub fn is_type_var(&self, i_s: &mut InferenceState<'db, '_>) -> bool {
        if let InferredState::Saved(definition, point) = self.state {
            if point.get_type() == PointType::LanguageSpecific
                && point.get_language_specific() == Specific::InstanceWithArguments
            {
                // TODO this check can/should be optimized by comparing node pointers that are cached
                // in python_state
                let cls = self.infer_instance_with_arguments_cls(i_s, &definition);
                if let InferredState::Saved(cls_definition, _) = cls.state {
                    return cls_definition.file.get_file_index()
                        == i_s.database.python_state.get_typing().get_file_index()
                        && cls_definition
                            .node()
                            .get_code()
                            .starts_with("class TypeVar");
                }
            }
        }
        false
    }

    pub fn resolve_function_return(self, i_s: &mut InferenceState<'db, '_>) -> Inferred<'db> {
        if let InferredState::Saved(definition, point) = self.state {
            if point.get_type() == PointType::LanguageSpecific {
                match point.get_language_specific() {
                    Specific::InstanceWithArguments => {
                        let cls = self
                            .infer_instance_with_arguments_cls(i_s, &definition)
                            .resolve_function_return(i_s);
                        let args =
                            SimpleArguments::new(definition.file, Primary(definition.node()), None);
                        let init = cls.expect_class().unwrap().get_init_func(i_s, &args);
                        return Inferred::new_unsaved_complex(ComplexPoint::Instance(
                            cls.get_saved().unwrap().0.as_link(),
                            args.as_execution(&init),
                        ));
                    }
                    Specific::Closure => {
                        return Inferred::new_unsaved_complex(ComplexPoint::Closure(
                            PointLink::new(definition.file.get_file_index(), definition.node_index),
                            i_s.args_as_execution().unwrap(),
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
            .infer_expression_part(definition.node().get_nth_child(0))
    }

    fn instantiate(&self) -> Instance<'db> {
        match &self.state {
            InferredState::Saved(definition, point) => {
                use_instance(definition.file, definition.node_index)
            }
            InferredState::UnsavedComplex(complex) => {
                unreachable!("{:?}", complex)
            }
        }
    }

    fn expect_class(&self) -> Option<Class<'db>> {
        match &self.state {
            InferredState::Saved(definition, point) => {
                use_class(definition.file, definition.node_index)
            }
            InferredState::UnsavedComplex(complex) => {
                todo!("{:?}", complex)
            }
        }
    }

    pub fn expect_int(&self) -> Option<i64> {
        if let InferredState::Saved(definition, point) = self.state {
            if let PointType::LanguageSpecific = point.get_type() {
                if let Specific::Integer = point.get_language_specific() {
                    //if definition.node.is_type(Terminal(TerminalType::Number)) {
                    return definition.node().get_code().parse().ok();
                    //}
                }
            }
        }
        None
    }

    pub fn save_redirect(self, file: &'db PythonFile, index: NodeIndex) -> Self {
        // TODO this locality should be calculated in a more correct way
        match &self.state {
            InferredState::Saved(definition, point) => {
                if file.get_point(index).is_calculated() {
                    todo!(
                        "{:?} {:?}",
                        file.get_point(index),
                        file.tree.get_node_by_index(index)
                    );
                }
                file.set_point(
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
                Self::new_saved(file, index, file.get_point(index))
            }
        }
    }

    pub fn find_function_alternative(&self) -> Function<'db> {
        if let InferredState::Saved(definition, point) = &self.state {
            if let PointType::LanguageSpecific = point.get_type() {
                if let Specific::Function = point.get_language_specific() {
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

fn use_instance(file: &PythonFile, node_index: NodeIndex) -> Instance {
    let v = file.get_point(node_index);
    debug_assert_eq!(v.get_type(), PointType::Complex);
    let complex = file.complex_points.get(v.get_complex_index() as usize);
    match complex {
        ComplexPoint::Class(c) => Instance::new(file, node_index, &c.symbol_table),
        _ => unreachable!("Probably an issue with indexing: {:?}", &complex),
    }
}

fn use_class(file: &PythonFile, node_index: NodeIndex) -> Option<Class> {
    let v = file.get_point(node_index);
    debug_assert_eq!(v.get_type(), PointType::Complex);
    let complex = file.complex_points.get(v.get_complex_index() as usize);
    match complex {
        ComplexPoint::Class(c) => Some(Class::new(file, node_index, &c.symbol_table)),
        _ => unreachable!("Probably an issue with indexing: {:?}", &complex),
    }
}

fn load_builtin_instance_from_str<'db>(
    database: &'db Database,
    name: &'static str,
) -> Instance<'db> {
    let builtins = database.python_state.get_builtins();
    let node_index = builtins.lookup_global(name).unwrap().node_index;
    let v = builtins.get_point(node_index);
    debug_assert_eq!(v.get_type(), PointType::Redirect);
    debug_assert_eq!(v.get_file_index(), builtins.get_file_index());
    use_instance(builtins, v.get_node_index())
}

// TODO unused -> delete?!
enum Exact<'db> {
    Int(bool),
    Str(&'db str),
    Bool(bool),
    Bytes(&'db str),
    Float(f64),
}
