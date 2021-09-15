use crate::arguments::Arguments;
use crate::database::{ComplexPoint, Database, Locality, Point, PointLink, PointType, Specific};
use crate::debug;
use crate::file::PythonFile;
use crate::file_state::File;
use crate::name::{ValueNames, WithValueName};
use crate::value::{Class, Function, Instance, Module, Value};
use parsa::{Node, NodeIndex};
use parsa_python::PyNode;
use std::fmt;

#[derive(Debug, Clone, Copy)]
struct NodeReference<'a> {
    pub file: &'a PythonFile,
    pub node: PyNode<'a>,
}

#[derive(Debug, Clone)]
enum InferredState<'a> {
    Saved(NodeReference<'a>, Point),
    UnsavedComplex(ComplexPoint),
    UnsavedSpecific(Specific),
}

#[derive(Clone)]
pub struct Inferred<'a> {
    database: &'a Database,
    state: InferredState<'a>,
}

impl<'a> Inferred<'a> {
    pub fn new_and_save(
        database: &'a Database,
        file: &'a PythonFile,
        node: PyNode<'a>,
        point: Point,
    ) -> Self {
        file.set_point(node.index, point);
        Self::new_saved(database, file, node, point)
    }

    pub fn new_saved(
        database: &'a Database,
        file: &'a PythonFile,
        node: PyNode<'a>,
        point: Point,
    ) -> Self {
        Self {
            database,
            state: InferredState::Saved(NodeReference { file, node }, point),
        }
    }

    pub fn new_unsaved_complex(database: &'a Database, complex: ComplexPoint) -> Self {
        Self {
            database,
            state: InferredState::UnsavedComplex(complex),
        }
    }

    #[allow(clippy::wrong_self_convention)]
    pub fn to_value_names(&self) -> ValueNames<'a> {
        use PointType::*;
        match &self.state {
            InferredState::Saved(definition, point) => match point.get_type() {
                LanguageSpecific => {
                    let specific = point.get_language_specific();
                    vec![match specific {
                        Specific::Function => Box::new(WithValueName::new(
                            self.database,
                            Function::new(definition.file, definition.node.index, None),
                        )),
                        Specific::AnnotationInstance => {
                            let inferred = definition
                                .file
                                .get_inference(self.database, None)
                                .infer_expression(definition.node.get_nth_child(1));
                            if let Some(instance) = inferred.instantiate() {
                                Box::new(WithValueName::new(self.database, instance))
                            } else {
                                debug!(
                                    "Inferred annotation {:?}, which is not a class: {:?}",
                                    self, inferred
                                );
                                return vec![];
                            }
                        }
                        Specific::TypeVar => {
                            todo!()
                        }
                        _ => Box::new(WithValueName::new(
                            self.database,
                            self.resolve_specific(point.get_language_specific()),
                        )),
                    }]
                }
                Complex => {
                    match definition
                        .file
                        .complex_points
                        .get(point.get_complex_index())
                    {
                        ComplexPoint::Class(cls_storage) => {
                            let cls = Class::new(
                                definition.file,
                                definition.node.index,
                                &cls_storage.symbol_table,
                            );
                            vec![Box::new(WithValueName::new(self.database, cls))]
                        }
                        x => {
                            todo!("{:?}", x);
                        }
                    }
                }
                MissingOrUnknown => {
                    vec![]
                }
                FileReference => {
                    todo!();
                }
                _ => unreachable!(),
            },
            InferredState::UnsavedComplex(complex) => {
                todo!()
            }
            InferredState::UnsavedSpecific(specific) => {
                todo!()
            }
        }
    }

    #[inline]
    pub fn run<T>(
        &self,
        callable: impl Fn(&dyn Value<'a>) -> T,
        on_missing: impl Fn(Inferred<'a>) -> T,
    ) -> T {
        use PointType::*;
        match &self.state {
            InferredState::Saved(definition, point) => match point.get_type() {
                LanguageSpecific => {
                    let specific = point.get_language_specific();
                    match specific {
                        Specific::Function => {
                            callable(&Function::new(definition.file, definition.node.index, None))
                        }
                        Specific::AnnotationInstance => {
                            let inferred = definition
                                .file
                                .get_inference(self.database, None)
                                .infer_expression(definition.node.get_nth_child(1));
                            todo!()
                        }
                        Specific::InstanceWithArguments => {
                            let cls = self.infer_instance_with_arguments_cls(definition);
                            callable(&cls.instantiate().unwrap())
                        }
                        Specific::Param => {
                            todo!()
                        }
                        _ => {
                            let instance = self.resolve_specific(specific);
                            callable(&instance)
                        }
                    }
                }
                Complex => self.run_on_complex(
                    definition
                        .file
                        .complex_points
                        .get(point.get_complex_index()),
                    Some(definition),
                    callable,
                ),
                MissingOrUnknown => on_missing(self.clone()),
                FileReference => {
                    let f = self.database.get_loaded_python_file(point.get_file_index());
                    callable(&Module::new(f, &f.symbol_table))
                }
                _ => unreachable!(),
            },
            InferredState::UnsavedComplex(complex) => self.run_on_complex(complex, None, callable),
            InferredState::UnsavedSpecific(specific) => {
                todo!()
            }
        }
    }

    #[inline]
    fn run_on_complex<T>(
        &self,
        complex: &ComplexPoint,
        definition: Option<&NodeReference<'a>>,
        callable: impl Fn(&dyn Value<'a>) -> T,
    ) -> T {
        match complex {
            ComplexPoint::Union(lst) => {
                todo!()
            }
            ComplexPoint::Class(cls_storage) => {
                let definition = definition.unwrap();
                let class = Class::new(
                    definition.file,
                    definition.node.index,
                    &cls_storage.symbol_table,
                );
                callable(&class)
            }
            ComplexPoint::Instance(bla) => {
                todo!()
            }
            ComplexPoint::Method(bla, bar) => {
                todo!()
            }
            ComplexPoint::Closure(function, execution) => {
                let f = self.database.get_loaded_python_file(function.file);
                callable(&Function::new(f, function.node_index, Some(execution)))
            }
            ComplexPoint::Generic(bla) => {
                todo!()
            }
        }
    }

    #[inline]
    pub fn run_on_value(&self, callable: impl Fn(&dyn Value<'a>) -> Inferred<'a>) -> Inferred<'a> {
        self.run(callable, |inferred| inferred)
    }

    fn resolve_specific(&self, specific: Specific) -> Instance<'a> {
        load_builtin_instance_from_str(
            self.database,
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

    pub fn is_type_var(&self) -> bool {
        if let InferredState::Saved(definition, point) = self.state {
            if point.get_type() == PointType::LanguageSpecific
                && point.get_language_specific() == Specific::InstanceWithArguments
            {
                // TODO this check can/should be optimized by comparing node pointers that are cached
                // in python_state
                let cls = self.infer_instance_with_arguments_cls(&definition);
                if let InferredState::Saved(cls_definition, _) = cls.state {
                    return cls_definition.file.get_file_index()
                        == self.database.python_state.get_typing().get_file_index()
                        && cls_definition.node.get_code().starts_with("class TypeVar");
                }
            }
        }
        false
    }

    pub fn resolve_closure_and_params(
        self,
        function: &Function<'a, '_>,
        args: &Arguments<'a>,
    ) -> Inferred<'a> {
        if let InferredState::Saved(definition, point) = self.state {
            if point.get_type() == PointType::LanguageSpecific {
                if point.get_language_specific() == Specific::Closure {
                    return Inferred::new_unsaved_complex(
                        self.database,
                        ComplexPoint::Closure(
                            PointLink::new(definition.file.get_file_index(), definition.node.index),
                            args.as_execution(function),
                        ),
                    );
                } else if point.get_language_specific() == Specific::Param {
                    return function.infer_param(self.database, definition.node.index, args);
                }
            }
        }
        self
    }

    fn infer_instance_with_arguments_cls(&self, definition: &NodeReference<'a>) -> Self {
        definition
            .file
            .get_inference(self.database, None)
            .infer_expression_part(definition.node.get_nth_child(0))
    }

    fn instantiate(&self) -> Option<Instance<'a>> {
        match &self.state {
            InferredState::Saved(definition, point) => {
                use_instance(definition.file, definition.node.index)
            }
            InferredState::UnsavedComplex(complex) => {
                todo!("{:?}", complex)
            }
            InferredState::UnsavedSpecific(specific) => {
                todo!("{:?}", specific)
            }
        }
    }

    pub fn save_redirect(self, file: &'a PythonFile, index: NodeIndex) -> Self {
        // TODO this locality should be calculated in a more correct way
        match &self.state {
            InferredState::Saved(definition, point) => {
                file.set_point(
                    index,
                    Point::new_redirect(
                        definition.file.get_file_index(),
                        definition.node.index,
                        Locality::Stmt,
                    ),
                );
                self
            }
            InferredState::UnsavedComplex(complex) => {
                file.complex_points
                    .insert(&file.points, index, complex.clone());
                Self::new_saved(
                    self.database,
                    file,
                    file.tree.get_node_by_index(index),
                    file.get_point(index),
                )
            }
            InferredState::UnsavedSpecific(specific) => {
                todo!()
            }
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
            InferredState::UnsavedSpecific(specific) => s.field("specific", &specific),
        }
        .finish()
    }
}

fn use_instance(file: &PythonFile, node_index: NodeIndex) -> Option<Instance> {
    let v = file.get_point(node_index);
    debug_assert_eq!(v.get_type(), PointType::Complex);
    let complex = file.complex_points.get(v.get_complex_index() as usize);
    match complex {
        ComplexPoint::Class(c) => Some(Instance::new(file, node_index, &c.symbol_table)),
        _ => unreachable!("Probably an issue with indexing: {:?}", &complex),
    }
}

fn load_builtin_instance_from_str<'a>(database: &'a Database, name: &'static str) -> Instance<'a> {
    let builtins = database.python_state.get_builtins();
    let node_index = builtins.lookup_global(name).unwrap().node_index;
    let v = builtins.get_point(node_index);
    debug_assert_eq!(v.get_type(), PointType::Redirect);
    debug_assert_eq!(v.get_file_index(), builtins.get_file_index());
    use_instance(builtins, v.get_node_index()).unwrap()
}
