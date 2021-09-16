use crate::database::{ComplexPoint, Database, Locality, Point, PointLink, PointType, Specific};
use crate::debug;
use crate::file::PythonFile;
use crate::file_state::File;
use crate::inference_state::InferenceState;
use crate::name::{ValueNames, WithValueName};
use crate::value::{Class, Function, Instance, Module, Value};
use parsa::{Node, NodeIndex};
use parsa_python::PyNode;
use std::fmt;

#[derive(Debug, Clone, Copy)]
pub struct NodeReference<'db> {
    pub file: &'db PythonFile,
    pub node: PyNode<'db>,
}

#[derive(Debug, Clone)]
enum InferredState<'db> {
    Saved(NodeReference<'db>, Point),
    UnsavedComplex(ComplexPoint),
    UnsavedSpecific(Specific),
}

#[derive(Clone)]
pub struct Inferred<'db> {
    state: InferredState<'db>,
}

impl<'db> Inferred<'db> {
    pub fn new_and_save(file: &'db PythonFile, node: PyNode<'db>, point: Point) -> Self {
        file.set_point(node.index, point);
        Self::new_saved(file, node, point)
    }

    pub fn new_saved(file: &'db PythonFile, node: PyNode<'db>, point: Point) -> Self {
        Self {
            state: InferredState::Saved(NodeReference { file, node }, point),
        }
    }

    pub fn new_unsaved_complex(database: &'db Database, complex: ComplexPoint) -> Self {
        Self {
            state: InferredState::UnsavedComplex(complex),
        }
    }

    #[allow(clippy::wrong_self_convention)]
    pub fn to_value_names(&self, i_s: &mut InferenceState<'db, '_>) -> ValueNames<'db> {
        use PointType::*;
        match &self.state {
            InferredState::Saved(definition, point) => match point.get_type() {
                LanguageSpecific => {
                    let specific = point.get_language_specific();
                    vec![match specific {
                        Specific::Function => Box::new(WithValueName::new(
                            i_s.database,
                            Function::new(definition.file, definition.node.index, None),
                        )),
                        Specific::AnnotationInstance => {
                            let inferred = definition
                                .file
                                .get_inference(i_s, None)
                                .infer_expression(definition.node.get_nth_child(1));
                            if let Some(instance) = inferred.instantiate() {
                                Box::new(WithValueName::new(i_s.database, instance))
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
                            i_s.database,
                            self.resolve_specific(i_s.database, point.get_language_specific()),
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
                            vec![Box::new(WithValueName::new(i_s.database, cls))]
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
        i_s: &mut InferenceState<'db, '_>,
        callable: impl Fn(&mut InferenceState<'db, '_>, &dyn Value<'db>) -> T,
        on_missing: impl Fn(Inferred<'db>) -> T,
    ) -> T {
        use PointType::*;
        match &self.state {
            InferredState::Saved(definition, point) => match point.get_type() {
                LanguageSpecific => {
                    let specific = point.get_language_specific();
                    match specific {
                        Specific::Function => callable(
                            i_s,
                            &Function::new(definition.file, definition.node.index, None),
                        ),
                        Specific::AnnotationInstance => {
                            let inferred = definition
                                .file
                                .get_inference(i_s, None)
                                .infer_expression(definition.node.get_nth_child(1));
                            todo!()
                        }
                        Specific::InstanceWithArguments => {
                            let cls = self.infer_instance_with_arguments_cls(i_s, definition);
                            callable(i_s, &cls.instantiate().unwrap())
                        }
                        Specific::Param => {
                            i_s.infer_param(definition).run(i_s, callable, on_missing)
                        }
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
                            definition.node.index,
                            &cls_storage.symbol_table,
                        );
                        callable(i_s, &class)
                    } else {
                        self.run_on_complex(i_s, complex, Some(definition), callable)
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
                self.run_on_complex(i_s, complex, None, callable)
            }
            InferredState::UnsavedSpecific(specific) => {
                todo!()
            }
        }
    }

    #[inline]
    fn run_on_complex<T>(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        complex: &ComplexPoint,
        definition: Option<&NodeReference<'db>>,
        callable: impl Fn(&mut InferenceState<'db, '_>, &dyn Value<'db>) -> T,
    ) -> T {
        match complex {
            ComplexPoint::Union(lst) => {
                todo!()
            }
            ComplexPoint::Class(cls_storage) => {
                unreachable!("Class is handled earlier")
            }
            ComplexPoint::Instance(bla) => {
                todo!()
            }
            ComplexPoint::Method(bla, bar) => {
                todo!()
            }
            ComplexPoint::Closure(function, execution) => {
                let f = i_s.database.get_loaded_python_file(function.file);
                callable(i_s, &Function::new(f, function.node_index, Some(execution)))
            }
            ComplexPoint::Generic(bla) => {
                todo!()
            }
        }
    }

    #[inline]
    pub fn run_on_value(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        callable: impl Fn(&mut InferenceState<'db, '_>, &dyn Value<'db>) -> Inferred<'db>,
    ) -> Inferred<'db> {
        self.run(i_s, callable, |inferred| inferred)
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
                        && cls_definition.node.get_code().starts_with("class TypeVar");
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
                        let cls = self.infer_instance_with_arguments_cls(i_s, &definition);
                        return cls.resolve_function_return(i_s);
                    }
                    Specific::Closure => {
                        return Inferred::new_unsaved_complex(
                            i_s.database,
                            ComplexPoint::Closure(
                                PointLink::new(
                                    definition.file.get_file_index(),
                                    definition.node.index,
                                ),
                                i_s.args_as_execution().unwrap(),
                            ),
                        );
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
            .get_inference(i_s, None)
            .infer_expression_part(definition.node.get_nth_child(0))
    }

    fn instantiate(&self) -> Option<Instance<'db>> {
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

    pub fn save_redirect(self, file: &'db PythonFile, index: NodeIndex) -> Self {
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

fn load_builtin_instance_from_str<'db>(
    database: &'db Database,
    name: &'static str,
) -> Instance<'db> {
    let builtins = database.python_state.get_builtins();
    let node_index = builtins.lookup_global(name).unwrap().node_index;
    let v = builtins.get_point(node_index);
    debug_assert_eq!(v.get_type(), PointType::Redirect);
    debug_assert_eq!(v.get_file_index(), builtins.get_file_index());
    use_instance(builtins, v.get_node_index()).unwrap()
}
