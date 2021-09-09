use crate::database::{ComplexPoint, Database, Point, PointType, Specific};
use crate::debug;
use crate::file::PythonFile;
use crate::file_state::File;
use crate::name::{ValueNames, WithValueName};
use crate::value::{Class, Function, Instance, Module, Value};
use parsa::Node;
use parsa_python::PyNode;
use std::fmt;

#[derive(Debug, Clone, Copy)]
pub struct NodeReference<'a> {
    pub file: &'a PythonFile,
    pub node: PyNode<'a>,
}

#[derive(Clone, Copy)]
pub struct Inferred<'a> {
    database: &'a Database,
    pub definition: NodeReference<'a>,
    point: Point,
    is_saved: bool,
}

impl<'a> Inferred<'a> {
    pub fn new_and_save(
        database: &'a Database,
        file: &'a PythonFile,
        node: PyNode<'a>,
        point: Point,
    ) -> Self {
        file.set_point(node.index, point);
        Self::new(database, file, node, point, true)
    }

    pub fn new(
        database: &'a Database,
        file: &'a PythonFile,
        node: PyNode<'a>,
        point: Point,
        is_saved: bool,
    ) -> Self {
        Self {
            database,
            definition: NodeReference { file, node },
            point,
            is_saved,
        }
    }

    #[allow(clippy::wrong_self_convention)]
    pub fn to_value_names(&self) -> ValueNames<'a> {
        use PointType::*;
        match self.point.get_type() {
            LanguageSpecific => {
                let specific = self.point.get_language_specific();
                vec![match specific {
                    Specific::Function => Box::new(WithValueName::new(
                        self.database,
                        Function::new(self.definition.file, self.definition.node.index),
                    )),
                    Specific::AnnotationInstance => {
                        let inferred = self
                            .definition
                            .file
                            .infer_expression(self.database, self.definition.node.get_nth_child(1));
                        if let Some(instance) = inferred
                            .definition
                            .file
                            .use_instance(inferred.definition.node.index)
                        {
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
                        self.resolve_specific(self.point.get_language_specific()),
                    )),
                }]
            }
            Complex => {
                match self
                    .definition
                    .file
                    .complex_points
                    .get(self.point.get_complex_index())
                    .unwrap()
                {
                    ComplexPoint::Class(cls_storage) => {
                        let cls = Class::new(
                            self.definition.file,
                            self.definition.node.index,
                            &cls_storage.symbol_table,
                        );
                        vec![Box::new(WithValueName::new(self.database, cls))]
                    }
                    _ => {
                        todo!();
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
        }
    }

    #[inline]
    pub fn run<T>(
        &self,
        callable: impl Fn(&dyn Value<'a>) -> T,
        on_missing: impl Fn(Inferred<'a>) -> T,
    ) -> T {
        use PointType::*;
        match self.point.get_type() {
            LanguageSpecific => {
                let specific = self.point.get_language_specific();
                match specific {
                    Specific::Function => callable(&Function::new(
                        self.definition.file,
                        self.definition.node.index,
                    )),
                    Specific::AnnotationInstance => {
                        let inferred = self
                            .definition
                            .file
                            .infer_expression(self.database, self.definition.node.get_nth_child(1));
                        todo!()
                    }
                    Specific::InstanceWithArguments => {
                        let cls = self.infer_instance_with_arguments_cls();
                        callable(
                            &cls.definition
                                .file
                                .use_instance(cls.definition.node.index)
                                .unwrap(),
                        )
                    }
                    _ => {
                        let instance = self.resolve_specific(specific);
                        callable(&instance)
                    }
                }
            }
            Complex => {
                match self
                    .definition
                    .file
                    .complex_points
                    .get(self.point.get_complex_index())
                    .unwrap()
                {
                    ComplexPoint::Union(lst) => {
                        todo!()
                    }
                    ComplexPoint::Class(cls_storage) => {
                        let class = Class::new(
                            self.definition.file,
                            self.definition.node.index,
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
                    ComplexPoint::Closure(bla, bar) => {
                        todo!()
                    }
                    ComplexPoint::Generic(bla) => {
                        todo!()
                    }
                }
            }
            MissingOrUnknown => on_missing(*self),
            FileReference => {
                let f = self
                    .database
                    .get_loaded_python_file(self.point.get_file_index());
                callable(&Module::new(f, &f.symbol_table))
            }
            _ => unreachable!(),
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
        if self.point.get_type() == PointType::LanguageSpecific
            && self.point.get_language_specific() == Specific::InstanceWithArguments
        {
            // TODO this check can/should be optimized by comparing node pointers that are cached
            // in python_state
            let cls = self.infer_instance_with_arguments_cls();
            return cls.definition.file.get_file_index()
                == self.database.python_state.get_typing().get_file_index()
                && cls.definition.node.get_code().starts_with("class TypeVar");
        }
        false
    }

    pub fn resolve_closure(self) -> Inferred<'a> {
        if self.point.get_type() == PointType::LanguageSpecific
            && self.point.get_language_specific() == Specific::Closure
        {
            todo!()
        } else {
            self
        }
    }

    fn infer_instance_with_arguments_cls(&self) -> Self {
        self.definition
            .file
            .infer_expression_part(self.database, self.definition.node.get_nth_child(0))
    }
}

impl fmt::Debug for Inferred<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("Inferred")
            .field("definition", &self.definition)
            .field("point", &self.point)
            .field("is_saved", &self.is_saved)
            .finish()
    }
}

fn load_builtin_instance_from_str<'a>(database: &'a Database, name: &'static str) -> Instance<'a> {
    let builtins = database.python_state.get_builtins();
    let node_index = builtins.lookup_global(name).unwrap().node_index;
    let v = builtins.get_point(node_index);
    debug_assert_eq!(v.get_type(), PointType::Redirect);
    debug_assert_eq!(v.get_file_index(), builtins.get_file_index());
    builtins.use_instance(v.get_node_index()).unwrap()
}
