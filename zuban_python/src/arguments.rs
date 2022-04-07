use std::mem;

use crate::database::{Database, Execution, MroIndex, PointLink, TypeVar};
use crate::file::PythonFile;
use crate::file_state::File;
use crate::getitem::{SliceType, SliceTypeContent};
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::node_ref::NodeRef;
use crate::value::{Class, Function, Value};
use parsa_python_ast::{
    Argument as ASTArgument, ArgumentsDetails, ArgumentsIterator, Comprehension, NodeIndex,
    Primary, PrimaryContent,
};

pub enum ArgumentsType<'db> {
    Normal(&'db PythonFile, NodeIndex),
}

pub trait Arguments<'db>: std::fmt::Debug {
    fn iter_arguments(&self) -> ArgumentIterator<'db, '_>;
    fn outer_execution(&self) -> Option<&Execution>;
    fn as_execution(&self, function: &Function) -> Option<Execution>;
    fn type_(&self) -> ArgumentsType<'db>;
    fn node_reference(&self) -> NodeRef<'db>;
}

#[derive(Debug)]
pub struct SimpleArguments<'db, 'a> {
    // The node id of the grammar node called primary, which is defined like
    // primary "(" [arguments | comprehension] ")"
    file: &'db PythonFile,
    primary_node_index: NodeIndex,
    details: ArgumentsDetails<'db>,
    in_: Option<&'a Execution>,
    class_of_method: Option<Class<'db, 'a>>,
}

impl<'db, 'a> Arguments<'db> for SimpleArguments<'db, 'a> {
    fn iter_arguments(&self) -> ArgumentIterator<'db, '_> {
        ArgumentIterator::Normal(self.argument_iterator_base())
    }

    fn outer_execution(&self) -> Option<&Execution> {
        self.in_
    }

    fn as_execution(&self, function: &Function) -> Option<Execution> {
        Some(Execution::new(
            function.reference.as_link(),
            PointLink::new(self.file.file_index(), self.primary_node_index),
            self.in_,
        ))
    }

    fn type_(&self) -> ArgumentsType<'db> {
        ArgumentsType::Normal(self.file, self.primary_node_index)
    }

    fn node_reference(&self) -> NodeRef<'db> {
        NodeRef::new(self.file, self.primary_node_index)
    }
}

impl<'db, 'a> SimpleArguments<'db, 'a> {
    pub fn new(
        file: &'db PythonFile,
        primary_node_index: NodeIndex,
        details: ArgumentsDetails<'db>,
        in_: Option<&'a Execution>,
        class_of_method: Option<Class<'db, 'a>>,
    ) -> Self {
        Self {
            file,
            primary_node_index,
            details,
            in_,
            class_of_method,
        }
    }

    pub fn from_primary(
        file: &'db PythonFile,
        primary_node: Primary<'db>,
        in_: Option<&'a Execution>,
        class_of_method: Option<Class<'db, 'a>>,
    ) -> Self {
        match primary_node.second() {
            PrimaryContent::Execution(details) => {
                Self::new(file, primary_node.index(), details, in_, class_of_method)
            }
            _ => unreachable!(),
        }
    }

    pub fn from_execution(database: &'db Database, execution: &'a Execution) -> Self {
        let f = database.loaded_python_file(execution.argument_node.file);
        let primary = Primary::by_index(&f.tree, execution.argument_node.node_index);
        Self::from_primary(f, primary, execution.in_.as_deref(), None)
    }

    pub fn argument_iterator_base(&self) -> ArgumentIteratorBase<'db> {
        match self.details {
            ArgumentsDetails::Node(arguments) => {
                ArgumentIteratorBase::Iterator(self.file, arguments.iter())
            }
            ArgumentsDetails::Comprehension(comprehension) => {
                ArgumentIteratorBase::Comprehension(self.file, comprehension)
            }
            ArgumentsDetails::None => ArgumentIteratorBase::Finished,
        }
    }

    fn with_class_method(&self, class: Class<'db, 'a>) -> Self {
        debug_assert!(self.class_of_method.is_none());
        Self::new(
            self.file,
            self.primary_node_index,
            self.details,
            self.in_,
            Some(class),
        )
    }

    pub fn maybe_type_var(&self, i_s: &mut InferenceState<'db, '_>) -> Option<TypeVar> {
        let mut iterator = self.iter_arguments();
        if let Some(Argument::Positional(name_node)) = iterator.next() {
            let name_expr = name_node.as_named_expression();
            let py_string = match name_expr.maybe_single_string_literal() {
                Some(py_string) => py_string,
                None => return None,
            };
            let mut constraints = vec![];
            let mut bound = None;
            let mut covariant = false;
            let mut contravariant = false;
            for arg in iterator {
                match arg {
                    Argument::Positional(node) => {
                        let mut inference = node.file.inference(i_s);
                        if let Some(t) = inference.compute_type_var_bound(node.as_expression()) {
                            constraints.push(t);
                        } else {
                            return None;
                        }
                    }
                    Argument::Keyword(name, node) => match name {
                        "covariant" => {
                            let code = node.as_expression().as_code();
                            match code {
                                "true" => covariant = true,
                                "false" => (),
                                _ => return None,
                            }
                        }
                        "contravariant" => {
                            let code = node.as_expression().as_code();
                            match code {
                                "true" => contravariant = true,
                                "false" => (),
                                _ => return None,
                            }
                        }
                        "bound" => {
                            if let Some(t) = node
                                .file
                                .inference(i_s)
                                .compute_type_var_bound(node.as_expression())
                            {
                                bound = Some(t)
                            } else {
                                return None;
                            }
                        }
                        _ => return None,
                    },
                    Argument::Value(v) => unreachable!(),
                }
            }
            return Some(TypeVar {
                name: PointLink {
                    file: name_node.file.file_index(),
                    node_index: py_string.index(),
                },
                constraints: constraints.into_boxed_slice(),
                bound,
                covariant,
                contravariant,
            });
        }
        None
    }
}

#[derive(Debug)]
pub struct InstanceArguments<'db, 'a, 'b> {
    instance: &'a dyn Value<'db, 'b>,
    mro_index: MroIndex,
    arguments: &'a dyn Arguments<'db>,
}

impl<'db, 'a> Arguments<'db> for InstanceArguments<'db, 'a, '_> {
    fn iter_arguments(&self) -> ArgumentIterator<'db, '_> {
        let args = self.arguments.iter_arguments();
        // Transmute is necessary, because lifetimes in traits are invariant, see also:
        // https://stackoverflow.com/questions/70425773/why-does-lifetime-coercion-work-with-structs-but-not-with-traits/70427218#70427218
        // But, we know that all Values only work with coariant 'b, so it's ok.
        ArgumentIterator::Instance(
            unsafe { std::mem::transmute(self.instance) },
            self.arguments,
        )
    }

    fn outer_execution(&self) -> Option<&Execution> {
        self.arguments.outer_execution()
    }

    fn as_execution(&self, function: &Function) -> Option<Execution> {
        self.arguments.as_execution(function)
    }

    fn type_(&self) -> ArgumentsType<'db> {
        self.arguments.type_()
    }

    fn node_reference(&self) -> NodeRef<'db> {
        self.arguments.node_reference()
    }
}

impl<'db, 'a, 'b> InstanceArguments<'db, 'a, 'b> {
    pub fn new(instance: &'a dyn Value<'db, 'b>, arguments: &'a dyn Arguments<'db>) -> Self {
        Self {
            arguments,
            instance,
            mro_index: MroIndex(0),
        }
    }

    pub fn with_mro_index(
        instance: &'a dyn Value<'db, 'b>,
        mro_index: MroIndex,
        arguments: &'a dyn Arguments<'db>,
    ) -> Self {
        Self {
            arguments,
            instance,
            mro_index,
        }
    }
}

#[derive(Debug)]
pub enum Argument<'db, 'a> {
    // Can be used for classmethod class or self in bound methods
    Keyword(&'db str, NodeRef<'db>),
    Value(&'a dyn Value<'db, 'a>),
    Positional(NodeRef<'db>),
}

impl<'db> Argument<'db, '_> {
    fn new_argument(file: &'db PythonFile, node_index: NodeIndex) -> Self {
        Self::Positional(NodeRef { file, node_index })
    }

    fn new_keyword_argument(file: &'db PythonFile, name: &'db str, node_index: NodeIndex) -> Self {
        Self::Keyword(name, NodeRef { file, node_index })
    }

    pub fn infer(&self, i_s: &mut InferenceState<'db, '_>) -> Inferred<'db> {
        match self {
            Self::Value(instance) => instance
                .as_instance()
                .unwrap_or_else(|| todo!())
                .as_inferred()
                .clone(),
            Self::Positional(reference) => {
                reference
                    .file
                    // TODO this execution is wrong
                    .inference(i_s)
                    .infer_named_expression(reference.as_named_expression())
            }
            Self::Keyword(_, reference) => reference
                .file
                .inference(i_s)
                .infer_expression(reference.as_expression()),
        }
    }

    pub fn as_node_reference(&self) -> NodeRef<'db> {
        match self {
            Self::Positional(node_ref) => *node_ref,
            Self::Keyword(_, node_ref) => *node_ref,
            Self::Value(_) => {
                todo!("Probably happens with something weird like def foo(self: int)")
            }
        }
    }
}

pub enum ArgumentIteratorBase<'db> {
    Iterator(&'db PythonFile, ArgumentsIterator<'db>),
    Comprehension(&'db PythonFile, Comprehension<'db>),
    Finished,
}

pub enum ArgumentIterator<'db, 'a> {
    Normal(ArgumentIteratorBase<'db>),
    Instance(&'a dyn Value<'db, 'a>, &'a dyn Arguments<'db>),
    SliceType(SliceType<'db>),
}

impl<'db, 'a> Iterator for ArgumentIterator<'db, 'a> {
    type Item = Argument<'db, 'a>;

    fn next(&mut self) -> Option<Self::Item> {
        use ArgumentIteratorBase::*;
        match self {
            Self::Instance(_, _) => {
                if let Self::Instance(instance, args) = mem::replace(self, Self::Normal(Finished)) {
                    *self = args.iter_arguments();
                    Some(Argument::Value(instance))
                } else {
                    unreachable!()
                }
            }
            Self::Normal(Iterator(python_file, iterator)) => {
                for arg in iterator {
                    match arg {
                        ASTArgument::Positional(named_expr) => {
                            return Some(Self::Item::new_argument(python_file, named_expr.index()))
                        }
                        ASTArgument::Keyword(name, expr) => {
                            return Some(Self::Item::new_keyword_argument(
                                python_file,
                                name,
                                expr.index(),
                            ))
                        }
                        ASTArgument::Starred(expr) => todo!("*args"),
                        ASTArgument::DoubleStarred(expr) => todo!("**kwargs"),
                    }
                }
                None
            }
            Self::Normal(Comprehension(file, comprehension)) => {
                Some(Argument::new_argument(file, comprehension.index()))
            }
            Self::Normal(Finished) => None,
            Self::SliceType(slice_type) => match slice_type.unpack() {
                SliceTypeContent::Simple(s) => {
                    let file = s.file;
                    let named_expr = s.named_expr;
                    *self = Self::Normal(Finished);
                    Some(Self::Item::Positional(NodeRef {
                        file,
                        node_index: named_expr.index(),
                    }))
                }
                _ => todo!(),
            },
        }
    }
}

#[derive(Debug)]
pub struct NoArguments<'db>(NodeRef<'db>);

impl<'db> NoArguments<'db> {
    pub fn new(node_ref: NodeRef<'db>) -> Self {
        Self(node_ref)
    }
}

impl<'db> Arguments<'db> for NoArguments<'db> {
    fn iter_arguments(&self) -> ArgumentIterator<'db, '_> {
        ArgumentIterator::Normal(ArgumentIteratorBase::Finished)
    }

    fn outer_execution(&self) -> Option<&Execution> {
        None
    }

    fn as_execution(&self, function: &Function) -> Option<Execution> {
        None
    }

    fn type_(&self) -> ArgumentsType<'db> {
        todo!()
    }

    fn node_reference(&self) -> NodeRef<'db> {
        self.0
    }
}
