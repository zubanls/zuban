use crate::database::{Database, Execution, PointLink};
use crate::file::PythonFile;
use crate::file_state::File;
use crate::inference_state::InferenceState;
use crate::inferred::{Inferred, NodeReference};
use crate::value::{Function, Instance};
use parsa_python::{NonterminalType, PyNode, PyNodeType::Nonterminal, SiblingIterator};
use std::mem;

pub enum ArgumentsType<'db> {
    Normal(&'db PythonFile, PyNode<'db>),
}

pub trait Arguments<'db>: std::fmt::Debug {
    fn iter_arguments(&self) -> ArgumentIterator<'db>;
    fn get_outer_execution(&self) -> Option<&Execution>;
    fn as_execution(&self, function: &Function) -> Execution;
    fn get_type(&self) -> ArgumentsType<'db>;
}

#[derive(Debug)]
enum SimpleArgumentsDetailed<'db> {
    None,
    Comprehension(PyNode<'db>),
    Node(PyNode<'db>),
}

#[derive(Debug)]
pub struct SimpleArguments<'db, 'a> {
    // The node id of the grammar node called primary, which is defined like
    // primary "(" [arguments | comprehension] ")"
    file: &'db PythonFile,
    primary_node: PyNode<'db>,
    details: SimpleArgumentsDetailed<'db>,
    in_: Option<&'a Execution>,
}

impl<'db, 'a> Arguments<'db> for SimpleArguments<'db, 'a> {
    fn iter_arguments(&self) -> ArgumentIterator<'db> {
        ArgumentIterator::Normal(self.get_argument_iterator_base())
    }

    fn get_outer_execution(&self) -> Option<&Execution> {
        self.in_
    }

    fn as_execution(&self, function: &Function) -> Execution {
        Execution::new(
            function.as_point_link(),
            PointLink::new(self.file.get_file_index(), self.primary_node.index),
            self.in_,
        )
    }

    fn get_type(&self) -> ArgumentsType<'db> {
        ArgumentsType::Normal(self.file, self.primary_node)
    }
}

impl<'db, 'a> SimpleArguments<'db, 'a> {
    pub fn new(f: &'db PythonFile, primary_node: PyNode<'db>, in_: Option<&'a Execution>) -> Self {
        use NonterminalType::*;
        debug_assert_eq!(primary_node.get_type(), Nonterminal(primary));
        let arguments_node = primary_node.get_nth_child(2);
        let details = if arguments_node.is_type(Nonterminal(arguments)) {
            SimpleArgumentsDetailed::Node(arguments_node)
        } else if arguments_node.is_type(Nonterminal(comprehension)) {
            SimpleArgumentsDetailed::Comprehension(arguments_node)
        } else {
            SimpleArgumentsDetailed::None
        };
        Self {
            file: f,
            primary_node,
            details,
            in_,
        }
    }

    pub fn from_execution(database: &'db Database, execution: &'a Execution) -> Self {
        let f = database.get_loaded_python_file(execution.argument_node.file);
        let primary_node = f.tree.get_node_by_index(execution.argument_node.node_index);
        Self::new(f, primary_node, execution.in_.as_deref())
    }

    pub fn get_argument_iterator_base(&self) -> ArgumentIteratorBase<'db> {
        use ArgumentIteratorBase::*;
        match self.details {
            SimpleArgumentsDetailed::Node(node) => Iterator(self.file, node.iter_children()),
            SimpleArgumentsDetailed::Comprehension(node) => Comprehension(self.file, node),
            SimpleArgumentsDetailed::None => Finished,
        }
    }
}

#[derive(Debug)]
pub struct InstanceArguments<'db, 'a> {
    // The node id of the grammar node called primary, which is defined like
    // primary "(" [arguments | comprehension] ")"
    arguments: SimpleArguments<'db, 'a>,
    instance: &'a Instance<'db>,
}

impl<'db, 'a> Arguments<'db> for InstanceArguments<'db, 'a> {
    fn iter_arguments(&self) -> ArgumentIterator<'db> {
        let args = self.arguments.iter_arguments();
        ArgumentIterator::Instance(
            self.instance.as_point_link(),
            self.arguments.get_argument_iterator_base(),
        )
    }

    fn get_outer_execution(&self) -> Option<&Execution> {
        self.arguments.get_outer_execution()
    }

    fn as_execution(&self, function: &Function) -> Execution {
        self.arguments.as_execution(function)
    }

    fn get_type(&self) -> ArgumentsType<'db> {
        self.arguments.get_type()
    }
}

impl<'db, 'a> InstanceArguments<'db, 'a> {
    pub fn new(
        instance: &'a Instance<'db>,
        f: &'db PythonFile,
        primary_node: PyNode<'db>,
        in_: Option<&'a Execution>,
    ) -> Self {
        Self {
            arguments: SimpleArguments::new(f, primary_node, in_),
            instance,
        }
    }

    pub fn from_execution(
        database: &'db Database,
        instance: &'a Instance<'db>,
        execution: &'a Execution,
    ) -> Self {
        Self {
            instance,
            arguments: SimpleArguments::from_execution(database, execution),
        }
    }
}

#[derive(Debug)]
pub enum Argument<'db> {
    Instance(PointLink),
    KeywordArgument(&'db str, NodeReference<'db>),
    Argument(NodeReference<'db>),
}

impl<'db> Argument<'db> {
    fn new_argument(file: &'db PythonFile, node: PyNode<'db>) -> Self {
        Self::Argument(NodeReference { file, node })
    }

    fn new_keyword_argument(file: &'db PythonFile, node: PyNode<'db>, name: &'db str) -> Self {
        Self::KeywordArgument(name, NodeReference { file, node })
    }

    pub fn infer(&self, i_s: &mut InferenceState<'db, '_>) -> Inferred<'db> {
        match self {
            Self::Instance(point_link) => {
                todo!()
            }
            Self::KeywordArgument(_, reference) | Self::Argument(reference) => {
                reference
                    .file
                    // TODO this execution is wrong
                    .get_inference(i_s)
                    .infer_named_expression(reference.node)
            }
        }
    }
}

pub enum ArgumentIteratorBase<'db> {
    Iterator(&'db PythonFile, SiblingIterator<'db>),
    Comprehension(&'db PythonFile, PyNode<'db>),
    Finished,
}

pub enum ArgumentIterator<'db> {
    Normal(ArgumentIteratorBase<'db>),
    Instance(PointLink, ArgumentIteratorBase<'db>),
}

impl<'db> Iterator for ArgumentIterator<'db> {
    type Item = Argument<'db>;

    fn next(&mut self) -> Option<Self::Item> {
        use ArgumentIteratorBase::*;
        match self {
            Self::Instance(_, _) => {
                if let Self::Instance(point_link, base) = mem::replace(self, Self::Normal(Finished))
                {
                    *self = Self::Normal(base);
                    Some(Argument::Instance(point_link))
                } else {
                    unreachable!()
                }
            }
            Self::Normal(Iterator(python_file, iterator)) => {
                for node in iterator {
                    use NonterminalType::*;
                    if node.is_type(Nonterminal(named_expression)) {
                        return Some(Self::Item::new_argument(python_file, node));
                    } else if node.is_type(Nonterminal(kwargs)) {
                        *self = Self::Normal(Iterator(python_file, node.iter_children()));
                        return self.next();
                    } else if node.is_type(Nonterminal(kwarg)) {
                        // kwarg: Name "=" expression
                        let mut kwarg_iterator = node.iter_children();
                        let name = kwarg_iterator.next().unwrap().get_code();
                        kwarg_iterator.next();
                        let arg = kwarg_iterator.next().unwrap();
                        return Some(Self::Item::new_keyword_argument(python_file, node, name));
                    } else if node.is_type(Nonterminal(starred_expression)) {
                        todo!("*args");
                    } else if node.is_type(Nonterminal(double_starred_expression)) {
                        todo!("**kwargs");
                    }
                }
                None
            }
            Self::Normal(Comprehension(file, node)) => Some(Argument::new_argument(file, *node)),
            Self::Normal(Finished) => None,
        }
    }
}
