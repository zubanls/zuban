use crate::database::{Database, Execution, PointLink};
use crate::file::PythonFile;
use crate::file_state::File;
use crate::inference_state::InferenceState;
use crate::inferred::{Inferred, NodeReference};
use crate::value::{Function, Instance};
use parsa_python_ast::{
    Argument as ASTArgument, ArgumentsDetails, ArgumentsIterator, Comprehension, NodeIndex,
    Primary, PrimaryContent,
};
use std::mem;

pub enum ArgumentsType<'db> {
    Normal(&'db PythonFile, Primary<'db>),
}

pub trait Arguments<'db>: std::fmt::Debug {
    fn iter_arguments(&self) -> ArgumentIterator<'db>;
    fn get_outer_execution(&self) -> Option<&Execution>;
    fn as_execution(&self, function: &Function) -> Execution;
    fn get_type(&self) -> ArgumentsType<'db>;
}

#[derive(Debug)]
pub struct SimpleArguments<'db, 'a> {
    // The node id of the grammar node called primary, which is defined like
    // primary "(" [arguments | comprehension] ")"
    file: &'db PythonFile,
    primary_node: Primary<'db>,
    details: ArgumentsDetails<'db>,
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
            PointLink::new(self.file.get_file_index(), self.primary_node.index()),
            self.in_,
        )
    }

    fn get_type(&self) -> ArgumentsType<'db> {
        ArgumentsType::Normal(self.file, self.primary_node)
    }
}

impl<'db, 'a> SimpleArguments<'db, 'a> {
    pub fn new(
        file: &'db PythonFile,
        primary_node: Primary<'db>,
        details: ArgumentsDetails<'db>,
        in_: Option<&'a Execution>,
    ) -> Self {
        Self {
            file,
            primary_node,
            details,
            in_,
        }
    }

    pub fn from_primary(
        file: &'db PythonFile,
        primary_node: Primary<'db>,
        in_: Option<&'a Execution>,
    ) -> Self {
        match primary_node.second() {
            PrimaryContent::Execution(details) => Self::new(file, primary_node, details, in_),
            _ => unreachable!(),
        }
    }

    pub fn from_execution(database: &'db Database, execution: &'a Execution) -> Self {
        let f = database.get_loaded_python_file(execution.argument_node.file);
        let primary = Primary::by_index(&f.tree, execution.argument_node.node_index);
        Self::from_primary(f, primary, execution.in_.as_deref())
    }

    pub fn get_argument_iterator_base(&self) -> ArgumentIteratorBase<'db> {
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
    pub fn from_primary(
        instance: &'a Instance<'db>,
        f: &'db PythonFile,
        primary_node: Primary<'db>,
        in_: Option<&'a Execution>,
    ) -> Self {
        Self {
            arguments: SimpleArguments::from_primary(f, primary_node, in_),
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
    PositionalInstance(PointLink),
    Keyword(&'db str, NodeReference<'db>),
    Positional(NodeReference<'db>),
}

impl<'db> Argument<'db> {
    fn new_argument(file: &'db PythonFile, node_index: NodeIndex) -> Self {
        Self::Positional(NodeReference { file, node_index })
    }

    fn new_keyword_argument(file: &'db PythonFile, name: &'db str, node_index: NodeIndex) -> Self {
        Self::Keyword(name, NodeReference { file, node_index })
    }

    pub fn infer(&self, i_s: &mut InferenceState<'db, '_>) -> Inferred<'db> {
        match self {
            Self::PositionalInstance(point_link) => {
                todo!()
            }
            Self::Keyword(_, reference) | Self::Positional(reference) => {
                reference
                    .file
                    // TODO this execution is wrong
                    .get_inference(i_s)
                    .infer_named_expression(reference.node())
            }
        }
    }
}

pub enum ArgumentIteratorBase<'db> {
    Iterator(&'db PythonFile, ArgumentsIterator<'db>),
    Comprehension(&'db PythonFile, Comprehension<'db>),
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
                    Some(Argument::PositionalInstance(point_link))
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
        }
    }
}
