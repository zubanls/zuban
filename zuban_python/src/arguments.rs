use crate::database::{Database, Execution, PointLink};
use crate::file::PythonFile;
use crate::file_state::File;
use crate::inferred::Inferred;
use crate::value::Function;
use parsa::Node;
use parsa_python::{NonterminalType, PyNode, PyNodeType::Nonterminal, SiblingIterator};

enum ArgumentsDetailed<'a> {
    None,
    Comprehension(PyNode<'a>),
    Node(PyNode<'a>),
}

pub struct Arguments<'a> {
    // The node id of the grammar node called primary, which is defined like
    // primary "(" [arguments | comprehension] ")"
    pub file: &'a PythonFile,
    pub primary_node: PyNode<'a>,
    details: ArgumentsDetailed<'a>,
}

impl<'a> Arguments<'a> {
    pub fn new(
        f: &'a PythonFile,
        primary_node: PyNode<'a>,
        arguments_node: PyNode<'a>,
    ) -> Arguments<'a> {
        use NonterminalType::*;
        debug_assert_eq!(primary_node.get_type(), Nonterminal(primary));
        if arguments_node.is_type(Nonterminal(arguments)) {
            Arguments::new_with_arguments(f, primary_node, arguments_node)
        } else if arguments_node.is_type(Nonterminal(comprehension)) {
            Arguments::new_comprehension(f, primary_node, arguments_node)
        } else {
            Arguments::new_empty_arguments(f, primary_node)
        }
    }

    fn new_empty_arguments(file: &'a PythonFile, primary_node: PyNode<'a>) -> Self {
        Self {
            file,
            primary_node,
            details: ArgumentsDetailed::None,
        }
    }

    fn new_comprehension(
        file: &'a PythonFile,
        primary_node: PyNode<'a>,
        comprehension: PyNode<'a>,
    ) -> Self {
        Self {
            file,
            primary_node,
            details: ArgumentsDetailed::Comprehension(comprehension),
        }
    }

    fn new_with_arguments(
        file: &'a PythonFile,
        primary_node: PyNode<'a>,
        arguments: PyNode<'a>,
    ) -> Self {
        Self {
            file,
            primary_node,
            details: ArgumentsDetailed::Node(arguments),
        }
    }

    pub fn iter_arguments(&self) -> ArgumentIterator<'a> {
        match self.details {
            ArgumentsDetailed::Node(node) => {
                ArgumentIterator::Iterator(self.file, node.iter_children())
            }
            ArgumentsDetailed::Comprehension(node) => {
                ArgumentIterator::Comprehension(self.file, node)
            }
            ArgumentsDetailed::None => ArgumentIterator::Finished,
        }
    }

    pub fn as_execution(&self, function: &Function) -> Execution {
        function.as_execution(PointLink::new(
            self.file.get_file_index(),
            self.primary_node.index,
        ))
    }
}

pub enum ArgumentType<'a> {
    KeywordArgument(&'a str),
    Argument,
}

pub struct Argument<'a> {
    file: &'a PythonFile,
    node: PyNode<'a>,
    pub typ: ArgumentType<'a>,
}

impl<'a> Argument<'a> {
    fn new_argument(file: &'a PythonFile, node: PyNode<'a>) -> Self {
        Self {
            typ: ArgumentType::Argument,
            file,
            node,
        }
    }

    fn new_keyword_argument(file: &'a PythonFile, node: PyNode<'a>, name: &'a str) -> Self {
        Self {
            typ: ArgumentType::KeywordArgument(name),
            file,
            node,
        }
    }

    pub fn infer(&self, database: &'a Database) -> Inferred<'a> {
        self.file
            // TODO this execution is wrong
            .get_inference(database, None)
            .infer_named_expression(self.node)
    }
}

pub enum ArgumentIterator<'a> {
    Iterator(&'a PythonFile, SiblingIterator<'a>),
    Comprehension(&'a PythonFile, PyNode<'a>),
    Finished,
}

impl<'a> Iterator for ArgumentIterator<'a> {
    type Item = Argument<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::Iterator(python_file, iterator) => {
                for node in iterator {
                    use NonterminalType::*;
                    if node.is_type(Nonterminal(named_expression)) {
                        return Some(Self::Item::new_argument(python_file, node));
                    } else if node.is_type(Nonterminal(kwargs)) {
                        *self = Self::Iterator(python_file, node.iter_children());
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
            Self::Comprehension(file, node) => Some(Argument::new_argument(file, *node)),
            Self::Finished => None,
        }
    }
}
