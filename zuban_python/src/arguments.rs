use crate::file::PythonFile;
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
    pub fn new_empty_arguments(file: &'a PythonFile, primary_node: PyNode<'a>) -> Self {
        Self {
            file,
            primary_node,
            details: ArgumentsDetailed::None,
        }
    }

    pub fn new_comprehension(
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

    pub fn new_with_arguments(
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

    pub fn iter_arguments(&self) -> impl Iterator<Item = Argument<'a>> {
        match self.details {
            ArgumentsDetailed::Node(node) => ArgumentIterator::Iterator(node.iter_children()),
            ArgumentsDetailed::Comprehension(node) => ArgumentIterator::Comprehension(node),
            ArgumentsDetailed::None => ArgumentIterator::Finished,
        }
    }
}

enum ArgumentType<'a> {
    KeywordArgument(&'a str),
    Argument,
}

pub struct Argument<'a> {
    typ: ArgumentType<'a>,
}

impl<'a> Argument<'a> {
    fn new_argument() -> Self {
        Self {
            typ: ArgumentType::Argument,
        }
    }

    fn new_keyword_argument(name: &'a str) -> Self {
        Self {
            typ: ArgumentType::KeywordArgument(name),
        }
    }
}

enum ArgumentIterator<'a> {
    Iterator(SiblingIterator<'a>),
    Comprehension(PyNode<'a>),
    Finished,
}

impl<'a> Iterator for ArgumentIterator<'a> {
    type Item = Argument<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::Iterator(iterator) => {
                for node in iterator {
                    use NonterminalType::*;
                    if node.is_type(Nonterminal(named_expression)) {
                        return Some(Self::Item::new_argument());
                    } else if node.is_type(Nonterminal(kwargs)) {
                        *self = Self::Iterator(node.iter_children());
                        return self.next();
                    } else if node.is_type(Nonterminal(kwarg)) {
                        // kwarg: Name "=" expression
                        let mut kwarg_iterator = node.iter_children();
                        let name = kwarg_iterator.next().unwrap().get_code();
                        kwarg_iterator.next();
                        let arg = kwarg_iterator.next().unwrap();
                        return Some(Self::Item::new_keyword_argument(name));
                    } else if node.is_type(Nonterminal(starred_expression)) {
                        todo!("*args");
                    } else if node.is_type(Nonterminal(double_starred_expression)) {
                        todo!("**kwargs");
                    }
                }
                None
            }
            Self::Comprehension(node) => Some(Argument::new_argument()),
            Self::Finished => None,
        }
    }
}
