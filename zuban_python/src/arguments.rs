use crate::database::{Database, Execution, PointLink};
use crate::file::PythonFile;
use crate::file_state::File;
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::value::Function;
use parsa::Node;
use parsa_python::{NonterminalType, PyNode, PyNodeType::Nonterminal, SiblingIterator};

#[derive(Debug)]
enum ArgumentsDetailed<'db> {
    None,
    Comprehension(PyNode<'db>),
    Node(PyNode<'db>),
}

#[derive(Debug)]
pub struct Arguments<'db, 'a> {
    // The node id of the grammar node called primary, which is defined like
    // primary "(" [arguments | comprehension] ")"
    pub file: &'db PythonFile,
    pub primary_node: PyNode<'db>,
    details: ArgumentsDetailed<'db>,
    pub in_: Option<&'a Execution>,
}

impl<'db, 'a> Arguments<'db, 'a> {
    pub fn new(f: &'db PythonFile, primary_node: PyNode<'db>, in_: Option<&'a Execution>) -> Self {
        use NonterminalType::*;
        debug_assert_eq!(primary_node.get_type(), Nonterminal(primary));
        let arguments_node = primary_node.get_nth_child(2);
        let details = if arguments_node.is_type(Nonterminal(arguments)) {
            ArgumentsDetailed::Node(arguments_node)
        } else if arguments_node.is_type(Nonterminal(comprehension)) {
            ArgumentsDetailed::Comprehension(arguments_node)
        } else {
            ArgumentsDetailed::None
        };
        Self {
            file: f,
            primary_node,
            details,
            in_,
        }
    }

    pub fn iter_arguments(&self) -> ArgumentIterator<'db> {
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

    pub fn from_execution(database: &'db Database, execution: &'a Execution) -> Self {
        let f = database.get_loaded_python_file(execution.argument_node.file);
        let primary_node = f.tree.get_node_by_index(execution.argument_node.node_index);
        Self::new(f, primary_node, execution.in_.as_deref())
    }

    pub fn as_execution(&self, function: &Function) -> Execution {
        Execution::new(
            function.as_point_link(),
            PointLink::new(self.file.get_file_index(), self.primary_node.index),
            self.in_,
        )
    }
}

#[derive(Debug)]
pub enum ArgumentType<'db> {
    KeywordArgument(&'db str),
    Argument,
}

#[derive(Debug)]
pub struct Argument<'db> {
    file: &'db PythonFile,
    node: PyNode<'db>,
    pub typ: ArgumentType<'db>,
}

impl<'db> Argument<'db> {
    fn new_argument(file: &'db PythonFile, node: PyNode<'db>) -> Self {
        Self {
            typ: ArgumentType::Argument,
            file,
            node,
        }
    }

    fn new_keyword_argument(file: &'db PythonFile, node: PyNode<'db>, name: &'db str) -> Self {
        Self {
            typ: ArgumentType::KeywordArgument(name),
            file,
            node,
        }
    }

    pub fn infer(&self, i_s: &mut InferenceState<'db, '_>) -> Inferred<'db> {
        self.file
            // TODO this execution is wrong
            .get_inference(i_s)
            .infer_named_expression(self.node)
    }
}

pub enum ArgumentIterator<'db> {
    Iterator(&'db PythonFile, SiblingIterator<'db>),
    Comprehension(&'db PythonFile, PyNode<'db>),
    Finished,
}

impl<'db> Iterator for ArgumentIterator<'db> {
    type Item = Argument<'db>;

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
