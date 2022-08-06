use std::mem;

use crate::database::{
    ComplexPoint, Database, DbType, Execution, FormatStyle, GenericsList, MroIndex, PointLink,
    TupleContent,
};
use crate::file::PythonFile;
use crate::file_state::File;
use crate::getitem::{SliceType, SliceTypeContent, Slices};
use crate::inference_state::InferenceState;
use crate::inferred::Inferred;
use crate::node_ref::NodeRef;
use crate::value::Function;
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
    fn as_node_ref(&self) -> NodeRef<'db>;
}

#[derive(Debug)]
pub struct SimpleArguments<'db, 'a> {
    // The node id of the grammar node called primary, which is defined like
    // primary "(" [arguments | comprehension] ")"
    file: &'db PythonFile,
    primary_node_index: NodeIndex,
    details: ArgumentsDetails<'a>,
    in_: Option<&'a Execution>,
}

impl<'db, 'a> Arguments<'db> for SimpleArguments<'db, 'a> {
    fn iter_arguments(&self) -> ArgumentIterator<'db, '_> {
        ArgumentIterator::new(match self.details {
            ArgumentsDetails::Node(arguments) => {
                ArgumentIteratorBase::Iterator(self.file, arguments.iter().enumerate())
            }
            ArgumentsDetails::Comprehension(comprehension) => {
                ArgumentIteratorBase::Comprehension(self.file, comprehension)
            }
            ArgumentsDetails::None => ArgumentIteratorBase::Finished,
        })
    }

    fn outer_execution(&self) -> Option<&Execution> {
        self.in_
    }

    fn as_execution(&self, function: &Function) -> Option<Execution> {
        self.details.index().map(|index| {
            Execution::new(
                function.node_ref.as_link(),
                PointLink::new(self.file.file_index(), index),
                self.in_,
            )
        })
    }

    fn type_(&self) -> ArgumentsType<'db> {
        ArgumentsType::Normal(self.file, self.primary_node_index)
    }

    fn as_node_ref(&self) -> NodeRef<'db> {
        NodeRef::new(self.file, self.primary_node_index)
    }
}

impl<'db: 'a, 'a> SimpleArguments<'db, 'a> {
    pub fn new(
        file: &'db PythonFile,
        primary_node_index: NodeIndex,
        details: ArgumentsDetails<'a>,
        in_: Option<&'a Execution>,
    ) -> Self {
        Self {
            file,
            primary_node_index,
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
            PrimaryContent::Execution(details) => {
                Self::new(file, primary_node.index(), details, in_)
            }
            _ => unreachable!(),
        }
    }

    pub fn from_execution(db: &'db Database, execution: &'a Execution) -> Self {
        let f = db.loaded_python_file(execution.argument_node.file);
        todo!()
        // details = ...
        //Self::from_primary(f, primary, execution.in_.as_deref(), None)
    }
}

#[derive(Debug)]
pub struct KnownArguments<'db, 'a> {
    inferred: &'a Inferred<'db>,
    mro_index: MroIndex,
    node_ref: Option<NodeRef<'db>>,
}

impl<'db, 'a> Arguments<'db> for KnownArguments<'db, 'a> {
    fn iter_arguments(&self) -> ArgumentIterator<'db, '_> {
        ArgumentIterator::new(ArgumentIteratorBase::Inferred(self.inferred, self.node_ref))
    }

    fn outer_execution(&self) -> Option<&Execution> {
        todo!()
    }

    fn as_execution(&self, function: &Function) -> Option<Execution> {
        None
    }

    fn type_(&self) -> ArgumentsType<'db> {
        todo!()
    }

    fn as_node_ref(&self) -> NodeRef<'db> {
        todo!()
    }
}

impl<'db, 'a> KnownArguments<'db, 'a> {
    pub fn new(inferred: &'a Inferred<'db>, node_ref: Option<NodeRef<'db>>) -> Self {
        Self {
            inferred,
            node_ref,
            mro_index: MroIndex(0),
        }
    }

    pub fn with_mro_index(
        inferred: &'a Inferred<'db>,
        mro_index: MroIndex,
        node_ref: Option<NodeRef<'db>>,
    ) -> Self {
        Self {
            inferred,
            node_ref,
            mro_index,
        }
    }
}

#[derive(Debug)]
pub struct CombinedArguments<'db, 'a> {
    args1: &'a dyn Arguments<'db>,
    args2: &'a dyn Arguments<'db>,
}

impl<'db, 'a> Arguments<'db> for CombinedArguments<'db, 'a> {
    fn iter_arguments(&self) -> ArgumentIterator<'db, '_> {
        let mut iterator = self.args1.iter_arguments();
        debug_assert!(iterator.next.is_none()); // For now this is not supported
        iterator.next = Some(self.args2);
        iterator
    }

    fn outer_execution(&self) -> Option<&Execution> {
        todo!()
    }

    fn as_execution(&self, function: &Function) -> Option<Execution> {
        None
    }

    fn type_(&self) -> ArgumentsType<'db> {
        todo!()
    }

    fn as_node_ref(&self) -> NodeRef<'db> {
        self.args2.as_node_ref()
    }
}

impl<'db, 'a> CombinedArguments<'db, 'a> {
    pub fn new(args1: &'a dyn Arguments<'db>, args2: &'a dyn Arguments<'db>) -> Self {
        Self { args1, args2 }
    }
}

#[derive(Debug, Copy, Clone)]
pub enum Argument<'db, 'a> {
    // Can be used for classmethod class or self in bound methods
    Keyword(&'a str, NodeRef<'db>),
    Inferred(&'a Inferred<'db>, Option<NodeRef<'db>>),
    // The first argument is the position as a 1-based index
    Positional(usize, NodeRef<'db>),
    SlicesTuple(Slices<'db, 'a>),
}

impl<'db, 'a> Argument<'db, 'a> {
    fn new_argument(position: usize, file: &'db PythonFile, node_index: NodeIndex) -> Self {
        Self::Positional(position, NodeRef { file, node_index })
    }

    fn new_keyword_argument(file: &'db PythonFile, name: &'a str, node_index: NodeIndex) -> Self {
        Self::Keyword(name, NodeRef { file, node_index })
    }

    pub fn infer(&self, i_s: &mut InferenceState<'db, '_>) -> Inferred<'db> {
        match self {
            Self::Inferred(inferred, _) => (*inferred).clone(),
            Self::Positional(_, reference) => {
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
            Self::SlicesTuple(slices) => {
                let parts = slices
                    .iter()
                    .map(|x| x.infer(i_s).class_as_db_type(i_s))
                    .collect();
                Inferred::new_unsaved_complex(ComplexPoint::TypeInstance(Box::new(DbType::Tuple(
                    TupleContent {
                        generics: Some(GenericsList::new_generics(parts)),
                        arbitrary_length: false,
                    },
                ))))
            }
        }
    }

    pub fn as_node_ref(&self) -> NodeRef<'db> {
        match self {
            Self::Positional(_, node_ref) => *node_ref,
            Self::Keyword(_, node_ref) => *node_ref,
            Self::Inferred(_, node_ref) => node_ref.unwrap_or_else(|| {
                todo!("Probably happens with something weird like def foo(self: int)")
            }),
            Self::SlicesTuple(slices) => todo!(),
        }
    }

    pub fn index(&self) -> String {
        match self {
            Self::Positional(index, _) => format!("{index}"),
            Self::Keyword(kw, _) => format!("{kw:?}"),
            Self::Inferred(_, _) => "1".to_owned(), // TODO this is not correct
            Self::SlicesTuple(_) => todo!(),
        }
    }

    pub fn is_keyword_argument(&self) -> bool {
        matches!(self, Argument::Keyword(_, _))
    }
}

#[derive(Debug)]
enum ArgumentIteratorBase<'db, 'a> {
    Iterator(&'db PythonFile, std::iter::Enumerate<ArgumentsIterator<'a>>),
    Comprehension(&'db PythonFile, Comprehension<'a>),
    Inferred(&'a Inferred<'db>, Option<NodeRef<'db>>),
    SliceType(SliceType<'db, 'a>),
    Finished,
}

impl<'db, 'a> ArgumentIteratorBase<'db, 'a> {
    fn into_argument_types(self, i_s: &mut InferenceState<'db, '_>) -> Vec<Box<str>> {
        match self {
            Self::Inferred(inf, _) => {
                // TODO for now we just skip this, because most of these are instances.
                //      Shouldn't this be something like:
                //      vec![inf.class_as_type(i_s).format(i_s, None, FormatStyle::Short)]
                vec![]
            }
            Self::Iterator(python_file, iterator) => iterator
                .map(|(_, arg)| {
                    let mut prefix = "".to_owned();
                    let mut inference = python_file.inference(i_s);
                    let inf = match arg {
                        ASTArgument::Positional(named_expr) => {
                            inference.infer_named_expression(named_expr)
                        }
                        ASTArgument::Keyword(name, expr) => {
                            prefix = format!("{name}=");
                            inference.infer_expression(expr)
                        }
                        ASTArgument::Starred(expr) => {
                            prefix = "*".to_owned();
                            inference.infer_expression(expr)
                        }
                        ASTArgument::DoubleStarred(expr) => {
                            prefix = "*".to_owned();
                            inference.infer_expression(expr)
                        }
                    };
                    format!(
                        "{prefix}{}",
                        inf.class_as_type(i_s).format(i_s, None, FormatStyle::Short)
                    )
                    .into()
                })
                .collect(),
            Self::Comprehension(file, comprehension) => {
                todo!()
            }
            Self::Finished => vec![],
            Self::SliceType(slice_type) => match slice_type.unpack() {
                SliceTypeContent::Simple(s) => {
                    let file = s.file;
                    let named_expr = s.named_expr;
                    todo!()
                }
                SliceTypeContent::Slices(slices) => todo!(),
                _ => todo!(),
            },
        }
    }
}

impl<'db, 'a> Iterator for ArgumentIteratorBase<'db, 'a> {
    type Item = Argument<'db, 'a>;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::Inferred(_, _) => {
                if let Self::Inferred(inf, node_ref) = mem::replace(self, Self::Finished) {
                    Some(Argument::Inferred(inf, node_ref))
                } else {
                    unreachable!()
                }
            }
            Self::Iterator(python_file, iterator) => {
                for (i, arg) in iterator {
                    match arg {
                        ASTArgument::Positional(named_expr) => {
                            return Some(Self::Item::new_argument(
                                i + 1,
                                python_file,
                                named_expr.index(),
                            ))
                        }
                        ASTArgument::Keyword(name, expr) => {
                            return Some(Self::Item::new_keyword_argument(
                                python_file,
                                name,
                                expr.index(),
                            ))
                        }
                        ASTArgument::Starred(expr) => todo!("*args {arg:?}"),
                        ASTArgument::DoubleStarred(expr) => todo!("**kwargs"),
                    }
                }
                None
            }
            Self::Comprehension(file, comprehension) => {
                Some(Argument::new_argument(1, file, comprehension.index()))
            }
            Self::Finished => None,
            Self::SliceType(slice_type) => match slice_type.unpack() {
                SliceTypeContent::Simple(s) => {
                    let file = s.file;
                    let named_expr = s.named_expr;
                    *self = Self::Finished;
                    Some(Self::Item::Positional(
                        1,
                        NodeRef {
                            file,
                            node_index: named_expr.index(),
                        },
                    ))
                }
                SliceTypeContent::Slices(slices) => Some(Self::Item::SlicesTuple(slices)),
                _ => todo!(),
            },
        }
    }
}

#[derive(Debug)]
pub struct ArgumentIterator<'db, 'a> {
    current: ArgumentIteratorBase<'db, 'a>,
    next: Option<&'a dyn Arguments<'db>>,
}

impl<'db, 'a> ArgumentIterator<'db, 'a> {
    fn new(current: ArgumentIteratorBase<'db, 'a>) -> Self {
        Self {
            current,
            next: None,
        }
    }

    pub fn new_slice(slice_type: SliceType<'db, 'a>) -> Self {
        Self {
            current: ArgumentIteratorBase::SliceType(slice_type),
            next: None,
        }
    }

    pub fn into_argument_types(mut self, i_s: &mut InferenceState<'db, '_>) -> Box<[Box<str>]> {
        let mut result = vec![];
        loop {
            result.extend(self.current.into_argument_types(i_s));
            if let Some(next) = self.next {
                self = next.iter_arguments();
            } else {
                break;
            }
        }
        result.into_boxed_slice()
    }
}

impl<'db, 'a> Iterator for ArgumentIterator<'db, 'a> {
    type Item = Argument<'db, 'a>;

    fn next(&mut self) -> Option<Self::Item> {
        self.current.next().or_else(|| {
            if let Some(next) = self.next {
                *self = next.iter_arguments();
                self.next()
            } else {
                None
            }
        })
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
        ArgumentIterator::new(ArgumentIteratorBase::Finished)
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

    fn as_node_ref(&self) -> NodeRef<'db> {
        self.0
    }
}
