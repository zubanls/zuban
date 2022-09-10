use std::mem;

use crate::database::{
    ComplexPoint, Database, DbType, Execution, GenericsList, MroIndex, PointLink, TupleContent,
};
use crate::file::PythonFile;
use crate::file_state::File;
use crate::getitem::{SliceType, SliceTypeContent, Slices};
use crate::inference_state::{Context, InferenceState};
use crate::inferred::Inferred;
use crate::matching::{FormatData, ResultContext};
use crate::node_ref::NodeRef;
use crate::value::{Function, IteratorContent};
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
    i_s: InferenceState<'db, 'a>,
}

impl<'db, 'a> Arguments<'db> for SimpleArguments<'db, 'a> {
    fn iter_arguments(&self) -> ArgumentIterator<'db, '_> {
        ArgumentIterator::new(match self.details {
            ArgumentsDetails::Node(arguments) => ArgumentIteratorBase::Iterator(
                self.i_s.clone(),
                self.file,
                arguments.iter().enumerate(),
            ),
            ArgumentsDetails::Comprehension(comprehension) => {
                ArgumentIteratorBase::Comprehension(self.i_s.context, self.file, comprehension)
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

impl<'db, 'a> SimpleArguments<'db, 'a> {
    pub fn new(
        i_s: InferenceState<'db, 'a>,
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
            i_s,
        }
    }

    pub fn from_primary(
        i_s: InferenceState<'db, 'a>,
        file: &'db PythonFile,
        primary_node: Primary<'db>,
        in_: Option<&'a Execution>,
    ) -> Self {
        match primary_node.second() {
            PrimaryContent::Execution(details) => {
                Self::new(i_s, file, primary_node.index(), details, in_)
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

#[derive(Debug, Clone)]
pub enum Argument<'db, 'a> {
    // Can be used for classmethod class or self in bound methods
    Keyword(Context<'db, 'a>, &'a str, NodeRef<'db>),
    Inferred {
        inferred: Inferred<'db>,
        position: usize, // The position as a 1-based index
        node_ref: Option<NodeRef<'db>>,
    },
    Positional {
        context: Context<'db, 'a>,
        position: usize, // The position as a 1-based index
        node_ref: NodeRef<'db>,
    },
    SlicesTuple(Context<'db, 'a>, Slices<'db, 'a>),
}

impl<'db, 'a> Argument<'db, 'a> {
    fn new_positional_return(
        context: Context<'db, 'a>,
        position: usize,
        file: &'db PythonFile,
        node_index: NodeIndex,
    ) -> BaseArgumentReturn<'db, 'a> {
        BaseArgumentReturn::Argument(Argument::Positional {
            context,
            position,
            node_ref: NodeRef { file, node_index },
        })
    }

    fn new_keyword_return(
        context: Context<'db, 'a>,
        file: &'db PythonFile,
        name: &'a str,
        node_index: NodeIndex,
    ) -> BaseArgumentReturn<'db, 'a> {
        BaseArgumentReturn::Argument(Argument::Keyword(
            context,
            name,
            NodeRef { file, node_index },
        ))
    }
}

impl<'db, 'a> Argument<'db, 'a> {
    pub fn infer(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        result_context: ResultContext<'db, '_>,
    ) -> Inferred<'db> {
        match self {
            Self::Inferred { inferred, .. } => (*inferred).clone(),
            Self::Positional {
                context, node_ref, ..
            } => {
                let mut i_s = i_s.with_context(*context);
                node_ref
                    .file
                    // TODO this execution is wrong
                    .inference(&mut i_s)
                    .infer_named_expression_with_context(
                        node_ref.as_named_expression(),
                        result_context,
                    )
            }
            Self::Keyword(context, _, reference) => {
                let mut i_s = i_s.with_context(*context);
                reference
                    .file
                    .inference(&mut i_s)
                    .infer_expression_with_context(reference.as_expression(), result_context)
            }
            Self::SlicesTuple(context, slices) => {
                let mut i_s = i_s.with_context(*context);
                let parts = slices
                    .iter()
                    .map(|x| x.infer(&mut i_s).class_as_db_type(&mut i_s))
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
        match &self {
            Self::Positional { node_ref, .. } => *node_ref,
            Self::Keyword(_, _, node_ref) => *node_ref,
            Self::Inferred { node_ref, .. } => node_ref.unwrap_or_else(|| {
                todo!("Probably happens with something weird like def foo(self: int)")
            }),
            Self::SlicesTuple(_, slices) => todo!(),
        }
    }

    pub fn index(&self) -> String {
        match self {
            Self::Positional { position, .. } | Self::Inferred { position, .. } => {
                format!("{position}")
            }
            Self::Keyword(_, kw, _) => format!("{kw:?}"),
            Self::SlicesTuple(_, _) => todo!(),
        }
    }

    pub fn is_keyword_argument(&self) -> bool {
        matches!(self, Self::Keyword(_, _, _))
    }
}

#[derive(Debug)]
enum ArgumentIteratorBase<'db, 'a> {
    Iterator(
        InferenceState<'db, 'a>,
        &'db PythonFile,
        std::iter::Enumerate<ArgumentsIterator<'a>>,
    ),
    Comprehension(Context<'db, 'a>, &'db PythonFile, Comprehension<'a>),
    Inferred(&'a Inferred<'db>, Option<NodeRef<'db>>),
    SliceType(Context<'db, 'a>, SliceType<'db, 'a>),
    Finished,
}

enum BaseArgumentReturn<'db, 'a> {
    ArgsKwargs(ArgsKwargsIterator<'db, 'db>),
    Argument(Argument<'db, 'a>),
}

impl<'db, 'a> ArgumentIteratorBase<'db, 'a> {
    fn expect_i_s(&mut self) -> &mut InferenceState<'db, 'a> {
        if let Self::Iterator(i_s, ..) = self {
            i_s
        } else {
            unreachable!()
        }
    }
    fn into_argument_types(self) -> Vec<Box<str>> {
        match self {
            Self::Inferred(inf, _) => {
                // TODO for now we just skip this, because most of these are instances.
                //      Shouldn't this be something like:
                //      vec![inf.class_as_type(i_s).format(i_s, None, FormatStyle::Short)]
                vec![]
            }
            Self::Iterator(mut i_s, python_file, iterator) => iterator
                .map(|(_, arg)| {
                    let mut prefix = "".to_owned();
                    let mut inference = python_file.inference(&mut i_s);
                    let inf = match arg {
                        ASTArgument::Positional(named_expr) => {
                            inference.infer_named_expression(named_expr)
                        }
                        ASTArgument::Keyword(name, expr) => {
                            prefix = format!("{}=", name.as_code());
                            inference.infer_expression(expr)
                        }
                        ASTArgument::Starred(starred_expr) => {
                            prefix = "*".to_owned();
                            inference.infer_expression(starred_expr.expression())
                        }
                        ASTArgument::DoubleStarred(double_starred_expr) => {
                            prefix = "*".to_owned();
                            inference.infer_expression(double_starred_expr.expression())
                        }
                    };
                    format!(
                        "{prefix}{}",
                        inf.class_as_type(&mut i_s)
                            .format(&FormatData::new_short(i_s.db))
                    )
                    .into()
                })
                .collect(),
            Self::Comprehension(_, file, comprehension) => {
                todo!()
            }
            Self::Finished => vec![],
            Self::SliceType(_, slice_type) => match slice_type.unpack() {
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
    type Item = BaseArgumentReturn<'db, 'a>;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::Inferred(_, _) => {
                if let Self::Inferred(inf, node_ref) = mem::replace(self, Self::Finished) {
                    Some(BaseArgumentReturn::Argument(Argument::Inferred {
                        inferred: inf.clone(),
                        position: 1, // TODO this is probably a bad assumption
                        node_ref,
                    }))
                } else {
                    unreachable!()
                }
            }
            Self::Iterator(i_s, python_file, iterator) => {
                for (i, arg) in iterator {
                    match arg {
                        ASTArgument::Positional(named_expr) => {
                            return Some(Argument::new_positional_return(
                                i_s.context,
                                i + 1,
                                python_file,
                                named_expr.index(),
                            ))
                        }
                        ASTArgument::Keyword(name, expr) => {
                            return Some(Argument::new_keyword_return(
                                i_s.context,
                                python_file,
                                name.as_code(),
                                expr.index(),
                            ))
                        }
                        ASTArgument::Starred(starred_expr) => {
                            let inf = python_file
                                .inference(i_s)
                                .infer_expression(starred_expr.expression());
                            let node_ref = NodeRef::new(python_file, starred_expr.index());
                            return Some(BaseArgumentReturn::ArgsKwargs(
                                ArgsKwargsIterator::Args {
                                    iterator: inf.save_and_iter(i_s, node_ref),
                                    node_ref,
                                    position: i + 1,
                                },
                            ));
                        }
                        ASTArgument::DoubleStarred(expr) => todo!("**kwargs"),
                    }
                }
                None
            }
            Self::Comprehension(context, file, comprehension) => Some(
                Argument::new_positional_return(*context, 1, file, comprehension.index()),
            ),
            Self::Finished => None,
            Self::SliceType(context, slice_type) => match slice_type.unpack() {
                SliceTypeContent::Simple(s) => {
                    let file = s.file;
                    let named_expr = s.named_expr;
                    let context = *context;
                    *self = Self::Finished;
                    Some(Argument::new_positional_return(
                        context,
                        1,
                        file,
                        named_expr.index(),
                    ))
                }
                SliceTypeContent::Slices(slices) => Some(BaseArgumentReturn::Argument(
                    Argument::SlicesTuple(*context, slices),
                )),
                _ => todo!(),
            },
        }
    }
}

#[derive(Debug)]
pub struct ArgumentIterator<'db, 'a> {
    current: ArgumentIteratorBase<'db, 'a>,
    args_kwargs_iterator: ArgsKwargsIterator<'db, 'a>,
    next: Option<&'a dyn Arguments<'db>>,
}

impl<'db, 'a> ArgumentIterator<'db, 'a> {
    fn new(current: ArgumentIteratorBase<'db, 'a>) -> Self {
        Self {
            current,
            next: None,
            args_kwargs_iterator: ArgsKwargsIterator::None,
        }
    }

    pub fn new_slice(slice_type: SliceType<'db, 'a>, context: Context<'db, 'a>) -> Self {
        Self {
            current: ArgumentIteratorBase::SliceType(context, slice_type),
            args_kwargs_iterator: ArgsKwargsIterator::None,
            next: None,
        }
    }

    pub fn into_argument_types(mut self) -> Box<[Box<str>]> {
        let mut result = vec![];
        loop {
            result.extend(self.current.into_argument_types());
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
        match &mut self.args_kwargs_iterator {
            ArgsKwargsIterator::None => match self.current.next() {
                Some(BaseArgumentReturn::Argument(arg)) => Some(arg),
                Some(BaseArgumentReturn::ArgsKwargs(args_kwargs)) => {
                    self.args_kwargs_iterator = args_kwargs;
                    self.next()
                }
                None => {
                    if let Some(next) = self.next {
                        *self = next.iter_arguments();
                        self.next()
                    } else {
                        None
                    }
                }
            },
            ArgsKwargsIterator::Args {
                iterator,
                node_ref,
                position,
            } => {
                if let Some(inferred) = iterator.next(self.current.expect_i_s()) {
                    Some(Argument::Inferred {
                        inferred,
                        position: *position,
                        node_ref: Some(*node_ref),
                    })
                } else {
                    self.args_kwargs_iterator = ArgsKwargsIterator::None;
                    self.next()
                }
            }
            ArgsKwargsIterator::Kwargs(_) => {
                todo!()
            }
        }
    }
}

#[derive(Debug)]
enum ArgsKwargsIterator<'db, 'a> {
    Args {
        iterator: IteratorContent<'db, 'a>,
        position: usize,
        node_ref: NodeRef<'db>,
    },
    Kwargs(()),
    None,
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
