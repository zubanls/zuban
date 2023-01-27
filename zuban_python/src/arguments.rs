use std::mem;

use crate::database::{
    ComplexPoint, Database, DbType, Execution, MroIndex, ParamSpecUsage, PointLink, TupleContent,
    TypeOrTypeVarTuple,
};
use crate::diagnostics::IssueType;
use crate::file::File;
use crate::file::PythonFile;
use crate::getitem::{SliceType, SliceTypeContent, Slices};
use crate::inference_state::{Context, InferenceState};
use crate::inferred::Inferred;
use crate::matching::{ResultContext, Type};
use crate::node_ref::NodeRef;
use crate::value::{Function, IteratorContent};
use parsa_python_ast::{
    Argument as ASTArgument, ArgumentsDetails, ArgumentsIterator, Comprehension, NodeIndex,
    Primary, PrimaryContent,
};

pub trait ArgumentIterator<'db: 'a, 'a>: Iterator<Item = Argument<'db, 'a>> {
    fn drop_args_kwargs_iterator(&mut self);
}

impl<'db, 'a> ArgumentIterator<'db, 'a> for std::vec::IntoIter<Argument<'db, 'a>> {
    fn drop_args_kwargs_iterator(&mut self) {
        unreachable!()
    }
}

pub enum ArgumentsType<'a> {
    Normal(&'a PythonFile, NodeIndex),
}

pub trait Arguments<'db>: std::fmt::Debug {
    // Returns an iterator of arguments, where args are returned before kw args.
    // This is not the case in the grammar, but here we want that.
    fn iter_arguments(&self) -> ArgumentIteratorImpl<'db, '_>;
    fn outer_execution(&self) -> Option<&Execution>;
    fn as_execution(&self, function: &Function) -> Option<Execution>;
    fn type_(&self) -> ArgumentsType;
    fn as_node_ref(&self) -> NodeRef;
}

#[derive(Debug)]
pub struct SimpleArguments<'db, 'a> {
    // The node id of the grammar node called primary, which is defined like
    // primary "(" [arguments | comprehension] ")"
    file: &'a PythonFile,
    primary_node_index: NodeIndex,
    details: ArgumentsDetails<'a>,
    in_: Option<&'a Execution>,
    i_s: InferenceState<'db, 'a>,
}

impl<'db: 'a, 'a> Arguments<'db> for SimpleArguments<'db, 'a> {
    fn iter_arguments(&self) -> ArgumentIteratorImpl<'db, '_> {
        ArgumentIteratorImpl::new(match self.details {
            ArgumentsDetails::Node(arguments) => ArgumentIteratorBase::Iterator {
                i_s: self.i_s.clone(),
                file: self.file,
                iterator: arguments.iter().enumerate(),
                kwargs_before_star_args: {
                    let mut iterator = arguments.iter();
                    if iterator.any(|arg| matches!(arg, ASTArgument::Keyword(_, _))) {
                        if iterator.any(|arg| matches!(arg, ASTArgument::Starred(_))) {
                            Some(vec![])
                        } else {
                            None
                        }
                    } else {
                        None
                    }
                },
            },
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

    fn type_(&self) -> ArgumentsType {
        ArgumentsType::Normal(self.file, self.primary_node_index)
    }

    fn as_node_ref(&self) -> NodeRef {
        NodeRef::new(self.file, self.primary_node_index)
    }
}

impl<'db: 'a, 'a> SimpleArguments<'db, 'a> {
    pub fn new(
        i_s: InferenceState<'db, 'a>,
        file: &'a PythonFile,
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
        file: &'a PythonFile,
        primary_node: Primary<'a>,
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
pub struct KnownArguments<'a> {
    inferred: &'a Inferred,
    mro_index: MroIndex,
    node_ref: NodeRef<'a>,
}

impl<'db, 'a> Arguments<'db> for KnownArguments<'a> {
    fn iter_arguments(&self) -> ArgumentIteratorImpl<'db, '_> {
        ArgumentIteratorImpl::new(ArgumentIteratorBase::Inferred(self.inferred, self.node_ref))
    }

    fn outer_execution(&self) -> Option<&Execution> {
        todo!()
    }

    fn as_execution(&self, function: &Function) -> Option<Execution> {
        None
    }

    fn type_(&self) -> ArgumentsType {
        todo!()
    }

    fn as_node_ref(&self) -> NodeRef {
        self.node_ref
    }
}

impl<'a> KnownArguments<'a> {
    pub fn new(inferred: &'a Inferred, node_ref: NodeRef<'a>) -> Self {
        Self {
            inferred,
            node_ref,
            mro_index: MroIndex(0),
        }
    }

    pub fn with_mro_index(
        inferred: &'a Inferred,
        mro_index: MroIndex,
        node_ref: NodeRef<'a>,
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
    fn iter_arguments(&self) -> ArgumentIteratorImpl<'db, '_> {
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

    fn type_(&self) -> ArgumentsType {
        todo!()
    }

    fn as_node_ref(&self) -> NodeRef {
        self.args2.as_node_ref()
    }
}

impl<'db, 'a> CombinedArguments<'db, 'a> {
    pub fn new(args1: &'a dyn Arguments<'db>, args2: &'a dyn Arguments<'db>) -> Self {
        Self { args1, args2 }
    }
}

#[derive(Debug, Clone)]
pub enum ArgumentKind<'db, 'a> {
    // Can be used for classmethod class or self in bound methods
    Keyword {
        context: Context<'db, 'a>,
        key: &'a str,
        node_ref: NodeRef<'a>,
    },
    Inferred {
        inferred: Inferred,
        position: usize, // The position as a 1-based index
        node_ref: NodeRef<'a>,
        in_args_or_kwargs_and_arbitrary_len: bool,
        is_keyword: bool,
    },
    Positional {
        context: Context<'db, 'a>,
        position: usize, // The position as a 1-based index
        node_ref: NodeRef<'a>,
    },
    SlicesTuple {
        context: Context<'db, 'a>,
        slices: Slices<'a>,
    },
    ParamSpec {
        usage: ParamSpecUsage,
        node_ref: NodeRef<'a>,
        position: usize,
    },
}

impl<'db, 'a> ArgumentKind<'db, 'a> {
    fn new_positional_return(
        context: Context<'db, 'a>,
        position: usize,
        file: &'a PythonFile,
        node_index: NodeIndex,
    ) -> BaseArgumentReturn<'db, 'a> {
        BaseArgumentReturn::Argument(ArgumentKind::Positional {
            context,
            position,
            node_ref: NodeRef { file, node_index },
        })
    }

    fn new_keyword_return(
        context: Context<'db, 'a>,
        file: &'a PythonFile,
        key: &'a str,
        node_index: NodeIndex,
    ) -> BaseArgumentReturn<'db, 'a> {
        BaseArgumentReturn::Argument(ArgumentKind::Keyword {
            context,
            key,
            node_ref: NodeRef { file, node_index },
        })
    }
}

#[derive(Debug, Clone)]
pub struct Argument<'db, 'a> {
    pub kind: ArgumentKind<'db, 'a>,
    pub index: usize,
}

impl<'db, 'a> Argument<'db, 'a> {
    pub fn in_args_or_kwargs_and_arbitrary_len(&self) -> bool {
        match &self.kind {
            ArgumentKind::Inferred {
                in_args_or_kwargs_and_arbitrary_len,
                ..
            } => *in_args_or_kwargs_and_arbitrary_len,
            _ => false,
        }
    }

    pub fn infer(
        &self,
        i_s: &mut InferenceState<'db, '_>,
        result_context: &mut ResultContext,
    ) -> Inferred {
        match &self.kind {
            ArgumentKind::Inferred { inferred, .. } => (*inferred).clone(),
            ArgumentKind::Positional {
                context, node_ref, ..
            } => {
                let mut i_s = i_s.with_context(*context);
                if let Some(named_expr) = node_ref.maybe_named_expression() {
                    node_ref
                        .file
                        // TODO this execution is wrong
                        .inference(&mut i_s)
                        .infer_named_expression_with_context(named_expr, result_context)
                } else {
                    todo!("comprehension")
                }
            }
            ArgumentKind::Keyword {
                context, node_ref, ..
            } => {
                let mut i_s = i_s.with_context(*context);
                node_ref
                    .file
                    .inference(&mut i_s)
                    .infer_expression_with_context(node_ref.as_expression(), result_context)
            }
            ArgumentKind::SlicesTuple { context, slices } => {
                let mut i_s = i_s.with_context(*context);
                let parts = slices
                    .iter()
                    .map(|x| {
                        TypeOrTypeVarTuple::Type(
                            x.infer(&mut i_s, &mut ResultContext::Unknown)
                                .class_as_db_type(&mut i_s),
                        )
                    })
                    .collect();
                Inferred::new_unsaved_complex(ComplexPoint::TypeInstance(Box::new(DbType::Tuple(
                    TupleContent::new_fixed_length(parts),
                ))))
            }
            ArgumentKind::ParamSpec { usage, .. } => Inferred::new_unsaved_complex(
                ComplexPoint::TypeInstance(Box::new(DbType::ParamSpecArgs(usage.clone()))),
            ),
        }
    }

    pub fn as_node_ref(&self) -> NodeRef {
        match &self.kind {
            ArgumentKind::Positional { node_ref, .. }
            | ArgumentKind::Keyword { node_ref, .. }
            | ArgumentKind::ParamSpec { node_ref, .. }
            | ArgumentKind::Inferred { node_ref, .. } => *node_ref,
            ArgumentKind::SlicesTuple { slices, .. } => todo!(),
        }
    }

    pub fn human_readable_index(&self) -> String {
        match &self.kind {
            ArgumentKind::Positional { position, .. }
            | ArgumentKind::Inferred { position, .. }
            | ArgumentKind::ParamSpec { position, .. } => {
                format!("{position}")
            }
            ArgumentKind::Keyword { key, .. } => format!("{key:?}"),
            ArgumentKind::SlicesTuple { .. } => todo!(),
        }
    }

    pub fn is_keyword_argument(&self) -> bool {
        matches!(
            self.kind,
            ArgumentKind::Keyword { .. }
                | ArgumentKind::Inferred {
                    is_keyword: true,
                    ..
                }
        )
    }
}

#[derive(Debug)]
enum ArgumentIteratorBase<'db, 'a> {
    Iterator {
        i_s: InferenceState<'db, 'a>,
        file: &'a PythonFile,
        iterator: std::iter::Enumerate<ArgumentsIterator<'a>>,
        kwargs_before_star_args: Option<Vec<ASTArgument<'a>>>,
    },
    Comprehension(Context<'db, 'a>, &'a PythonFile, Comprehension<'a>),
    Inferred(&'a Inferred, NodeRef<'a>),
    SliceType(Context<'db, 'a>, SliceType<'a>),
    Finished,
}

enum BaseArgumentReturn<'db, 'a> {
    ArgsKwargs(ArgsKwargsIterator<'a>),
    Argument(ArgumentKind<'db, 'a>),
}

impl<'db, 'a> ArgumentIteratorBase<'db, 'a> {
    fn expect_i_s(&mut self) -> &mut InferenceState<'db, 'a> {
        if let Self::Iterator { i_s, .. } = self {
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
            Self::Iterator {
                mut i_s,
                file,
                iterator,
                ..
            } => iterator
                .map(|(_, arg)| {
                    let mut prefix = "".to_owned();
                    let mut inference = file.inference(&mut i_s);
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
                    format!("{prefix}{}", inf.format_short(&mut i_s)).into()
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
                    Some(BaseArgumentReturn::Argument(ArgumentKind::Inferred {
                        inferred: inf.clone(),
                        position: 1, // TODO this is probably a bad assumption
                        node_ref,
                        in_args_or_kwargs_and_arbitrary_len: false,
                        is_keyword: false,
                    }))
                } else {
                    unreachable!()
                }
            }
            Self::Iterator {
                i_s,
                file,
                iterator,
                kwargs_before_star_args,
            } => {
                for (i, arg) in iterator.by_ref() {
                    match arg {
                        ASTArgument::Positional(named_expr) => {
                            return Some(ArgumentKind::new_positional_return(
                                i_s.context,
                                i + 1,
                                file,
                                named_expr.index(),
                            ))
                        }
                        ASTArgument::Keyword(name, expr) => {
                            if let Some(kwargs_before_star_args) = kwargs_before_star_args {
                                kwargs_before_star_args.push(arg);
                            } else {
                                return Some(ArgumentKind::new_keyword_return(
                                    i_s.context,
                                    file,
                                    name.as_code(),
                                    expr.index(),
                                ));
                            }
                        }
                        ASTArgument::Starred(starred_expr) => {
                            let inf = file
                                .inference(i_s)
                                .infer_expression(starred_expr.expression());
                            let node_ref = NodeRef::new(file, starred_expr.index());
                            match inf.class_as_type(i_s).maybe_borrowed_db_type() {
                                Some(DbType::ParamSpecArgs(usage)) => {
                                    // TODO check for the next arg being **P.kwargs
                                    iterator.next();
                                    return Some(BaseArgumentReturn::Argument(
                                        ArgumentKind::ParamSpec {
                                            usage: usage.clone(),
                                            node_ref: NodeRef::new(file, starred_expr.index()),
                                            position: i + 1,
                                        },
                                    ));
                                }
                                _ => {
                                    return Some(BaseArgumentReturn::ArgsKwargs(
                                        ArgsKwargsIterator::Args {
                                            iterator: inf.save_and_iter(i_s, node_ref),
                                            node_ref,
                                            position: i + 1,
                                        },
                                    ));
                                }
                            }
                        }
                        ASTArgument::DoubleStarred(double_starred_expr) => {
                            let inf = file
                                .inference(i_s)
                                .infer_expression(double_starred_expr.expression());
                            let type_ = inf.class_as_type(i_s);
                            let node_ref = NodeRef::new(file, double_starred_expr.index());
                            let mut value_type = None;
                            if let Some(mro) = type_.mro(i_s) {
                                for (_, t) in mro {
                                    if let Some(class) = t.maybe_class(i_s.db) {
                                        if class.node_ref == i_s.db.python_state.mapping_node_ref()
                                        {
                                            let type_vars = class.type_vars(i_s).unwrap();
                                            let key = class
                                                .generics()
                                                .nth(i_s, &type_vars[0], 0)
                                                .expect_type_argument();
                                            let s = Type::Class(i_s.db.python_state.str());
                                            if !key.is_simple_same_type(i_s, &s).bool() {
                                                node_ref.add_typing_issue(
                                                    i_s.db,
                                                    IssueType::ArgumentIssue(Box::from(
                                                        "Keywords must be strings",
                                                    )),
                                                );
                                            }
                                            value_type = Some(
                                                class
                                                    .generics()
                                                    .nth(i_s, &type_vars[1], 1)
                                                    .expect_type_argument()
                                                    .into_db_type(i_s),
                                            );
                                            break;
                                        }
                                    }
                                }
                            } else if type_.maybe_db_type() == Some(&DbType::Any) {
                                value_type = Some(DbType::Any);
                            }
                            let value_type = value_type.unwrap_or_else(|| {
                                node_ref.add_typing_issue(
                                    i_s.db,
                                    IssueType::ArgumentIssue(
                                        format!(
                                            "Argument after ** must be a mapping, not \"{}\"",
                                            type_.format_short(i_s.db),
                                        )
                                        .into(),
                                    ),
                                );
                                DbType::Any
                            });
                            return Some(BaseArgumentReturn::ArgsKwargs(
                                ArgsKwargsIterator::Kwargs {
                                    inferred_value: Inferred::execute_db_type(i_s, value_type),
                                    node_ref,
                                    position: i + 1,
                                },
                            ));
                        }
                    }
                }
                if let Some(kwargs_before_star_args) = kwargs_before_star_args {
                    if let Some(kwarg_before_star_args) = kwargs_before_star_args.pop() {
                        match kwarg_before_star_args {
                            ASTArgument::Keyword(name, expr) => {
                                return Some(ArgumentKind::new_keyword_return(
                                    i_s.context,
                                    file,
                                    name.as_code(),
                                    expr.index(),
                                ))
                            }
                            _ => unreachable!(),
                        }
                    }
                }
                None
            }
            Self::Comprehension(context, file, comprehension) => Some(
                ArgumentKind::new_positional_return(*context, 1, file, comprehension.index()),
            ),
            Self::Finished => None,
            Self::SliceType(context, slice_type) => match slice_type.unpack() {
                SliceTypeContent::Simple(s) => {
                    let file = s.file;
                    let named_expr = s.named_expr;
                    let context = *context;
                    *self = Self::Finished;
                    Some(ArgumentKind::new_positional_return(
                        context,
                        1,
                        file,
                        named_expr.index(),
                    ))
                }
                SliceTypeContent::Slices(slices) => {
                    Some(BaseArgumentReturn::Argument(ArgumentKind::SlicesTuple {
                        context: *context,
                        slices,
                    }))
                }
                _ => todo!(),
            },
        }
    }
}

#[derive(Debug)]
pub struct ArgumentIteratorImpl<'db, 'a> {
    current: ArgumentIteratorBase<'db, 'a>,
    args_kwargs_iterator: ArgsKwargsIterator<'a>,
    next: Option<&'a dyn Arguments<'db>>,
    counter: usize,
}

impl<'db, 'a> ArgumentIteratorImpl<'db, 'a> {
    fn new(current: ArgumentIteratorBase<'db, 'a>) -> Self {
        Self {
            current,
            next: None,
            args_kwargs_iterator: ArgsKwargsIterator::None,
            counter: 0,
        }
    }

    pub fn new_slice(slice_type: SliceType<'a>, context: Context<'db, 'a>) -> Self {
        Self {
            current: ArgumentIteratorBase::SliceType(context, slice_type),
            args_kwargs_iterator: ArgsKwargsIterator::None,
            next: None,
            counter: 0,
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

    pub fn calculate_diagnostics(mut self, i_s: &mut InferenceState<'db, '_>) {
        while let Some(arg) = self.next() {
            arg.infer(i_s, &mut ResultContext::Unknown);
            if arg.in_args_or_kwargs_and_arbitrary_len() {
                self.drop_args_kwargs_iterator()
            }
        }
    }
}

impl<'db, 'a> ArgumentIterator<'db, 'a> for ArgumentIteratorImpl<'db, 'a> {
    fn drop_args_kwargs_iterator(&mut self) {
        self.args_kwargs_iterator = ArgsKwargsIterator::None;
    }
}

impl<'db, 'a> Iterator for ArgumentIteratorImpl<'db, 'a> {
    type Item = Argument<'db, 'a>;

    fn next(&mut self) -> Option<Self::Item> {
        match &mut self.args_kwargs_iterator {
            ArgsKwargsIterator::None => match self.current.next() {
                Some(BaseArgumentReturn::Argument(arg)) => {
                    let index = self.counter;
                    self.counter += 1;
                    Some(Argument { kind: arg, index })
                }
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
                    let index = self.counter;
                    self.counter += 1;
                    Some(Argument {
                        kind: ArgumentKind::Inferred {
                            inferred,
                            position: *position,
                            node_ref: *node_ref,
                            in_args_or_kwargs_and_arbitrary_len: iterator.len().is_none(),
                            is_keyword: false,
                        },
                        index,
                    })
                } else {
                    self.args_kwargs_iterator = ArgsKwargsIterator::None;
                    self.next()
                }
            }
            ArgsKwargsIterator::Kwargs {
                inferred_value,
                node_ref,
                position,
            } => {
                let index = self.counter;
                self.counter += 1;
                Some(Argument {
                    kind: ArgumentKind::Inferred {
                        inferred: inferred_value.clone(),
                        position: *position,
                        node_ref: *node_ref,
                        in_args_or_kwargs_and_arbitrary_len: true,
                        is_keyword: true,
                    },
                    index,
                })
            }
        }
    }
}

#[derive(Debug)]
enum ArgsKwargsIterator<'a> {
    Args {
        iterator: IteratorContent<'a>,
        position: usize,
        node_ref: NodeRef<'a>,
    },
    Kwargs {
        inferred_value: Inferred,
        position: usize,
        node_ref: NodeRef<'a>,
    },
    None,
}

#[derive(Debug)]
pub struct NoArguments<'a>(NodeRef<'a>);

impl<'a> NoArguments<'a> {
    pub fn new(node_ref: NodeRef<'a>) -> Self {
        Self(node_ref)
    }
}

impl<'db, 'a> Arguments<'db> for NoArguments<'a> {
    fn iter_arguments(&self) -> ArgumentIteratorImpl<'db, '_> {
        ArgumentIteratorImpl::new(ArgumentIteratorBase::Finished)
    }

    fn outer_execution(&self) -> Option<&Execution> {
        None
    }

    fn as_execution(&self, function: &Function) -> Option<Execution> {
        None
    }

    fn type_(&self) -> ArgumentsType {
        todo!()
    }

    fn as_node_ref(&self) -> NodeRef {
        self.0
    }
}
