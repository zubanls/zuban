use std::{mem, rc::Rc};

use parsa_python_ast::{
    Argument as ASTArgument, ArgumentsDetails, ArgumentsIterator, Comprehension, Expression,
    NodeIndex, Primary, PrimaryContent,
};

use crate::{
    database::{Database, PointsBackup},
    debug,
    diagnostics::IssueType,
    file::PythonFile,
    getitem::{SliceType, SliceTypeContent, Slices},
    inferred::Inferred,
    matching::{IteratorContent, Matcher, ResultContext},
    node_ref::NodeRef,
    type_::{AnyCause, GenericItem, ParamSpecUsage, StringSlice, Type, TypedDict, Variance},
    InferenceState,
};

pub enum ArgumentsType<'a> {
    Normal(&'a PythonFile, NodeIndex),
}

pub(crate) trait Arguments<'db>: std::fmt::Debug {
    // Returns an iterator of arguments, where args are returned before kw args.
    // This is not the case in the grammar, but here we want that.
    fn iter(&self) -> ArgumentIterator<'db, '_>;
    fn type_(&self) -> ArgumentsType;
    fn as_node_ref(&self) -> NodeRef;
    fn add_issue(&self, i_s: &InferenceState, issue: IssueType) {
        self.as_node_ref().add_issue(i_s, issue)
    }
    fn starting_line(&self) -> String {
        self.as_node_ref().line().to_string()
    }
    fn points_backup(&self) -> Option<PointsBackup> {
        None
    }
    fn reset_points_from_backup(&self, backup: &Option<PointsBackup>) {
        // This is a bit special, but we use this to reset the type cache of the expressions to
        // avoid overload context inference issues.
    }

    fn has_a_union_argument(&self, i_s: &InferenceState<'db, '_>) -> bool {
        for arg in self.iter() {
            if arg.infer(i_s, &mut ResultContext::Unknown).is_union(i_s) {
                return true;
            }
        }
        false
    }

    fn maybe_two_positional_args(&self, db: &'db Database) -> Option<(NodeRef<'db>, NodeRef<'db>)> {
        let mut iterator = self.iter();
        let Some(first_arg) = iterator.next() else {
            return None
        };
        let ArgumentKind::Positional { node_ref: node_ref1, .. } = first_arg.kind else {
            return None
        };
        let Some(second_arg) = iterator.next() else {
            return None
        };
        let ArgumentKind::Positional { node_ref: node_ref2, .. } = second_arg.kind else {
            return None
        };
        if iterator.next().is_some() {
            return None;
        }
        Some((node_ref1.to_db_lifetime(db), node_ref2.to_db_lifetime(db)))
    }

    fn maybe_single_positional_arg(
        &self,
        i_s: &InferenceState<'db, '_>,
        context: &mut ResultContext,
    ) -> Option<Inferred> {
        let mut iterator = self.iter();
        let first = iterator.next()?;
        if iterator.next().is_some() {
            return None;
        }
        first.maybe_positional_arg(i_s, context)
    }
}

#[derive(Debug)]
pub struct SimpleArguments<'db, 'a> {
    // The node id of the grammar node called primary, which is defined like
    // primary "(" [arguments | comprehension] ")"
    file: &'a PythonFile,
    primary_node_index: NodeIndex,
    details: ArgumentsDetails<'a>,
    i_s: InferenceState<'db, 'a>,
}

impl<'db: 'a, 'a> Arguments<'db> for SimpleArguments<'db, 'a> {
    fn iter(&self) -> ArgumentIterator<'db, '_> {
        ArgumentIterator::new(match self.details {
            ArgumentsDetails::Node(arguments) => ArgumentIteratorBase::Iterator {
                i_s: self.i_s,
                file: self.file,
                iterator: arguments.iter().enumerate(),
                kwargs_before_star_args: {
                    let mut iterator = arguments.iter();
                    if iterator.any(|arg| matches!(arg, ASTArgument::Keyword(_))) {
                        if iterator.any(|arg| matches!(arg, ASTArgument::Star(_))) {
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
                ArgumentIteratorBase::Comprehension(self.i_s, self.file, comprehension)
            }
            ArgumentsDetails::None => ArgumentIteratorBase::Finished,
        })
    }

    fn type_(&self) -> ArgumentsType {
        ArgumentsType::Normal(self.file, self.primary_node_index)
    }

    fn as_node_ref(&self) -> NodeRef {
        NodeRef::new(self.file, self.primary_node_index)
    }

    fn points_backup(&self) -> Option<PointsBackup> {
        let primary = NodeRef::new(self.file, self.primary_node_index).as_primary();
        let start = primary.index();
        let end = primary.expect_closing_bracket_index();
        Some(self.file.points.backup(start..end))
    }

    fn reset_points_from_backup(&self, backup: &Option<PointsBackup>) {
        // Details is empty when no arguments are provided (e.g. `foo()`), which means we do not
        // have to reset the cache.
        self.file.points.reset_from_backup(backup.as_ref().unwrap());
    }
}

impl<'db: 'a, 'a> SimpleArguments<'db, 'a> {
    pub fn new(
        i_s: InferenceState<'db, 'a>,
        file: &'a PythonFile,
        primary_node_index: NodeIndex,
        details: ArgumentsDetails<'a>,
    ) -> Self {
        Self {
            file,
            primary_node_index,
            details,
            i_s,
        }
    }

    pub fn from_primary(
        i_s: InferenceState<'db, 'a>,
        file: &'a PythonFile,
        primary_node: Primary<'a>,
    ) -> Self {
        match primary_node.second() {
            PrimaryContent::Execution(details) => {
                Self::new(i_s, file, primary_node.index(), details)
            }
            _ => unreachable!(),
        }
    }
}

#[derive(Debug)]
pub struct KnownArguments<'a> {
    inferred: &'a Inferred,
    node_ref: NodeRef<'a>,
}

impl<'db, 'a> Arguments<'db> for KnownArguments<'a> {
    fn iter(&self) -> ArgumentIterator<'db, '_> {
        ArgumentIterator::new(ArgumentIteratorBase::Inferred {
            inferred: self.inferred,
            node_ref: self.node_ref,
        })
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
        Self { inferred, node_ref }
    }
}

#[derive(Debug)]
pub struct CombinedArguments<'db, 'a> {
    args1: &'a dyn Arguments<'db>,
    args2: &'a dyn Arguments<'db>,
}

impl<'db, 'a> Arguments<'db> for CombinedArguments<'db, 'a> {
    fn iter(&self) -> ArgumentIterator<'db, '_> {
        let mut iterator = self.args1.iter();
        debug_assert!(iterator.next.is_none()); // For now this is not supported
        iterator.next = Some(self.args2);
        iterator
    }

    fn type_(&self) -> ArgumentsType {
        todo!()
    }

    fn as_node_ref(&self) -> NodeRef {
        self.args2.as_node_ref()
    }

    fn points_backup(&self) -> Option<PointsBackup> {
        debug_assert!(self.args1.points_backup().is_none());
        self.args2.points_backup()
    }

    fn reset_points_from_backup(&self, backup: &Option<PointsBackup>) {
        self.args1.reset_points_from_backup(backup);
        self.args2.reset_points_from_backup(backup);
    }
}

impl<'db, 'a> CombinedArguments<'db, 'a> {
    pub(crate) fn new(args1: &'a dyn Arguments<'db>, args2: &'a dyn Arguments<'db>) -> Self {
        Self { args1, args2 }
    }
}

#[derive(Debug, Clone)]
pub enum ArgumentKind<'db, 'a> {
    // Can be used for classmethod class or self in bound methods
    Keyword {
        i_s: InferenceState<'db, 'a>,
        key: &'a str,
        node_ref: NodeRef<'a>,
        expression: Expression<'a>,
    },
    Inferred {
        inferred: Inferred,
        position: usize, // The position as a 1-based index
        node_ref: NodeRef<'a>,
        in_args_or_kwargs_and_arbitrary_len: bool,
        is_keyword: Option<Option<StringSlice>>,
    },
    Positional {
        i_s: InferenceState<'db, 'a>,
        position: usize, // The position as a 1-based index
        node_ref: NodeRef<'a>,
    },
    SlicesTuple {
        i_s: InferenceState<'db, 'a>,
        slices: Slices<'a>,
    },
    ParamSpec {
        usage: ParamSpecUsage,
        node_ref: NodeRef<'a>,
        position: usize,
    },
    Comprehension {
        i_s: InferenceState<'db, 'a>,
        file: &'a PythonFile,
        comprehension: Comprehension<'a>,
    },
    Overridden {
        original: &'a Argument<'db, 'a>,
        inferred: Inferred,
    },
}

impl<'db, 'a> ArgumentKind<'db, 'a> {
    fn new_positional_return(
        i_s: InferenceState<'db, 'a>,
        position: usize,
        file: &'a PythonFile,
        node_index: NodeIndex,
    ) -> BaseArgumentReturn<'db, 'a> {
        BaseArgumentReturn::Argument(ArgumentKind::Positional {
            i_s,
            position,
            node_ref: NodeRef { file, node_index },
        })
    }

    fn new_keyword_return(
        i_s: InferenceState<'db, 'a>,
        file: &'a PythonFile,
        key: &'a str,
        node_index: NodeIndex,
        expression: Expression<'a>,
    ) -> BaseArgumentReturn<'db, 'a> {
        BaseArgumentReturn::Argument(ArgumentKind::Keyword {
            i_s,
            key,
            node_ref: NodeRef { file, node_index },
            expression,
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
        func_i_s: &InferenceState<'db, '_>,
        result_context: &mut ResultContext,
    ) -> Inferred {
        match &self.kind {
            ArgumentKind::Inferred { inferred, .. } => (*inferred).clone(),
            ArgumentKind::Positional { i_s, node_ref, .. } => {
                node_ref
                    .file
                    // TODO this execution is wrong
                    .inference(&i_s.use_mode_of(func_i_s))
                    .infer_named_expression_with_context(
                        node_ref.as_named_expression(),
                        result_context,
                    )
            }
            ArgumentKind::Keyword {
                i_s,
                node_ref,
                expression,
                ..
            } => node_ref
                .file
                .inference(&i_s.use_mode_of(func_i_s))
                .infer_expression_with_context(*expression, result_context),
            ArgumentKind::SlicesTuple { i_s, slices } => slices.infer(&i_s.use_mode_of(func_i_s)),
            ArgumentKind::Comprehension {
                file,
                comprehension,
                i_s,
            } => file
                .inference(&i_s.use_mode_of(func_i_s))
                .infer_generator_comprehension(*comprehension, result_context),
            ArgumentKind::ParamSpec { usage, .. } => {
                Inferred::from_type(Type::ParamSpecArgs(usage.clone()))
            }
            ArgumentKind::Overridden { inferred, .. } => inferred.clone(),
        }
    }

    fn as_node_ref(&self) -> NodeRef {
        match &self.kind {
            ArgumentKind::Positional { node_ref, .. }
            | ArgumentKind::Keyword { node_ref, .. }
            | ArgumentKind::ParamSpec { node_ref, .. }
            | ArgumentKind::Inferred { node_ref, .. } => *node_ref,
            ArgumentKind::Comprehension {
                file,
                comprehension,
                ..
            } => NodeRef::new(file, comprehension.index()),
            ArgumentKind::SlicesTuple { slices, .. } => todo!(),
            ArgumentKind::Overridden { original, .. } => original.as_node_ref(),
        }
    }

    pub(crate) fn add_issue(&self, i_s: &InferenceState, issue: IssueType) {
        self.as_node_ref().add_issue(i_s, issue)
    }

    pub fn maybe_star_type(&self, i_s: &InferenceState) -> Option<Type> {
        self.as_node_ref()
            .maybe_starred_expression()
            .map(|starred| {
                self.as_node_ref()
                    .file
                    .inference(i_s)
                    .infer_expression(starred.expression())
                    .as_type(i_s)
            })
    }

    pub fn maybe_star_star_type(&self, i_s: &InferenceState) -> Option<Type> {
        let node_ref = self.as_node_ref();
        node_ref
            .maybe_double_starred_expression()
            .and_then(|star_star| {
                // If we have a defined kwargs name, that's from a TypedDict and
                // shouldn't be formatted.
                if matches!(
                    &self.kind,
                    ArgumentKind::Inferred {
                        is_keyword: Some(Some(_)),
                        ..
                    }
                ) {
                    None
                } else {
                    Some(
                        node_ref
                            .file
                            .inference(i_s)
                            .infer_expression(star_star.expression())
                            .as_type(i_s),
                    )
                }
            })
    }

    pub fn is_from_star_star_args(&self) -> bool {
        let reference = self.as_node_ref();
        reference.maybe_double_starred_expression().is_some()
    }

    pub fn human_readable_index(&self, db: &Database) -> String {
        match &self.kind {
            ArgumentKind::Inferred {
                is_keyword: Some(Some(s)),
                ..
            } => format!("\"{}\"", s.as_str(db)),
            ArgumentKind::Positional { position, .. }
            | ArgumentKind::Inferred { position, .. }
            | ArgumentKind::ParamSpec { position, .. } => {
                format!("{position}")
            }
            ArgumentKind::Comprehension { .. } => "0".to_owned(),
            ArgumentKind::Keyword { key, .. } => format!("\"{key}\""),
            ArgumentKind::SlicesTuple { .. } => todo!(),
            ArgumentKind::Overridden { original, .. } => original.human_readable_index(db),
        }
    }

    pub fn is_keyword_argument(&self) -> bool {
        matches!(
            self.kind,
            ArgumentKind::Keyword { .. }
                | ArgumentKind::Inferred {
                    is_keyword: Some(_),
                    ..
                }
        )
    }

    pub fn keyword_name(&self, db: &'db Database) -> Option<&str> {
        match self.kind {
            ArgumentKind::Keyword { key, .. } => Some(key),
            ArgumentKind::Inferred {
                is_keyword: Some(Some(key)),
                ..
            } => Some(key.as_str(db)),
            _ => None,
        }
    }

    pub fn maybe_positional_arg(
        self,
        i_s: &InferenceState<'db, '_>,
        context: &mut ResultContext,
    ) -> Option<Inferred> {
        match self.kind {
            ArgumentKind::Positional { .. }
            | ArgumentKind::SlicesTuple { .. }
            | ArgumentKind::Comprehension { .. } => Some(self.infer(i_s, context)),
            ArgumentKind::Inferred {
                inferred,
                in_args_or_kwargs_and_arbitrary_len: false,
                is_keyword: None,
                ..
            } => Some(inferred),
            ArgumentKind::ParamSpec { .. } => todo!(),
            ArgumentKind::Overridden { original, inferred } => original
                .clone()
                .maybe_positional_arg(i_s, context)
                .map(|_| inferred),
            ArgumentKind::Keyword { .. } | ArgumentKind::Inferred { .. } => None,
        }
    }
}

#[derive(Debug, Clone)]
enum ArgumentIteratorBase<'db, 'a> {
    Iterator {
        i_s: InferenceState<'db, 'a>,
        file: &'a PythonFile,
        iterator: std::iter::Enumerate<ArgumentsIterator<'a>>,
        kwargs_before_star_args: Option<Vec<ASTArgument<'a>>>,
    },
    Comprehension(InferenceState<'db, 'a>, &'a PythonFile, Comprehension<'a>),
    Inferred {
        inferred: &'a Inferred,
        node_ref: NodeRef<'a>,
    },
    SliceType(InferenceState<'db, 'a>, SliceType<'a>),
    Finished,
}

enum BaseArgumentReturn<'db, 'a> {
    ArgsKwargs(ArgsKwargsIterator<'a>),
    Argument(ArgumentKind<'db, 'a>),
}

impl<'db, 'a> ArgumentIteratorBase<'db, 'a> {
    fn expect_i_s(&mut self) -> &InferenceState<'db, 'a> {
        if let Self::Iterator { i_s, .. } = self {
            i_s
        } else {
            unreachable!()
        }
    }
    fn into_argument_types(self, i_s: &InferenceState) -> Vec<Box<str>> {
        match self {
            Self::Inferred { inferred, .. } => vec![inferred.as_cow_type(i_s).format_short(i_s.db)],
            Self::Iterator {
                i_s,
                file,
                iterator,
                ..
            } => iterator
                .map(|(_, arg)| {
                    let mut prefix = "".to_owned();
                    let mut inference = file.inference(&i_s);
                    let inf = match arg {
                        ASTArgument::Positional(named_expr) => {
                            inference.infer_named_expression(named_expr)
                        }
                        ASTArgument::Keyword(kwarg) => {
                            let (name, expr) = kwarg.unpack();
                            prefix = format!("{}=", name.as_code());
                            inference.infer_expression(expr)
                        }
                        ASTArgument::Star(starred_expr) => {
                            prefix = "*".to_owned();
                            inference.infer_expression(starred_expr.expression())
                        }
                        ASTArgument::StarStar(double_starred_expr) => {
                            prefix = "*".to_owned();
                            inference.infer_expression(double_starred_expr.expression())
                        }
                    };
                    format!("{prefix}{}", inf.format_short(&i_s)).into()
                })
                .collect(),
            Self::Comprehension(_, file, comprehension) => {
                todo!()
            }
            Self::Finished => vec![],
            Self::SliceType(i_s, slice_type) => slice_type
                .iter()
                .map(|x| {
                    x.infer(&i_s, &mut ResultContext::Unknown)
                        .format_short(&i_s)
                })
                .collect(),
        }
    }
}

impl<'db, 'a> Iterator for ArgumentIteratorBase<'db, 'a> {
    type Item = BaseArgumentReturn<'db, 'a>;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::Inferred { .. } => {
                if let Self::Inferred { inferred, node_ref } = mem::replace(self, Self::Finished) {
                    Some(BaseArgumentReturn::Argument(ArgumentKind::Inferred {
                        inferred: inferred.clone(),
                        position: 1,
                        node_ref,
                        in_args_or_kwargs_and_arbitrary_len: false,
                        is_keyword: None,
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
                                *i_s,
                                i + 1,
                                file,
                                named_expr.index(),
                            ))
                        }
                        ASTArgument::Keyword(kwarg) => {
                            let (name, expression) = kwarg.unpack();
                            if let Some(kwargs_before_star_args) = kwargs_before_star_args {
                                kwargs_before_star_args.push(arg);
                            } else {
                                return Some(ArgumentKind::new_keyword_return(
                                    *i_s,
                                    file,
                                    name.as_code(),
                                    kwarg.index(),
                                    expression,
                                ));
                            }
                        }
                        ASTArgument::Star(starred_expr) => {
                            let inf = file
                                .inference(i_s)
                                .infer_expression(starred_expr.expression());
                            let node_ref = NodeRef::new(file, starred_expr.index());
                            return match inf.as_cow_type(i_s).as_ref() {
                                Type::ParamSpecArgs(usage) => {
                                    // TODO check for the next arg being **P.kwargs
                                    iterator.next();
                                    Some(BaseArgumentReturn::Argument(ArgumentKind::ParamSpec {
                                        usage: usage.clone(),
                                        node_ref: NodeRef::new(file, starred_expr.index()),
                                        position: i + 1,
                                    }))
                                }
                                _ => {
                                    Some(BaseArgumentReturn::ArgsKwargs(ArgsKwargsIterator::Args {
                                        iterator: inf.iter(i_s, node_ref),
                                        node_ref,
                                        position: i + 1,
                                    }))
                                }
                            };
                        }
                        ASTArgument::StarStar(double_starred_expr) => {
                            let inf = file
                                .inference(i_s)
                                .infer_expression(double_starred_expr.expression());
                            let type_ = inf.as_cow_type(i_s);
                            let node_ref = NodeRef::new(file, double_starred_expr.index());
                            if let Some(typed_dict) = type_.maybe_typed_dict(i_s.db) {
                                return Some(BaseArgumentReturn::ArgsKwargs(
                                    ArgsKwargsIterator::TypedDict {
                                        db: i_s.db,
                                        typed_dict,
                                        iterator_index: 0,
                                        node_ref,
                                        position: i + 1,
                                    },
                                ));
                            }
                            let unpacked = unpack_star_star(i_s, &type_);
                            let s = i_s.db.python_state.str_type();
                            let value = if let Some((key, value)) = unpacked {
                                if !key.is_simple_same_type(i_s, &s).bool() {
                                    debug!("Keyword is type {}", key.format_short(i_s.db));
                                    node_ref.add_issue(
                                        i_s,
                                        IssueType::ArgumentIssue(Box::from(
                                            "Keywords must be strings",
                                        )),
                                    );
                                }
                                value
                            } else {
                                node_ref.add_issue(
                                    i_s,
                                    IssueType::ArgumentTypeIssue(
                                        format!(
                                            "Argument after ** must be a mapping, not \"{}\"",
                                            type_.format_short(i_s.db),
                                        )
                                        .into(),
                                    ),
                                );
                                Type::Any(AnyCause::FromError)
                            };
                            return Some(BaseArgumentReturn::ArgsKwargs(
                                ArgsKwargsIterator::Kwargs {
                                    inferred_value: Inferred::from_type(value),
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
                            ASTArgument::Keyword(kwarg) => {
                                let (name, expression) = kwarg.unpack();
                                return Some(ArgumentKind::new_keyword_return(
                                    *i_s,
                                    file,
                                    name.as_code(),
                                    kwarg.index(),
                                    expression,
                                ));
                            }
                            _ => unreachable!(),
                        }
                    }
                }
                None
            }
            Self::Comprehension(..) => {
                if let Self::Comprehension(i_s, file, comprehension) =
                    mem::replace(self, Self::Finished)
                {
                    Some(BaseArgumentReturn::Argument(ArgumentKind::Comprehension {
                        i_s,
                        file,
                        comprehension,
                    }))
                } else {
                    unreachable!()
                }
            }
            Self::Finished => None,
            Self::SliceType(..) => {
                let Self::SliceType(i_s, slice_type) = mem::replace(self, Self::Finished) else {
                    unreachable!()
                };
                match slice_type.unpack() {
                    SliceTypeContent::Simple(s) => {
                        let file = s.file;
                        let named_expr = s.named_expr;
                        Some(ArgumentKind::new_positional_return(
                            i_s,
                            1,
                            file,
                            named_expr.index(),
                        ))
                    }
                    SliceTypeContent::Slices(slices) => {
                        Some(BaseArgumentReturn::Argument(ArgumentKind::SlicesTuple {
                            i_s,
                            slices,
                        }))
                    }
                    SliceTypeContent::Slice(slice) => {
                        Some(BaseArgumentReturn::Argument(ArgumentKind::Inferred {
                            inferred: slice.infer(&i_s),
                            position: 1,
                            node_ref: slice.as_node_ref(),
                            in_args_or_kwargs_and_arbitrary_len: false,
                            is_keyword: None,
                        }))
                    }
                }
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct ArgumentIterator<'db, 'a> {
    current: ArgumentIteratorBase<'db, 'a>,
    args_kwargs_iterator: ArgsKwargsIterator<'a>,
    next: Option<&'a dyn Arguments<'db>>,
    counter: usize,
}

impl<'db, 'a> ArgumentIterator<'db, 'a> {
    fn new(current: ArgumentIteratorBase<'db, 'a>) -> Self {
        Self {
            current,
            next: None,
            args_kwargs_iterator: ArgsKwargsIterator::None,
            counter: 0,
        }
    }

    pub fn new_slice(slice_type: SliceType<'a>, i_s: InferenceState<'db, 'a>) -> Self {
        Self {
            current: ArgumentIteratorBase::SliceType(i_s, slice_type),
            args_kwargs_iterator: ArgsKwargsIterator::None,
            next: None,
            counter: 0,
        }
    }

    pub fn into_argument_types(mut self, i_s: &InferenceState) -> Box<[Box<str>]> {
        let mut result = vec![];
        loop {
            result.extend(self.current.into_argument_types(i_s));
            if let Some(next) = self.next {
                self = next.iter();
            } else {
                break;
            }
        }
        result.into_boxed_slice()
    }

    pub fn calculate_diagnostics(self, i_s: &InferenceState<'db, '_>) {
        for arg in self {
            arg.infer(i_s, &mut ResultContext::Unknown);
        }
    }
}

impl<'db, 'a> Iterator for ArgumentIterator<'db, 'a> {
    type Item = Argument<'db, 'a>;

    fn next(&mut self) -> Option<Self::Item> {
        match std::mem::replace(&mut self.args_kwargs_iterator, ArgsKwargsIterator::None) {
            ArgsKwargsIterator::None => match self.current.next() {
                Some(BaseArgumentReturn::Argument(mut kind)) => {
                    let index = self.counter;
                    if let ArgumentKind::Inferred { position, .. } = &mut kind {
                        // This is a bit of a special case where 0 means that we're on a bound self
                        // argument. In that case we do not want to increase the counter, because
                        // the bound argument is not counted as an argument.
                        if *position != 0 {
                            self.counter += 1;
                        }
                        *position += index;
                    } else {
                        self.counter += 1;
                    }
                    Some(Argument {
                        kind,
                        index: self.counter,
                    })
                }
                Some(BaseArgumentReturn::ArgsKwargs(args_kwargs)) => {
                    self.args_kwargs_iterator = args_kwargs;
                    self.next()
                }
                None => {
                    if let Some(next) = self.next {
                        let old_counter = self.counter;
                        *self = next.iter();
                        self.counter += old_counter;
                        self.next()
                    } else {
                        None
                    }
                }
            },
            ArgsKwargsIterator::Args {
                mut iterator,
                node_ref,
                position,
            } => {
                if let Some(inferred) = iterator.next(self.current.expect_i_s()) {
                    let index = self.counter;
                    self.counter += 1;
                    let in_args_or_kwargs_and_arbitrary_len = iterator.len().is_none();
                    if !in_args_or_kwargs_and_arbitrary_len {
                        self.args_kwargs_iterator = ArgsKwargsIterator::Args {
                            iterator,
                            node_ref,
                            position,
                        };
                    }
                    Some(Argument {
                        kind: ArgumentKind::Inferred {
                            inferred,
                            position,
                            node_ref,
                            in_args_or_kwargs_and_arbitrary_len,
                            is_keyword: None,
                        },
                        index,
                    })
                } else {
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
                        inferred: inferred_value,
                        position,
                        node_ref,
                        in_args_or_kwargs_and_arbitrary_len: true,
                        is_keyword: Some(None),
                    },
                    index,
                })
            }
            ArgsKwargsIterator::TypedDict {
                db,
                node_ref,
                position,
                typed_dict,
                iterator_index,
            } => {
                let index = self.counter;
                self.counter += 1;
                let Some((name, t)) = typed_dict.members(db).get(iterator_index).map(|member| {
                    (
                        member.name,
                        member.type_.clone(),
                    )
                }) else {
                    return self.next()
                };
                self.args_kwargs_iterator = ArgsKwargsIterator::TypedDict {
                    db,
                    node_ref,
                    position,
                    typed_dict,
                    iterator_index: iterator_index + 1,
                };
                Some(Argument {
                    kind: ArgumentKind::Inferred {
                        inferred: Inferred::from_type(t),
                        position,
                        node_ref,
                        in_args_or_kwargs_and_arbitrary_len: false,
                        is_keyword: Some(Some(name)),
                    },
                    index,
                })
            }
        }
    }
}

#[derive(Debug, Clone)]
enum ArgsKwargsIterator<'a> {
    Args {
        iterator: IteratorContent,
        position: usize,
        node_ref: NodeRef<'a>,
    },
    Kwargs {
        inferred_value: Inferred,
        position: usize,
        node_ref: NodeRef<'a>,
    },
    TypedDict {
        db: &'a Database,
        typed_dict: Rc<TypedDict>,
        iterator_index: usize,
        position: usize,
        node_ref: NodeRef<'a>,
    },
    None,
}

pub fn unpack_star_star(i_s: &InferenceState, t: &Type) -> Option<(Type, Type)> {
    let wanted_cls = i_s.db.python_state.supports_keys_and_get_item_class(i_s.db);
    let mut matcher = Matcher::new_class_matcher(i_s, wanted_cls);
    let matches = wanted_cls
        .check_protocol_match(i_s, &mut matcher, &t, Variance::Covariant)
        .bool();
    matches.then(|| {
        let mut iter = matcher
            .unwrap_calculated_type_args()
            .into_iter()
            .zip(wanted_cls.type_vars(i_s).iter())
            .map(|(c, type_var_like)| {
                let GenericItem::TypeArgument(t) = c.into_generic_item(
                    i_s.db,
                    type_var_like
                ) else {
                    unreachable!();
                };
                t
            });
        (iter.next().unwrap(), iter.next().unwrap())
    })
}

#[derive(Debug)]
pub struct NoArguments<'a>(NodeRef<'a>);

impl<'a> NoArguments<'a> {
    pub fn new(node_ref: NodeRef<'a>) -> Self {
        Self(node_ref)
    }
}

impl<'db, 'a> Arguments<'db> for NoArguments<'a> {
    fn iter(&self) -> ArgumentIterator<'db, '_> {
        ArgumentIterator::new(ArgumentIteratorBase::Finished)
    }

    fn type_(&self) -> ArgumentsType {
        todo!()
    }

    fn as_node_ref(&self) -> NodeRef {
        self.0
    }
}
