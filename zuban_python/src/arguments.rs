use std::{mem, rc::Rc};

use parsa_python_ast::{
    ArgsIterator, Argument as ASTArgument, ArgumentsDetails, Comprehension, Expression, NodeIndex,
    Primary, PrimaryContent,
};

use crate::{
    database::{Database, PointsBackup},
    debug,
    diagnostics::IssueType,
    file::PythonFile,
    getitem::{SliceType, SliceTypeContent, Slices},
    inferred::Inferred,
    matching::{IteratorContent, Matcher, ResultContext, UnpackedArgument},
    node_ref::NodeRef,
    type_::{AnyCause, GenericItem, ParamSpecUsage, StringSlice, Type, TypedDict, WithUnpack},
    InferenceState,
};

pub(crate) trait Args<'db>: std::fmt::Debug {
    // Returns an iterator of arguments, where args are returned before kw args.
    // This is not the case in the grammar, but here we want that.
    fn iter(&self) -> ArgIterator<'db, '_>;
    fn as_node_ref(&self) -> Option<NodeRef>;
    fn add_issue(&self, i_s: &InferenceState, issue: IssueType) {
        self.as_node_ref()
            .expect("Otherwise add_issue should be implemented")
            .add_issue(i_s, issue)
    }
    fn starting_line(&self) -> String {
        let Some(node_ref) = self.as_node_ref() else {
            return "<unkown line>".into()
        };
        node_ref.line().to_string()
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
            if let InferredArg::Inferred(inf) = arg.infer(i_s, &mut ResultContext::Unknown) {
                if inf.is_union(i_s) {
                    return true;
                }
            }
        }
        false
    }

    fn maybe_two_positional_args(&self, db: &'db Database) -> Option<(NodeRef<'db>, NodeRef<'db>)> {
        let mut iterator = self.iter();
        let Some(first_arg) = iterator.next() else {
            return None
        };
        let ArgKind::Positional(PositionalArg { node_ref: node_ref1, .. }) = first_arg.kind else {
            return None
        };
        let Some(second_arg) = iterator.next() else {
            return None
        };
        let ArgKind::Positional(PositionalArg { node_ref: node_ref2, .. }) = second_arg.kind else {
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
pub struct SimpleArgs<'db, 'a> {
    // The node id of the grammar node called primary, which is defined like
    // primary "(" [arguments | comprehension] ")"
    file: &'a PythonFile,
    primary_node_index: NodeIndex,
    details: ArgumentsDetails<'a>,
    i_s: InferenceState<'db, 'a>,
}

impl<'db: 'a, 'a> Args<'db> for SimpleArgs<'db, 'a> {
    fn iter(&self) -> ArgIterator<'db, '_> {
        ArgIterator::new(match self.details {
            ArgumentsDetails::Node(arguments) => ArgIteratorBase::Iterator {
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
                ArgIteratorBase::Comprehension(self.i_s, self.file, comprehension)
            }
            ArgumentsDetails::None => ArgIteratorBase::Finished,
        })
    }

    fn as_node_ref(&self) -> Option<NodeRef> {
        Some(NodeRef::new(self.file, self.primary_node_index))
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

impl<'db: 'a, 'a> SimpleArgs<'db, 'a> {
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
pub struct KnownArgs<'a> {
    inferred: &'a Inferred,
    node_ref: NodeRef<'a>,
}

impl<'db, 'a> Args<'db> for KnownArgs<'a> {
    fn iter(&self) -> ArgIterator<'db, '_> {
        ArgIterator::new(ArgIteratorBase::Inferred {
            inferred: self.inferred,
            node_ref: self.node_ref,
        })
    }

    fn as_node_ref(&self) -> Option<NodeRef> {
        Some(self.node_ref)
    }
}

impl<'a> KnownArgs<'a> {
    pub fn new(inferred: &'a Inferred, node_ref: NodeRef<'a>) -> Self {
        Self { inferred, node_ref }
    }
}

impl<'a> KnownArgsWithCustomAddIssue<'a> {
    pub(crate) fn new(inferred: &'a Inferred, add_issue: &'a dyn Fn(IssueType)) -> Self {
        Self {
            inferred,
            add_issue: CustomAddIssue(add_issue),
        }
    }
}

#[derive(Debug)]
pub(crate) struct KnownArgsWithCustomAddIssue<'a> {
    inferred: &'a Inferred,
    add_issue: CustomAddIssue<'a>,
}

impl<'db, 'a> Args<'db> for KnownArgsWithCustomAddIssue<'a> {
    fn iter(&self) -> ArgIterator<'db, '_> {
        ArgIterator::new(ArgIteratorBase::InferredWithCustomAddIssue {
            inferred: self.inferred,
            add_issue: self.add_issue,
        })
    }

    fn add_issue(&self, i_s: &InferenceState, issue: IssueType) {
        self.add_issue.0(issue)
    }

    fn as_node_ref(&self) -> Option<NodeRef> {
        None
    }
}

#[derive(Debug)]
pub struct CombinedArgs<'db, 'a> {
    args1: &'a dyn Args<'db>,
    args2: &'a dyn Args<'db>,
}

impl<'db, 'a> Args<'db> for CombinedArgs<'db, 'a> {
    fn iter(&self) -> ArgIterator<'db, '_> {
        let mut iterator = self.args1.iter();
        debug_assert!(iterator.next.is_none()); // For now this is not supported
        iterator.next = Some(self.args2);
        iterator
    }

    fn as_node_ref(&self) -> Option<NodeRef> {
        self.args2.as_node_ref()
    }

    fn starting_line(&self) -> String {
        self.args2.starting_line()
    }

    fn add_issue(&self, i_s: &InferenceState, issue: IssueType) {
        self.args2.add_issue(i_s, issue)
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

impl<'db, 'a> CombinedArgs<'db, 'a> {
    pub(crate) fn new(args1: &'a dyn Args<'db>, args2: &'a dyn Args<'db>) -> Self {
        Self { args1, args2 }
    }
}

#[derive(Debug, Clone)]
pub struct PositionalArg<'db, 'a> {
    i_s: InferenceState<'db, 'a>,
    pub position: usize, // The position as a 1-based index
    pub node_ref: NodeRef<'a>,
}

impl<'db> PositionalArg<'db, '_> {
    pub fn infer(
        &self,
        func_i_s: &InferenceState<'db, '_>,
        result_context: &mut ResultContext,
    ) -> Inferred {
        self.node_ref
            .file
            // TODO this execution is wrong
            .inference(&self.i_s.use_mode_of(func_i_s))
            .infer_named_expression_with_context(
                self.node_ref.as_named_expression(),
                result_context,
            )
    }

    pub(crate) fn add_issue(&self, i_s: &InferenceState, issue: IssueType) {
        self.node_ref.add_issue(i_s, issue)
    }
}

#[derive(Debug, Clone)]
pub struct KeywordArg<'db, 'a> {
    i_s: InferenceState<'db, 'a>,
    pub key: &'a str,
    pub node_ref: NodeRef<'a>,
    pub expression: Expression<'a>,
}

impl<'db> KeywordArg<'db, '_> {
    pub fn infer(
        &self,
        func_i_s: &InferenceState<'db, '_>,
        result_context: &mut ResultContext,
    ) -> Inferred {
        self.node_ref
            .file
            .inference(&self.i_s.use_mode_of(func_i_s))
            .infer_expression_with_context(self.expression, result_context)
    }

    pub(crate) fn add_issue(&self, i_s: &InferenceState, issue: IssueType) {
        self.node_ref.add_issue(i_s, issue)
    }
}

#[derive(Debug, Clone)]
pub enum ArgKind<'db, 'a> {
    // Can be used for classmethod class or self in bound methods
    Keyword(KeywordArg<'db, 'a>),
    Inferred {
        inferred: Inferred,
        position: usize, // The position as a 1-based index
        node_ref: NodeRef<'a>,
        in_args_or_kwargs_and_arbitrary_len: bool,
        is_keyword: Option<Option<StringSlice>>,
    },
    InferredWithCustomAddIssue {
        inferred: Inferred,
        position: usize, // The position as a 1-based index
        add_issue: CustomAddIssue<'a>,
    },
    Positional(PositionalArg<'db, 'a>),
    SlicesTuple {
        i_s: InferenceState<'db, 'a>,
        slices: Slices<'a>,
    },
    StarredWithUnpack {
        with_unpack: WithUnpack,
        node_ref: NodeRef<'a>,
        position: usize, // The position as a 1-based index
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
        original: &'a Arg<'db, 'a>,
        inferred: Inferred,
    },
}

impl<'db, 'a> ArgKind<'db, 'a> {
    fn new_positional_return(
        i_s: InferenceState<'db, 'a>,
        position: usize,
        file: &'a PythonFile,
        node_index: NodeIndex,
    ) -> BaseArgReturn<'db, 'a> {
        BaseArgReturn::Arg(ArgKind::Positional(PositionalArg {
            i_s,
            position,
            node_ref: NodeRef { file, node_index },
        }))
    }

    fn new_keyword_return(
        i_s: InferenceState<'db, 'a>,
        file: &'a PythonFile,
        key: &'a str,
        node_index: NodeIndex,
        expression: Expression<'a>,
    ) -> BaseArgReturn<'db, 'a> {
        BaseArgReturn::Arg(ArgKind::Keyword(KeywordArg {
            i_s,
            key,
            node_ref: NodeRef { file, node_index },
            expression,
        }))
    }
}

pub enum InferredArg<'a> {
    Inferred(Inferred),
    StarredWithUnpack(WithUnpack),
    ParamSpec(&'a ParamSpecUsage),
}

#[derive(Debug, Clone)]
pub struct Arg<'db, 'a> {
    pub kind: ArgKind<'db, 'a>,
    pub index: usize,
}

impl<'db, 'a> Arg<'db, 'a> {
    pub fn in_args_or_kwargs_and_arbitrary_len(&self) -> bool {
        match &self.kind {
            ArgKind::Inferred {
                in_args_or_kwargs_and_arbitrary_len,
                ..
            } => *in_args_or_kwargs_and_arbitrary_len,
            _ => false,
        }
    }

    pub fn infer_inferrable(
        &self,
        func_i_s: &InferenceState<'db, '_>,
        result_context: &mut ResultContext,
    ) -> Inferred {
        match self.infer(func_i_s, result_context) {
            InferredArg::Inferred(inf) => inf,
            _ => unreachable!(),
        }
    }

    pub fn infer(
        &self,
        func_i_s: &InferenceState<'db, '_>,
        result_context: &mut ResultContext,
    ) -> InferredArg {
        InferredArg::Inferred(match &self.kind {
            ArgKind::Inferred { inferred, .. }
            | ArgKind::InferredWithCustomAddIssue { inferred, .. } => (*inferred).clone(),
            ArgKind::Positional(positional) => positional.infer(func_i_s, result_context),
            ArgKind::Keyword(kw) => kw.infer(func_i_s, result_context),
            ArgKind::SlicesTuple { i_s, slices } => slices.infer(&i_s.use_mode_of(func_i_s)),
            ArgKind::Comprehension {
                file,
                comprehension,
                i_s,
            } => file
                .inference(&i_s.use_mode_of(func_i_s))
                .infer_generator_comprehension(*comprehension, result_context),
            ArgKind::ParamSpec { usage, .. } => return InferredArg::ParamSpec(usage),
            ArgKind::StarredWithUnpack { with_unpack, .. } => {
                return InferredArg::StarredWithUnpack(with_unpack.clone())
            }
            ArgKind::Overridden { inferred, .. } => inferred.clone(),
        })
    }

    fn as_node_ref(&self) -> Result<NodeRef, CustomAddIssue> {
        match &self.kind {
            ArgKind::Positional(PositionalArg { node_ref, .. })
            | ArgKind::Keyword(KeywordArg { node_ref, .. })
            | ArgKind::ParamSpec { node_ref, .. }
            | ArgKind::StarredWithUnpack { node_ref, .. }
            | ArgKind::Inferred { node_ref, .. } => Ok(*node_ref),
            ArgKind::Comprehension {
                file,
                comprehension,
                ..
            } => Ok(NodeRef::new(file, comprehension.index())),
            ArgKind::SlicesTuple { slices, .. } => todo!(),
            ArgKind::Overridden { original, .. } => original.as_node_ref(),
            ArgKind::InferredWithCustomAddIssue { add_issue, .. } => Err(add_issue.clone()),
        }
    }

    pub(crate) fn add_issue(&self, i_s: &InferenceState, issue: IssueType) {
        match self.as_node_ref() {
            Ok(node_ref) => node_ref.add_issue(i_s, issue),
            Err(add_issue) => add_issue.0(issue),
        }
    }

    pub fn maybe_star_type(&self, i_s: &InferenceState) -> Option<Type> {
        let Ok(node_ref) = self.as_node_ref() else {
            return None
        };
        node_ref.maybe_starred_expression().map(|starred| {
            node_ref
                .file
                .inference(i_s)
                .infer_expression(starred.expression())
                .as_type(i_s)
        })
    }

    pub fn maybe_star_star_type(&self, i_s: &InferenceState) -> Option<Type> {
        let Ok(node_ref) = self.as_node_ref() else {
            return None
        };
        node_ref
            .maybe_double_starred_expression()
            .and_then(|star_star| {
                // If we have a defined kwargs name, that's from a TypedDict and
                // shouldn't be formatted.
                if matches!(
                    &self.kind,
                    ArgKind::Inferred {
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
        let Ok(node_ref) = self.as_node_ref() else {
            return false
        };
        node_ref.maybe_double_starred_expression().is_some()
    }

    pub fn human_readable_index(&self, db: &Database) -> String {
        match &self.kind {
            ArgKind::Inferred {
                is_keyword: Some(Some(s)),
                ..
            } => format!("\"{}\"", s.as_str(db)),
            ArgKind::Positional(PositionalArg { position, .. })
            | ArgKind::Inferred { position, .. }
            | ArgKind::InferredWithCustomAddIssue { position, .. }
            | ArgKind::StarredWithUnpack { position, .. }
            | ArgKind::ParamSpec { position, .. } => {
                format!("{position}")
            }
            ArgKind::Comprehension { .. } => "0".to_owned(),
            ArgKind::Keyword(KeywordArg { key, .. }) => format!("\"{key}\""),
            ArgKind::SlicesTuple { .. } => todo!(),
            ArgKind::Overridden { original, .. } => original.human_readable_index(db),
        }
    }

    pub fn is_keyword_argument(&self) -> bool {
        matches!(
            self.kind,
            ArgKind::Keyword { .. }
                | ArgKind::Inferred {
                    is_keyword: Some(_),
                    ..
                }
        )
    }

    pub fn keyword_name(&self, db: &'db Database) -> Option<&str> {
        match &self.kind {
            ArgKind::Keyword(kw) => Some(kw.key),
            ArgKind::Inferred {
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
            ArgKind::Positional { .. }
            | ArgKind::SlicesTuple { .. }
            | ArgKind::Comprehension { .. } => Some(self.infer_inferrable(i_s, context)),
            ArgKind::Inferred {
                inferred,
                in_args_or_kwargs_and_arbitrary_len: false,
                is_keyword: None,
                ..
            }
            | ArgKind::InferredWithCustomAddIssue { inferred, .. } => Some(inferred),
            ArgKind::Overridden { original, inferred } => original
                .clone()
                .maybe_positional_arg(i_s, context)
                .map(|_| inferred),
            ArgKind::ParamSpec { .. }
            | ArgKind::StarredWithUnpack { .. }
            | ArgKind::Keyword(KeywordArg { .. })
            | ArgKind::Inferred { .. } => None,
        }
    }
}

#[derive(Debug, Clone)]
enum ArgIteratorBase<'db, 'a> {
    Iterator {
        i_s: InferenceState<'db, 'a>,
        file: &'a PythonFile,
        iterator: std::iter::Enumerate<ArgsIterator<'a>>,
        kwargs_before_star_args: Option<Vec<ASTArgument<'a>>>,
    },
    Comprehension(InferenceState<'db, 'a>, &'a PythonFile, Comprehension<'a>),
    Inferred {
        inferred: &'a Inferred,
        node_ref: NodeRef<'a>,
    },
    InferredWithCustomAddIssue {
        inferred: &'a Inferred,
        add_issue: CustomAddIssue<'a>,
    },
    SliceType(InferenceState<'db, 'a>, SliceType<'a>),
    Finished,
}

enum BaseArgReturn<'db, 'a> {
    ArgsKwargs(ArgsKwargsIterator<'a>),
    Arg(ArgKind<'db, 'a>),
}

impl<'db, 'a> ArgIteratorBase<'db, 'a> {
    fn expect_i_s(&mut self) -> &InferenceState<'db, 'a> {
        if let Self::Iterator { i_s, .. } = self {
            i_s
        } else {
            unreachable!()
        }
    }
    fn into_argument_types(self, i_s: &InferenceState) -> Vec<Box<str>> {
        match self {
            Self::Inferred { inferred, .. } | Self::InferredWithCustomAddIssue { inferred, .. } => {
                vec![inferred.as_cow_type(i_s).format_short(i_s.db)]
            }
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

impl<'db, 'a> Iterator for ArgIteratorBase<'db, 'a> {
    type Item = BaseArgReturn<'db, 'a>;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::Inferred { .. } => {
                if let Self::Inferred { inferred, node_ref } = mem::replace(self, Self::Finished) {
                    Some(BaseArgReturn::Arg(ArgKind::Inferred {
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
                            return Some(ArgKind::new_positional_return(
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
                                return Some(ArgKind::new_keyword_return(
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
                                    Some(BaseArgReturn::Arg(ArgKind::ParamSpec {
                                        usage: usage.clone(),
                                        node_ref: NodeRef::new(file, starred_expr.index()),
                                        position: i + 1,
                                    }))
                                }
                                _ => Some(BaseArgReturn::ArgsKwargs(ArgsKwargsIterator::Args {
                                    iterator: inf.iter(i_s, node_ref),
                                    node_ref,
                                    position: i + 1,
                                })),
                            };
                        }
                        ASTArgument::StarStar(double_starred_expr) => {
                            let inf = file
                                .inference(i_s)
                                .infer_expression(double_starred_expr.expression());
                            let type_ = inf.as_cow_type(i_s);
                            let node_ref = NodeRef::new(file, double_starred_expr.index());
                            if let Some(typed_dict) = type_.maybe_typed_dict(i_s.db) {
                                return Some(BaseArgReturn::ArgsKwargs(
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
                            return Some(BaseArgReturn::ArgsKwargs(ArgsKwargsIterator::Kwargs {
                                inferred_value: Inferred::from_type(value),
                                node_ref,
                                position: i + 1,
                            }));
                        }
                    }
                }
                if let Some(kwargs_before_star_args) = kwargs_before_star_args {
                    if let Some(kwarg_before_star_args) = kwargs_before_star_args.pop() {
                        match kwarg_before_star_args {
                            ASTArgument::Keyword(kwarg) => {
                                let (name, expression) = kwarg.unpack();
                                return Some(ArgKind::new_keyword_return(
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
                    Some(BaseArgReturn::Arg(ArgKind::Comprehension {
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
                        Some(ArgKind::new_positional_return(
                            i_s,
                            1,
                            file,
                            named_expr.index(),
                        ))
                    }
                    SliceTypeContent::Slices(slices) => {
                        Some(BaseArgReturn::Arg(ArgKind::SlicesTuple { i_s, slices }))
                    }
                    SliceTypeContent::Slice(slice) => Some(BaseArgReturn::Arg(ArgKind::Inferred {
                        inferred: slice.infer(&i_s),
                        position: 1,
                        node_ref: slice.as_node_ref(),
                        in_args_or_kwargs_and_arbitrary_len: false,
                        is_keyword: None,
                    })),
                    SliceTypeContent::Starred(_) => todo!(),
                }
            }
            Self::InferredWithCustomAddIssue {
                inferred,
                add_issue,
            } => {
                if let Self::InferredWithCustomAddIssue {
                    inferred,
                    add_issue,
                } = mem::replace(self, Self::Finished)
                {
                    Some(BaseArgReturn::Arg(ArgKind::InferredWithCustomAddIssue {
                        inferred: inferred.clone(),
                        position: 1,
                        add_issue,
                    }))
                } else {
                    unreachable!()
                }
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct ArgIterator<'db, 'a> {
    current: ArgIteratorBase<'db, 'a>,
    args_kwargs_iterator: ArgsKwargsIterator<'a>,
    next: Option<&'a dyn Args<'db>>,
    counter: usize,
}

impl<'db, 'a> ArgIterator<'db, 'a> {
    fn new(current: ArgIteratorBase<'db, 'a>) -> Self {
        Self {
            current,
            next: None,
            args_kwargs_iterator: ArgsKwargsIterator::None,
            counter: 0,
        }
    }

    pub fn new_slice(slice_type: SliceType<'a>, i_s: InferenceState<'db, 'a>) -> Self {
        Self {
            current: ArgIteratorBase::SliceType(i_s, slice_type),
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

impl<'db, 'a> Iterator for ArgIterator<'db, 'a> {
    type Item = Arg<'db, 'a>;

    fn next(&mut self) -> Option<Self::Item> {
        match std::mem::replace(&mut self.args_kwargs_iterator, ArgsKwargsIterator::None) {
            ArgsKwargsIterator::None => match self.current.next() {
                Some(BaseArgReturn::Arg(mut kind)) => {
                    let index = self.counter;
                    if let ArgKind::Inferred { position, .. }
                    | ArgKind::InferredWithCustomAddIssue { position, .. } = &mut kind
                    {
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
                    Some(Arg {
                        kind,
                        index: self.counter,
                    })
                }
                Some(BaseArgReturn::ArgsKwargs(args_kwargs)) => {
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
            } => match iterator.next_as_argument(self.current.expect_i_s()) {
                Some(UnpackedArgument::Normal {
                    inferred,
                    arbitrary_len,
                }) => {
                    let index = self.counter;
                    self.counter += 1;
                    if !arbitrary_len {
                        self.args_kwargs_iterator = ArgsKwargsIterator::Args {
                            iterator,
                            node_ref,
                            position,
                        };
                    }
                    Some(Arg {
                        kind: ArgKind::Inferred {
                            inferred,
                            position,
                            node_ref,
                            in_args_or_kwargs_and_arbitrary_len: arbitrary_len,
                            is_keyword: None,
                        },
                        index,
                    })
                }
                Some(UnpackedArgument::WithUnpack(with_unpack)) => {
                    let index = self.counter;
                    self.counter += 1;
                    Some(Arg {
                        kind: ArgKind::StarredWithUnpack {
                            with_unpack,
                            position,
                            node_ref,
                        },
                        index,
                    })
                }
                None => self.next(),
            },
            ArgsKwargsIterator::Kwargs {
                inferred_value,
                node_ref,
                position,
            } => {
                let index = self.counter;
                self.counter += 1;
                Some(Arg {
                    kind: ArgKind::Inferred {
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
                Some(Arg {
                    kind: ArgKind::Inferred {
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
        .check_protocol_match(i_s, &mut matcher, &t)
        .bool();
    matches.then(|| {
        let mut iter = matcher
            .unwrap_calculated_type_args()
            .into_iter()
            .zip(wanted_cls.type_vars(i_s).iter())
            .map(|(c, type_var_like)| {
                let GenericItem::TypeArg(t) = c.into_generic_item(
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
pub struct NoArgs<'a>(NodeRef<'a>);

impl<'a> NoArgs<'a> {
    pub fn new(node_ref: NodeRef<'a>) -> Self {
        Self(node_ref)
    }
}

impl<'db, 'a> Args<'db> for NoArgs<'a> {
    fn iter(&self) -> ArgIterator<'db, '_> {
        ArgIterator::new(ArgIteratorBase::Finished)
    }

    fn as_node_ref(&self) -> Option<NodeRef> {
        Some(self.0)
    }
}

#[derive(Clone, Copy)]
pub struct CustomAddIssue<'a>(&'a dyn Fn(IssueType));

impl std::fmt::Debug for CustomAddIssue<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        f.debug_struct("ArgumentsWithCustomAddIssue").finish()
    }
}
