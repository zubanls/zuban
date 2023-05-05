use std::mem;
use std::rc::Rc;

use crate::database::{
    ComplexPoint, Database, DbType, MroIndex, ParamSpecUsage, TupleContent, TypeOrTypeVarTuple,
};
use crate::diagnostics::IssueType;
use crate::file::PythonFile;
use crate::getitem::{SliceType, SliceTypeContent, Slices};
use crate::inferred::Inferred;
use crate::matching::{ResultContext, Type};
use crate::node_ref::NodeRef;
use crate::value::IteratorContent;
use crate::InferenceState;
use parsa_python_ast::{
    Argument as ASTArgument, ArgumentsDetails, ArgumentsIterator, Comprehension, NodeIndex,
    Primary, PrimaryContent,
};

pub enum ArgumentsType<'a> {
    Normal(&'a PythonFile, NodeIndex),
}

pub trait Arguments<'db>: std::fmt::Debug {
    // Returns an iterator of arguments, where args are returned before kw args.
    // This is not the case in the grammar, but here we want that.
    fn iter(&self) -> ArgumentIterator<'db, '_>;
    fn type_(&self) -> ArgumentsType;
    fn as_node_ref(&self) -> NodeRef;
    fn reset_cache(&self) {
        // This is a bit special, but we use this to reset the type cache of the expressions to
        // avoid overload context inference issues.
    }

    fn has_a_union_argument(&self, i_s: &InferenceState<'db, '_>) -> bool {
        for arg in self.iter() {
            if arg.infer(i_s, &mut ResultContext::Unknown).is_union(i_s.db) {
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

    fn reset_cache(&self) {
        // Details is empty when no arguments are provided (e.g. `foo()`), which means we do not
        // have to reset the cache.
        let primary = self.as_node_ref().as_primary();
        let start = primary.index();
        let end = primary.expect_closing_bracket_index();
        self.file.reset_non_name_cache_between(start..end);
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
    mro_index: MroIndex,
    node_ref: NodeRef<'a>,
    is_bound_self: bool,
}

impl<'db, 'a> Arguments<'db> for KnownArguments<'a> {
    fn iter(&self) -> ArgumentIterator<'db, '_> {
        ArgumentIterator::new(ArgumentIteratorBase::Inferred {
            inferred: self.inferred,
            node_ref: self.node_ref,
            is_bound_self: self.is_bound_self,
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
        Self {
            inferred,
            node_ref,
            mro_index: MroIndex(0),
            is_bound_self: false,
        }
    }

    pub fn new_self(inferred: &'a Inferred, mro_index: MroIndex, node_ref: NodeRef<'a>) -> Self {
        Self {
            inferred,
            node_ref,
            mro_index,
            is_bound_self: true,
        }
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

    fn reset_cache(&self) {
        self.args1.reset_cache();
        self.args2.reset_cache();
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
        i_s: InferenceState<'db, 'a>,
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
    ) -> BaseArgumentReturn<'db, 'a> {
        BaseArgumentReturn::Argument(ArgumentKind::Keyword {
            i_s,
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
            ArgumentKind::Keyword { i_s, node_ref, .. } => node_ref
                .file
                .inference(&i_s.use_mode_of(func_i_s))
                .infer_expression_with_context(node_ref.as_expression(), result_context),
            ArgumentKind::SlicesTuple { i_s, slices } => {
                let parts = slices
                    .iter()
                    .map(|x| {
                        let i_s = &i_s.use_mode_of(func_i_s);
                        TypeOrTypeVarTuple::Type(
                            x.infer(i_s, &mut ResultContext::Unknown)
                                .class_as_db_type(i_s),
                        )
                    })
                    .collect();
                Inferred::new_unsaved_complex(ComplexPoint::TypeInstance(Box::new(DbType::Tuple(
                    Rc::new(TupleContent::new_fixed_length(parts)),
                ))))
            }
            ArgumentKind::Comprehension {
                file,
                comprehension,
                i_s,
            } => file
                .inference(&i_s.use_mode_of(func_i_s))
                .infer_comprehension(*comprehension),
            ArgumentKind::ParamSpec { usage, .. } => Inferred::new_unsaved_complex(
                ComplexPoint::TypeInstance(Box::new(DbType::ParamSpecArgs(usage.clone()))),
            ),
            ArgumentKind::Overridden { inferred, .. } => inferred.clone(),
        }
    }

    pub fn as_node_ref(&self) -> NodeRef {
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

    pub fn human_readable_index(&self) -> String {
        match &self.kind {
            ArgumentKind::Positional { position, .. }
            | ArgumentKind::Inferred { position, .. }
            | ArgumentKind::ParamSpec { position, .. } => {
                format!("{position}")
            }
            ArgumentKind::Comprehension { .. } => "0".to_owned(),
            ArgumentKind::Keyword { key, .. } => format!("{key:?}"),
            ArgumentKind::SlicesTuple { .. } => todo!(),
            ArgumentKind::Overridden { original, .. } => original.human_readable_index(),
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
        is_bound_self: bool,
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
            Self::Inferred {
                inferred,
                is_bound_self,
                ..
            } => match is_bound_self {
                false => vec![inferred.class_as_type(i_s).format_short(i_s.db)],
                true => vec![],
            },
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
                if let Self::Inferred {
                    inferred,
                    node_ref,
                    is_bound_self,
                } = mem::replace(self, Self::Finished)
                {
                    Some(BaseArgumentReturn::Argument(ArgumentKind::Inferred {
                        inferred: inferred.clone(),
                        position: (!is_bound_self).into(),
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
                                *i_s,
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
                                    *i_s,
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
                            if let Some(mro) = type_.mro(i_s.db) {
                                for (_, t) in mro {
                                    if let Some(class) = t.maybe_class(i_s.db) {
                                        if class.node_ref == i_s.db.python_state.mapping_node_ref()
                                        {
                                            let type_vars = class.type_vars(i_s).unwrap();
                                            let key = class
                                                .generics()
                                                .nth(i_s.db, &type_vars[0], 0)
                                                .expect_type_argument();
                                            let s = Type::Class(i_s.db.python_state.str());
                                            if !key.is_simple_same_type(i_s, &s).bool() {
                                                node_ref.add_typing_issue(
                                                    i_s,
                                                    IssueType::ArgumentIssue(Box::from(
                                                        "Keywords must be strings",
                                                    )),
                                                );
                                            }
                                            value_type = Some(
                                                class
                                                    .generics()
                                                    .nth(i_s.db, &type_vars[1], 1)
                                                    .expect_type_argument()
                                                    .into_db_type(i_s.db),
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
                                    i_s,
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
                                    *i_s,
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
            Self::Comprehension(i_s, file, comprehension) => {
                Some(BaseArgumentReturn::Argument(ArgumentKind::Comprehension {
                    i_s: *i_s,
                    file,
                    comprehension: *comprehension,
                }))
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
                    SliceTypeContent::Slice(slices) => {
                        let t = i_s.db.python_state.slice_db_type();
                        Some(BaseArgumentReturn::Argument(ArgumentKind::Inferred {
                            inferred: Inferred::execute_db_type(&i_s, t),
                            position: 1,
                            node_ref: slices.as_node_ref(),
                            in_args_or_kwargs_and_arbitrary_len: false,
                            is_keyword: false,
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
                            is_keyword: false,
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
                        is_keyword: true,
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
