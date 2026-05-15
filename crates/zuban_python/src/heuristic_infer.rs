use std::{cell::RefCell, iter::Peekable, rc::Rc};

use parsa_python_cst::{
    Argument, Arguments, ArgumentsDetails, AssignmentContent, AssignmentRightSide, Atom,
    AtomContent, Comprehension, Expression, ExpressionContent, ExpressionPart, FunctionDef,
    GotoNode, Name, NameParent, NodeIndex, ParamKind, Primary, PrimaryContent, PrimaryOrAtom,
    ReturnOrYield, Scope, StarExpressionContent, StarExpressions, StarLikeExpression, Target,
    TypeLike,
};
use regex::{Matches, Regex};
use utils::FastHashMap;

use crate::{
    arguments::{
        ArgIteratorBase, ArgKind, Args as _, ArgsKwargsIterator, SimpleArgs, unpack_star_star,
    },
    database::{Database, PointKind, PointLink},
    debug,
    file::{ClassNodeRef, FuncNodeRef, Inference, PythonFile},
    format_data::FormatData,
    getitem::SliceType,
    goto::{
        FollowImportResult, PositionalDocument, check_node_ref_and_maybe_follow_import,
        try_to_follow,
    },
    inference_state::{InferenceState, Mode},
    inferred::Inferred,
    matching::{Generics, IteratorContent, LookupKind},
    node_ref::NodeRef,
    params::{InferrableParam, InferrableParamIterator, Param as _, ParamArgument},
    result_context::ResultContext,
    type_::{
        ClassGenerics, DbString, ExtraItemsType, FunctionKind, GenericClass, GenericItem,
        GenericsList, IterCause, LookupResult, Tuple, Type, TypedDict, TypedDictGenerics,
        TypedDictMember, TypedDictMembers,
    },
    type_helpers::{Class, Function, FunctionParam},
    utils::{debug_indent, limit_length_for_debug},
};

// Stats from a 2016 Lenovo Notebook running Linux:
// With os.walk, it takes about 10s to scan 11'000 files (without filesystem
// caching). Once cached it only takes 5s.
// const OPENED_FILE_LIMIT: usize = 200;
// const PARSED_FILE_LIMIT: usize = 10;
// const MAX_PARAM_SEARCHES: usize = 20;
const PER_FILE_SEARCH_NAME_LIMIT: usize = 20;

#[derive(Debug, Copy, Clone)]
enum ArgumentsFrameKind {
    None,
    Arguments(NodeIndex),
    Comprehension(NodeIndex),
}

#[derive(Debug, Copy, Clone)]
struct ArgsFrame<'db> {
    file: &'db PythonFile,
    primary_node_index: NodeIndex,
    kind: ArgumentsFrameKind,
}

impl<'db> ArgsFrame<'db> {
    fn new(
        file: &'db PythonFile,
        primary_node_index: NodeIndex,
        details: ArgumentsDetails,
    ) -> Self {
        Self {
            file,
            primary_node_index,
            kind: match details {
                ArgumentsDetails::None => ArgumentsFrameKind::None,
                ArgumentsDetails::Node(arguments) => {
                    ArgumentsFrameKind::Arguments(arguments.index())
                }
                ArgumentsDetails::Comprehension(comprehension) => {
                    ArgumentsFrameKind::Comprehension(comprehension.index())
                }
            },
        }
    }

    fn as_details(&self) -> ArgumentsDetails<'db> {
        match self.kind {
            ArgumentsFrameKind::None => ArgumentsDetails::None,
            ArgumentsFrameKind::Arguments(args_index) => {
                ArgumentsDetails::Node(Arguments::by_index(&self.file.tree, args_index))
            }
            ArgumentsFrameKind::Comprehension(comp_index) => ArgumentsDetails::Comprehension(
                Comprehension::by_index(&self.file.tree, comp_index),
            ),
        }
    }
}

struct HeuristicState<'db> {
    callable_search_cache: FastHashMap<PointLink, Rc<[FoundExecution<'db>]>>,
    call_stack: Vec<(FuncNodeRef<'db>, ArgsFrame<'db>)>,
    self_stack: Vec<Type>,
}

impl<'db> HeuristicState<'db> {
    fn find_call_stack_frame(&self, func_node_ref: FuncNodeRef) -> Option<&ArgsFrame<'db>> {
        let (_, args_frame) = self
            .call_stack
            .iter()
            .find(|frame| frame.0 == func_node_ref)?;
        Some(args_frame)
    }
}

struct HeuristicInference<'db, 'state, 'i_s> {
    state: &'state mut HeuristicState<'db>,
    inference: Inference<'db, 'db, 'i_s>,
}

#[derive(Debug)]
enum Heuristic {
    WellKnown(Inferred),
    Guess(Inferred),
}

impl From<Heuristic> for Inferred {
    fn from(value: Heuristic) -> Self {
        match value {
            Heuristic::WellKnown(inf) | Heuristic::Guess(inf) => inf,
        }
    }
}

impl Heuristic {
    fn new_any_due_to_error() -> Self {
        Self::WellKnown(Inferred::new_any_from_error())
    }

    fn maybe_guessed(self) -> Option<Inferred> {
        match self {
            Self::WellKnown(_) => None,
            Self::Guess(inf) => Some(inf),
        }
    }
}

impl<'db, 'state> HeuristicInference<'db, 'state, '_> {
    fn with_different_i_s<T>(
        &mut self,
        i_s: InferenceState<'db, '_>,
        file: &'db PythonFile,
        callback: impl FnOnce(&mut HeuristicInference<'db, '_, '_>) -> T,
    ) -> T {
        i_s.avoid_errors_within(|i_s| {
            callback(&mut HeuristicInference {
                state: self.state,
                inference: file.inference(i_s),
            })
        })
        .0
    }

    fn with_different_file<T>(
        &mut self,
        file: &'db PythonFile,
        callback: impl FnOnce(&mut HeuristicInference<'db, '_, '_>) -> T,
    ) -> T {
        self.with_different_i_s(
            InferenceState::new(self.inference.i_s.db, file),
            file,
            callback,
        )
    }

    fn infer_name(&mut self, name: Name<'db>) -> Option<Heuristic> {
        debug!("Heuristics: Infer name: {}", name.as_code());
        match name.parent() {
            NameParent::Atom(_) | NameParent::Error => self.infer_name_reference(name),
            NameParent::NameDef(name_def) => match name_def.expect_type() {
                TypeLike::ParamName(_) => {
                    let func_node = name.expect_as_param_of_function();
                    let func_node_ref = FuncNodeRef::new(self.inference.file, func_node.index());
                    let func = Function::new_with_unknown_parent(
                        self.inference.i_s.db,
                        NodeRef::new(self.inference.file, func_node.index()),
                    );
                    let i_s = self.inference.i_s;
                    if let Some(self_) = self.state.self_stack.last()
                        && let Type::Class(c) = self_
                        && let class = c.class(i_s.db)
                        && func.class.is_some_and(|c| c.node_ref == class.node_ref)
                    {
                        if class.use_cached_type_vars(i_s.db).has_from_untyped_params()
                            && let Some((param_index, _)) = func_node
                                .params()
                                .iter()
                                .skip(1)
                                .enumerate()
                                .find(|(_, p)| p.name_def().index() == name_def.index())
                        {
                            return Some(Heuristic::Guess(Inferred::from_type(
                                class.nth_type_argument(i_s.db, param_index),
                            )));
                        }
                        return None;
                    }
                    if let Some(args_frame) = self.state.find_call_stack_frame(func_node_ref) {
                        let details = args_frame.as_details();
                        let args = SimpleArgs::new(
                            InferenceState::new(self.inference.i_s.db, args_frame.file),
                            args_frame.file,
                            args_frame.primary_node_index,
                            details,
                        );
                        let mut skip_first_param = false;
                        if func.class.is_some() {
                            match func.kind(self.inference.i_s) {
                                FunctionKind::Staticmethod => (),
                                _ => skip_first_param = true,
                            }
                        }
                        return Some(Heuristic::Guess(self.infer_param_with_args(
                            &func,
                            args,
                            skip_first_param,
                            name,
                            false,
                        )?));
                    }
                    Some(Heuristic::Guess(
                        self.search_callable_arguments(func_node, name)?,
                    ))
                }
                TypeLike::Assignment(assignment) => {
                    if let AssignmentContent::Normal(targets, right_side) = assignment.unpack() {
                        for target in targets {
                            match target {
                                Target::Name(name_def) | Target::NameExpression(_, name_def) => {
                                    if name_def.name_index() == name.index() {
                                        return match right_side {
                                            AssignmentRightSide::YieldExpr(_) => None,
                                            AssignmentRightSide::StarExpressions(star_exprs) => {
                                                Some(self.infer_star_exprs(star_exprs)?.into())
                                            }
                                        };
                                    }
                                }
                                Target::Tuple(_) => (), // TODO
                                _ => (),
                            }
                        }
                    }
                    None
                }
                _ => None,
            },
            NameParent::Primary(primary) => Some(self.infer_primary(primary)),
            /*
            NameParent::PrimaryTarget(primary_target) => (),
            NameParent::KeywordPattern(keyword_pattern) => (),
            NameParent::DottedPatternName(dotted_pattern_name) => (),
            NameParent::FStringConversion(fstring_conversion) => (),
            */
            _ => None,
        }
    }

    fn infer_name_reference(&mut self, name: Name) -> Option<Heuristic> {
        debug!("Heuristic follow name: {}", name.as_code());
        match try_to_follow(
            self.inference.i_s.db,
            NodeRef::new(self.inference.file, name.index()),
            true,
        )?? {
            FollowImportResult::File(file_index) => Some(Heuristic::WellKnown(
                Inferred::new_file_reference(file_index),
            )),
            FollowImportResult::TreeName(tree_name) => {
                self.with_different_file(tree_name.file, |h| h.infer_name(tree_name.cst_name))
            }
        }
    }

    fn search_callable_arguments(
        &mut self,
        func: FunctionDef,
        param_name: Name,
    ) -> Option<Inferred> {
        let func_name = func.name();
        let mut search_name = func_name.as_code();
        let mut skip_first_param = false;
        let db = self.inference.i_s.db;
        let func =
            Function::new_with_unknown_parent(db, NodeRef::new(self.inference.file, func.index()));
        let wanted_link = if search_name == "__init__"
            && let Some(class) = func.class
        {
            let cls_name = class.node().name();
            search_name = cls_name.as_code();
            skip_first_param = true;
            PointLink::new(self.inference.file.file_index, cls_name.index())
        } else if search_name.starts_with("__") && search_name.ends_with("__") {
            // These are magic methods and should probably not be searched.
            return None;
        } else {
            if func.class.is_some() {
                match func.kind(self.inference.i_s) {
                    FunctionKind::Function { .. } | FunctionKind::Classmethod { .. } => {
                        skip_first_param = true
                    }
                    FunctionKind::Staticmethod => (),
                    FunctionKind::Property { .. } => return None, // Properties are never called
                }
            }
            PointLink::new(self.inference.file.file_index, func_name.index())
        };

        let entry = self.state.callable_search_cache.entry(wanted_link);
        // Cache the executions
        debug!(
            "Try to find callable execution for {search_name}, skip_first_param={skip_first_param}"
        );
        let _indent = debug_indent();
        let executions = entry
            .or_insert_with(|| {
                let regex = Regex::new(&format!(r"\b{}\b\s*\(", search_name)).unwrap();
                FileNameSearcher::new(db, self.inference.file, &regex, wanted_link).collect()
            })
            .clone();
        debug!("Found executions: {executions:?}");

        if executions.is_empty() {
            let param = func
                .iter_params()
                .find(|p| p.name_def().name_index() == param_name.index())?;
            return Some(self.infer_expression(param.default()?).into());
        }

        executions
            .iter()
            .filter_map(|execution| {
                let args = SimpleArgs::new(
                    InferenceState::new(db, execution.file),
                    execution.file,
                    execution.primary.index(),
                    execution.details,
                );
                self.infer_param_with_args(&func, args, skip_first_param, param_name, true)
                /*
                // The deeper we're in the recursion, the less code should be inferred.
                if i * inference_state.dynamic_params_depth > MAX_PARAM_SEARCHES {
                    found_arguments = True;
                    yield arguments
                }
                */
            })
            .reduce(|inf1, inf2| {
                let i_s = &InferenceState::new_in_unknown_file(db);
                Inferred::from_type(inf1.as_type(i_s).union(inf2.as_type(i_s)))
            })
    }

    fn arg_param_iterator<'a>(
        db: &'db Database,
        slf: &'a RefCell<&mut Self>,
        func: &Function<'a, 'a>,
        args: &'a SimpleArgs<'db, 'db, 'a>,
        skip_first_param: bool,
    ) -> impl Iterator<Item = InferrableParam<'db, 'a, FunctionParam<'a>>>
    where
        'db: 'a,
    {
        let mut params = func.iter_params();
        if skip_first_param {
            params.next();
        }
        let mut arg_iterator = args.iter(Mode::Normal);
        InferrableParamIterator::new(
            db,
            params,
            std::iter::from_fn(move || {
                if let next @ Some(_) = arg_iterator.next_from_args_kwargs_iterator() {
                    return next;
                }
                // Override the args/kwargs inference
                if let ArgIteratorBase::Iterator { iterator, .. } = &mut arg_iterator.current {
                    for (i, argument) in iterator.clone() {
                        match argument {
                            Argument::Star(starred_expr) => {
                                iterator.next(); // Skip this and replace it
                                let ret = slf.borrow_mut().with_different_file(args.file, |h| {
                                    let inf: Inferred =
                                        h.infer_expression(starred_expr.expression()).into();
                                    debug!(
                                        "Inferred {} as: {}",
                                        starred_expr.as_code(),
                                        inf.format_short(h.inference.i_s)
                                    );
                                    let node_ref =
                                        NodeRef::new(h.inference.file, starred_expr.index());
                                    ArgsKwargsIterator::Args {
                                        iterator: inf.iter(
                                            h.inference.i_s,
                                            node_ref,
                                            IterCause::VariadicUnpack,
                                        ),
                                        node_ref,
                                        position: i + 1,
                                    }
                                });
                                if let ArgsKwargsIterator::Args {
                                    iterator: IteratorContent::FixedLenTupleGenerics { entries, .. },
                                    ..
                                } = &ret
                                    && entries.is_empty()
                                {
                                    debug!("Avoid star args, because it's an empty tuple");
                                    continue;
                                }
                                arg_iterator.args_kwargs_iterator = ret;
                            }
                            Argument::StarStar(star_star_expr) => {
                                iterator.next(); // Skip this and replace it
                                let ret = slf.borrow_mut().with_different_file(args.file, |h| {
                                    let inf: Inferred =
                                        h.infer_expression(star_star_expr.expression()).into();
                                    debug!(
                                        "Inferred {} as: {}",
                                        star_star_expr.as_code(),
                                        inf.format_short(h.inference.i_s)
                                    );
                                    let i_s = h.inference.i_s;
                                    let type_ = inf.as_cow_type(i_s);
                                    let node_ref =
                                        NodeRef::new(h.inference.file, star_star_expr.index());
                                    if let Some(typed_dict) = type_.maybe_typed_dict(i_s.db) {
                                        return ArgsKwargsIterator::TypedDict {
                                            db: i_s.db,
                                            typed_dict,
                                            iterator_index: 0,
                                            node_ref,
                                            position: i + 1,
                                        };
                                    }
                                    let unpacked = unpack_star_star(i_s, &type_);
                                    let value = if let Some((_, value)) = unpacked {
                                        value
                                    } else {
                                        Type::ERROR
                                    };
                                    return ArgsKwargsIterator::Kwargs {
                                        inferred_value: Inferred::from_type(value),
                                        node_ref,
                                        position: i + 1,
                                    };
                                });
                                arg_iterator.args_kwargs_iterator = ret;
                            }
                            _ => (),
                        }
                        break;
                    }
                }
                arg_iterator.next()
            }),
        )
    }

    fn infer_param_with_args(
        &mut self,
        func: &Function,
        args: SimpleArgs<'db, 'db, 'db>,
        skip_first_param: bool,
        search_param_name: Name,
        from_callable_search: bool,
    ) -> Option<Inferred> {
        let db = self.inference.i_s.db;
        let slf = &RefCell::new(self);
        let mut matched_arg_iterator =
            Self::arg_param_iterator(db, slf, func, &args, skip_first_param);
        for param in matched_arg_iterator.by_ref() {
            if param.param.name_def().name_index() == search_param_name.index() {
                return Self::infer_param(
                    db,
                    slf,
                    &args,
                    param,
                    &mut matched_arg_iterator.peekable(),
                    from_callable_search,
                );
            }
        }
        for param in func.iter_params() {
            if param.name_def().name_index() == search_param_name.index()
                && param.kind(db) == ParamKind::Star
            {
                // *args might be inferred as tuple[Any, ...] instead of an empty tuple, because it
                // when no argument matches it. This is because it is simply omitted in that case,
                // but here in heuristics we want to make sure that it's clear that it's empty,
                // otherwise params might be assigned wrong.
                return Some(Inferred::from_type(Type::Tuple(Tuple::new_fixed_length(
                    [].into(),
                ))));
            }
        }
        None
    }

    fn infer_param<'x>(
        db: &'db Database,
        slf: &RefCell<&mut Self>,
        args: &SimpleArgs<'db, 'db, '_>,
        param: InferrableParam<FunctionParam>,
        rest_args: &mut Peekable<impl Iterator<Item = InferrableParam<'db, 'x, FunctionParam<'x>>>>,
        from_callable_search: bool,
    ) -> Option<Inferred>
    where
        'db: 'x,
    {
        let result = Self::infer_argument(db, slf, args, param.param, param.argument, rest_args);
        if !from_callable_search && result.is_some() {
            // If there is a result in a normal execution heuristic, we can simply continue,
            // because the actual type has been found from the execution.
            return result;
        }
        if let Some(default) = param.param.default() {
            let mut slf = slf.borrow_mut();

            let inferred_default: Inferred = slf.infer_expression(default).into();
            /*
             * TODO use this
            let inferred_default: Inferred = slf
                .with_different_file(param.param.file, |h| h.infer_expression(default))
                .into();
            */
            if let Some(result) = result {
                return Some(Inferred::from_type(
                    result
                        .as_type(&InferenceState::new(db, args.file))
                        .union(inferred_default.as_type(slf.inference.i_s)),
                ));
            }
            return Some(inferred_default);
        }
        result
    }

    fn infer_argument<'x>(
        db: &'db Database,
        slf: &RefCell<&mut Self>,
        args: &SimpleArgs<'db, 'db, '_>,
        param: FunctionParam,
        argument: ParamArgument,
        rest_args: &mut Peekable<impl Iterator<Item = InferrableParam<'db, 'x, FunctionParam<'x>>>>,
    ) -> Option<Inferred>
    where
        'db: 'x,
    {
        let i_s = &InferenceState::new(db, args.file);
        let inf_expr = |expr| {
            slf.borrow_mut()
                .with_different_file(args.file, |h| h.infer_expression(expr).into())
        };
        let infer = |argument| match argument {
            ParamArgument::None => None,
            ParamArgument::Argument(arg) => match arg.kind {
                ArgKind::Positional(arg) => Some(inf_expr(arg.named_expr.expression())),
                ArgKind::Keyword(kw) => Some(inf_expr(kw.expression)),
                ArgKind::Inferred { inferred, .. }
                | ArgKind::InferredWithCustomAddIssue { inferred, .. }
                | ArgKind::Overridden { inferred, .. } => Some(inferred),
                ArgKind::Comprehension { .. } => todo!(),
                ArgKind::StarredWithUnpack { .. } | ArgKind::ParamSpec { .. } => None,
            },
            ParamArgument::TupleUnpack(_args) => todo!(),
            ParamArgument::MatchedUnpackedTypedDictMember { .. } => todo!(),
            ParamArgument::ParamSpecArgs(..) => todo!(),
        };
        match param.kind(i_s.db) {
            ParamKind::Star => {
                let tuple = Tuple::new_fixed_length(
                    std::iter::once(argument)
                        .chain(
                            std::iter::from_fn(|| {
                                rest_args.next_if(|p| p.param.kind(i_s.db) == ParamKind::Star)
                            })
                            .map(|p| p.argument),
                        )
                        .map(|arg| Some(infer(arg)?.into_type(&i_s)))
                        .collect::<Option<_>>()?,
                );
                debug!(
                    "Heuristics: Inferred param *{} as: {}",
                    param.name_def().as_code(),
                    tuple.format(&FormatData::new_short(i_s.db)),
                );
                Some(Inferred::from_type(Type::Tuple(tuple)))
            }
            ParamKind::StarStar => {
                let mut extra_items = Type::NEVER;
                let named = std::iter::once(argument)
                    .chain(rest_args.map(|p| p.argument))
                    .filter_map(|arg| {
                        let inner = match &arg {
                            ParamArgument::Argument(arg) => arg,
                            ParamArgument::MatchedUnpackedTypedDictMember { .. } => {
                                return None; // TODO?
                            }
                            // Not sure if this even happens
                            _ => return None,
                        };
                        if let Some(name) = inner.keyword_name(i_s.db) {
                            let name = DbString::ArcStr(name.into());
                            let type_ = infer(arg)?.into_type(&i_s);
                            Some(TypedDictMember {
                                name,
                                type_,
                                required: false,
                                read_only: false,
                            })
                        } else {
                            let arbitrary = inner.in_args_or_kwargs_and_arbitrary_len();
                            let type_ = infer(arg)?.into_type(&i_s);
                            if arbitrary {
                                extra_items.union_in_place(type_);
                            }
                            None
                        }
                    })
                    .collect();
                let members = TypedDictMembers {
                    named,
                    extra_items: (!extra_items.is_never()).then(|| ExtraItemsType {
                        t: extra_items,
                        read_only: false,
                    }),
                };
                let td =
                    TypedDict::new(None, members, args.primary_link(), TypedDictGenerics::None);
                debug!(
                    "Heuristics: Inferred param **{} as: {}",
                    param.name_def().as_code(),
                    td.format(&FormatData::new_short(i_s.db)),
                );
                Some(Inferred::from_type(Type::TypedDict(td)))
            }
            _ => {
                let result = infer(argument);
                if let Some(result) = &result {
                    debug!(
                        "Heuristics: Inferred param {} as: {}",
                        param.name_def().as_code(),
                        result.format_short(&i_s),
                    );
                } else {
                    debug!(
                        "Heuristics: Could not infer param {}",
                        param.name_def().as_code(),
                    );
                }
                result
            }
        }
    }

    pub fn infer_atom(&mut self, atom: Atom) -> Heuristic {
        let inf = self.inference.infer_atom(atom, &mut ResultContext::Unknown);
        debug!(
            "Heuristics for atom: {}",
            limit_length_for_debug(atom.as_code())
        );
        self.create_heuristic_if_necessary(inf, |slf| {
            Some(match atom.unpack() {
                AtomContent::Name(name) => slf.infer_name_reference(name)?,
                AtomContent::NamedExpression(named_expr) => {
                    slf.infer_expression(named_expr.expression())
                }
                /*
                AtomContent::List(list) => todo!(),
                AtomContent::ListComprehension(comprehension) => todo!(),
                AtomContent::Dict(dict) => todo!(),
                AtomContent::DictComprehension(dict_comprehension) => todo!(),
                AtomContent::Set(set) => todo!(),
                AtomContent::SetComprehension(comprehension) => todo!(),
                AtomContent::Tuple(tuple) => todo!(),
                AtomContent::GeneratorComprehension(comprehension) => todo!(),
                */
                _ => return None,
            })
        })
    }

    fn infer_primary(&mut self, primary: Primary) -> Heuristic {
        let inf = self
            .inference
            .infer_primary(primary, &mut ResultContext::Unknown);
        debug!(
            "Heuristics for primary: {}",
            limit_length_for_debug(primary.as_code()),
        );
        self.create_heuristic_if_necessary(inf, |slf| {
            let first = slf.infer_primary_or_atom(primary.first());
            slf.infer_primary_or_primary_t_content(first, primary.index(), primary.second())
        })
    }

    fn create_heuristic_if_necessary(
        &mut self,
        inf: Inferred,
        infer_heuristic: impl FnOnce(&mut Self) -> Option<Heuristic>,
    ) -> Heuristic {
        let _indent = debug_indent();
        let i_s = self.inference.i_s;
        let t = inf.as_cow_type(i_s);
        if t.has_any(i_s)
            || t.maybe_class(i_s.db)
                .is_some_and(|c| !c.file.is_stub() && !matches!(c.generics, Generics::List(..)))
        {
            if let Some(new) = infer_heuristic(self) {
                if let Heuristic::Guess(bound) = &new
                    && bound.maybe_bound_method().is_some()
                {
                    return new;
                }
                let new: Inferred = new.into();
                let new_t = new.into_type(i_s);
                if new_t
                    .iter_with_unpacked_unions(i_s.db)
                    .all(|t| matches!(t, Type::Any(_) | Type::None))
                {
                    debug!(
                        "Did find heuristics, but it's a useless: {}",
                        t.format_short(i_s.db)
                    );
                } else {
                    debug!("Found heuristics: {}", new_t.format_short(i_s.db));
                    let inf = Inferred::from_type(new_t);
                    return Heuristic::Guess(inf);
                }
            } else {
                debug!(
                    "Did not find heuristics, after searching, inferred {} instead",
                    t.format_short(i_s.db)
                );
            }
        } else {
            debug!(
                "Did not need heuristics, because the type {} has no Any",
                t.format_short(i_s.db)
            );
        }
        Heuristic::WellKnown(inf)
    }

    fn infer_primary_or_primary_t_content(
        &mut self,
        base: Heuristic,
        primary_node_index: NodeIndex,
        content: PrimaryContent,
    ) -> Option<Heuristic> {
        match content {
            PrimaryContent::Attribute(attr_name) => {
                let base_is_heuristic = !matches!(base, Heuristic::WellKnown(_));
                let base: Inferred = base.into();
                let base_t = base.as_cow_type(self.inference.i_s);
                let mut added_to_stack = false;
                if let t @ Type::Class(_) = base_t.as_ref() {
                    self.state.self_stack.push(t.clone());
                    added_to_stack = true;
                }
                let result = base_t.lookup(
                    self.inference.i_s,
                    self.inference.file,
                    attr_name.as_code(),
                    LookupKind::Normal,
                    &mut ResultContext::Unknown,
                    &|_| false,
                    &|_| (),
                );
                let mut out = None;
                if let LookupResult::GotoName { name, .. } = result {
                    let directed_to = NodeRef::from_link(self.inference.i_s.db, name);
                    let new_name = directed_to.expect_name();
                    // Should always be a NameDef
                    out = if let Type::Class(c) = base_t.as_ref() {
                        self.with_different_i_s(
                            InferenceState::from_class(
                                self.inference.i_s.db,
                                &c.class(self.inference.i_s.db),
                            ),
                            directed_to.file,
                            |h| h.infer_name(new_name),
                        )
                    } else {
                        self.with_different_file(directed_to.file, |h| h.infer_name(new_name))
                    };
                }
                if added_to_stack {
                    self.state.self_stack.pop();
                }
                if base_is_heuristic && out.is_none() {
                    out = result.into_maybe_inferred().map(Heuristic::Guess);
                }
                out
            }
            PrimaryContent::Execution(details) => self.execute(base, primary_node_index, details),
            PrimaryContent::GetItem(slice) => {
                if let Heuristic::Guess(base) = base {
                    let inf = base.get_item(
                        self.inference.i_s,
                        &SliceType::new(self.inference.file, primary_node_index, slice),
                        &mut ResultContext::Unknown,
                    );
                    debug!(
                        "Heuristics: Getitem on {}, result: {}",
                        base.format_short(self.inference.i_s),
                        inf.format_short(self.inference.i_s),
                    );
                    Some(Heuristic::Guess(inf))
                } else {
                    None
                }
            }
        }
    }

    fn execute(
        &mut self,
        base: Heuristic,
        primary_node_index: NodeIndex,
        details: ArgumentsDetails,
    ) -> Option<Heuristic> {
        let base: Inferred = base.into();
        let db = self.inference.i_s.db;
        let mut bound_to = None;
        let Some(node_ref) = base.maybe_saved_node_ref(db).or_else(|| {
            base.maybe_bound_method().map(|bound| {
                bound_to = Some(&bound.instance);
                // Bound methods are also "saved"
                NodeRef::from_link(db, bound.func_link)
            })
        }) else {
            debug!(
                "Heuristics: Did not execute, because the base is not a saved NodeRef, but {}",
                base.debug_info(db)
            );
            return None;
        };
        if node_ref.maybe_class().is_some() {
            let cls_node_ref = ClassNodeRef::from_node_ref(node_ref);
            debug!(
                "Heuristics: Found instance call for class \"{}\"",
                Class::with_undefined_generics(cls_node_ref).qualified_name(db)
            );
            let type_vars = cls_node_ref.use_cached_type_vars(db);

            if type_vars.has_from_untyped_params()
                && let Some(func) = cls_node_ref.maybe_init_func()
            {
                let i_s = *self.inference.i_s;
                let args = SimpleArgs::new(i_s, self.inference.file, primary_node_index, details);
                let func = Function::new_with_unknown_parent(
                    db,
                    NodeRef::new(node_ref.file, func.index()),
                );

                let slf = &RefCell::new(self);
                let mut matched_arg_iterator =
                    Self::arg_param_iterator(db, slf, &func, &args, true).peekable();
                let mut generics = vec![];
                while let Some(param) = matched_arg_iterator.next() {
                    let found = Self::infer_param(
                        db,
                        slf,
                        &args,
                        param,
                        matched_arg_iterator.by_ref(),
                        false,
                    )
                    .unwrap_or_else(Inferred::new_any_from_error);
                    generics.push(GenericItem::TypeArg(found.into_type(&i_s)));
                }
                debug!(
                    "Heuristics: Inferred param generics as {:?}",
                    generics
                        .iter()
                        .map(|g| match g {
                            GenericItem::TypeArg(t) => t.format_short(i_s.db),
                            _ => unreachable!(),
                        })
                        .collect::<Vec<_>>()
                );
                if generics.is_empty() {
                    return Some(Heuristic::Guess(Inferred::from_type(Type::Class(
                        GenericClass {
                            link: cls_node_ref.as_link(),
                            generics: ClassGenerics::new_none(),
                        },
                    ))));
                }
                debug_assert_eq!(type_vars.len(), generics.len());
                let inf = Inferred::from_type(Type::Class(GenericClass {
                    link: cls_node_ref.as_link(),
                    generics: ClassGenerics::List(GenericsList::generics_from_vec(generics)),
                }));
                return Some(Heuristic::Guess(inf));
            }
            debug!("Heuristics: class has no untyped params, TODO is this ok?");
            return None;
        }
        if node_ref.maybe_function().is_none() {
            debug!(
                "Heuristics: Did not execute, because the base is not a function, but {}",
                base.debug_info(db)
            );
            return None;
        }
        let func_node_ref = FuncNodeRef::from_node_ref(node_ref);
        if func_node_ref.return_annotation().is_some() {
            let ret = func_node_ref.return_annotation_type(self.inference.i_s);
            if !ret.is_any_or_any_in_union(db) {
                debug!(
                    "Heuristics: Did not execute, because the function has \
                                an annotation without an explicit Any"
                );
                return None;
            }
            if ret.has_type_vars() {
                debug!(
                    "Heuristics: Did not execute, because the function has \
                                an annotation with type vars"
                );
                return None;
            }
        }
        if func_node_ref.is_generator() {
            debug!("Heuristics: TODO Did not execute, because the function is a generator");
            return None; // TODO make generators possible
        }
        if self.state.find_call_stack_frame(func_node_ref).is_some() {
            debug!(
                "Heuristics: Had a recursion with func '{}', stopping inference",
                func_node_ref.qualified_name(db)
            );
            return None;
        }

        let func = Function::new_with_unknown_parent(db, *func_node_ref);

        let args_frame = ArgsFrame::new(self.inference.file, primary_node_index, details);
        self.state.call_stack.push((func_node_ref, args_frame));
        if let Some(bound) = bound_to {
            self.state.self_stack.push(bound.clone());
        }
        let result_t = self.with_different_i_s(
            self.inference.i_s.with_func_context(&func),
            func_node_ref.file,
            |h| h.heuristic_return_type(func_node_ref),
        );
        if bound_to.is_some() {
            self.state.self_stack.pop();
        }
        self.state.call_stack.pop();

        let result_t = result_t?;
        if result_t.is_never() {
            debug!(
                "Heuristics: Execution of {} with Never result, aborting",
                func_node_ref.qualified_name(db)
            );
            return None;
        }
        debug!(
            "Heuristics: Executed {} with result: {}",
            func_node_ref.qualified_name(db),
            result_t.format_short(db),
        );
        Some(Heuristic::Guess(Inferred::from_type(result_t)))
    }

    fn heuristic_return_type(&mut self, func_node_ref: FuncNodeRef) -> Option<Type> {
        let mut result_t = Type::NEVER;
        for ret_or_yield in func_node_ref.iter_return_or_yield() {
            match ret_or_yield {
                ReturnOrYield::Return(return_stmt) => {
                    let inferred = match return_stmt.star_expressions() {
                        Some(star_exprs) => {
                            let Some(inf) = self.infer_star_exprs(star_exprs) else {
                                debug!(
                                    "Heuristics: Aborting execution because return '{}' \
                                             was not calculated",
                                    limit_length_for_debug(star_exprs.as_code()),
                                );
                                return None;
                            };
                            inf.into()
                        }
                        None => Inferred::new_none(),
                    };
                    result_t.union_in_place(inferred.into_type(self.inference.i_s))
                }
                ReturnOrYield::Yield(_yield_expr) => todo!(),
            }
        }
        Some(result_t)
    }

    fn infer_star_exprs(&mut self, star_exprs: StarExpressions) -> Option<Heuristic> {
        Some(match star_exprs.unpack() {
            StarExpressionContent::Expression(expr) => self.infer_expression(expr),
            // This is invalid anyway
            StarExpressionContent::StarExpression(_) => Heuristic::new_any_due_to_error(),
            StarExpressionContent::Tuple(tuple) => {
                let tuple = Tuple::new_fixed_length(
                    tuple
                        .iter()
                        .map(|s| {
                            let inf: Inferred = match s {
                                StarLikeExpression::Expression(e) => self.infer_expression(e),
                                StarLikeExpression::NamedExpression(ne) => {
                                    self.infer_expression(ne.expression())
                                }
                                StarLikeExpression::StarExpression(_)
                                | StarLikeExpression::StarNamedExpression(_) => {
                                    debug!("Heuristics: TODO star exprs tuple calculation");
                                    return None;
                                }
                            }
                            .into();
                            Some(inf.into_type(self.inference.i_s))
                        })
                        .collect::<Option<_>>()?,
                );
                return Some(Heuristic::Guess(Inferred::from_type(Type::Tuple(tuple))));
            }
        })
    }

    fn infer_primary_or_atom(&mut self, p_or_a: PrimaryOrAtom) -> Heuristic {
        match p_or_a {
            PrimaryOrAtom::Primary(p) => self.infer_primary(p),
            PrimaryOrAtom::Atom(a) => self.infer_atom(a),
        }
    }

    fn infer_expression(&mut self, expr: Expression) -> Heuristic {
        let inf = self.inference.infer_expression(expr);
        debug!(
            "Heuristics for expr: {}",
            limit_length_for_debug(expr.as_code())
        );
        self.create_heuristic_if_necessary(inf, |slf| {
            Some(match expr.unpack() {
                ExpressionContent::ExpressionPart(expr_part) => match expr_part {
                    ExpressionPart::Atom(atom) => slf.infer_atom(atom),
                    ExpressionPart::Primary(primary) => slf.infer_primary(primary),
                    _ => return None,
                    /*
                    ExpressionPart::AwaitPrimary(await_primary) => todo!(),
                    ExpressionPart::Power(power) => todo!(),
                    ExpressionPart::Factor(factor) => todo!(),
                    ExpressionPart::Term(term) => todo!(),
                    ExpressionPart::Sum(sum) => todo!(),
                    ExpressionPart::ShiftExpr(shift_expr) => todo!(),
                    ExpressionPart::BitwiseAnd(bitwise_and) => todo!(),
                    ExpressionPart::BitwiseXor(bitwise_xor) => todo!(),
                    ExpressionPart::BitwiseOr(bitwise_or) => todo!(),
                    ExpressionPart::Comparisons(comparisons) => todo!(),
                    ExpressionPart::Inversion(inversion) => todo!(),
                    ExpressionPart::Conjunction(conjunction) => todo!(),
                    ExpressionPart::Disjunction(disjunction) => todo!(),
                    */
                },
                ExpressionContent::Ternary(_ternary) => return None, // TODO
                ExpressionContent::Lambda(_lambda) => return None,   // TODO
            })
        })
    }
}

impl<'db> PositionalDocument<'db, GotoNode<'db>> {
    pub fn infer_heuristics_if_possible(&self) -> Option<Inferred> {
        debug!("Try to find heuristics");
        let _indent = debug_indent();
        self.with_i_s(|i_s| {
            let mut heuristic = HeuristicInference {
                state: &mut HeuristicState {
                    callable_search_cache: Default::default(),
                    call_stack: Default::default(),
                    self_stack: Default::default(),
                },
                inference: self.file.inference(i_s),
            };
            match self.node {
                GotoNode::Name(name) => heuristic.infer_name(name)?,
                GotoNode::Primary(primary) => heuristic.infer_primary(primary),
                /*
                GotoNode::PrimaryTarget(primary) => (),
                GotoNode::ImportFromAsName { .. } => (),
                GotoNode::GlobalName(_) | GotoNode::NonlocalName(_) | GotoNode::Atom(_) => (),
                GotoNode::Operator { .. } | GotoNode::AugAssignOperator { .. } | GotoNode::None => (),
                */
                _ => return None,
            }
            .maybe_guessed()
        })
    }
}

struct PotentialFileIterator<'db> {
    file: &'db PythonFile,
    //already_checked: HashSet<Arc<FileEntry>>,
}

impl<'db> Iterator for PotentialFileIterator<'db> {
    type Item = &'db PythonFile;

    fn next(&mut self) -> Option<Self::Item> {
        None
    }
}

struct FileNameSearcher<'db, 'regex> {
    db: &'db Database,
    potential_files: PotentialFileIterator<'db>,
    regex: &'regex Regex,
    current_file: &'db PythonFile,
    wanted_name: PointLink,
    matches: std::iter::Take<Matches<'regex, 'db>>,
    found_in_current_file: bool,
}

impl<'db, 'regex> FileNameSearcher<'db, 'regex> {
    fn new(
        db: &'db Database,
        file: &'db PythonFile,
        regex: &'regex Regex,
        wanted_name: PointLink,
    ) -> Self {
        Self {
            db,
            potential_files: PotentialFileIterator { file },
            regex,
            current_file: file,
            wanted_name,
            matches: regex
                .find_iter(file.tree.code())
                .take(PER_FILE_SEARCH_NAME_LIMIT),
            found_in_current_file: false,
        }
    }
}

#[derive(Debug)]
struct FoundExecution<'db> {
    file: &'db PythonFile,
    scope: Scope<'db>,
    primary: Primary<'db>,
    details: ArgumentsDetails<'db>,
}

impl<'db> Iterator for FileNameSearcher<'db, '_> {
    type Item = FoundExecution<'db>;

    fn next(&mut self) -> Option<Self::Item> {
        for match_ in &mut self.matches {
            let (scope, node) = self
                .current_file
                .tree
                .goto_node(match_.range().start as NodeIndex);
            if let Some(name) = node.on_name()
                && let Some(primary) = name.maybe_left_of_primary()
                && let PrimaryContent::Execution(details) = primary.second()
            {
                if matches!(details, ArgumentsDetails::None) {
                    continue;
                }
                let result = self.current_file.ensure_calculated_diagnostics(self.db);
                debug_assert!(result.is_ok());
                let point = self.current_file.points.get(name.index());
                if point.calculated() && point.kind() == PointKind::Redirect {
                    let node_ref = point.as_redirected_node_ref(self.db);
                    if let Some(FollowImportResult::TreeName(tree_name)) =
                        check_node_ref_and_maybe_follow_import(self.db, node_ref, true)
                        && tree_name.file.file_index == self.wanted_name.file
                        && tree_name.cst_name.index() == self.wanted_name.node_index
                    {
                        self.found_in_current_file = true;
                        return Some(FoundExecution {
                            file: self.current_file,
                            scope,
                            primary,
                            details,
                        });
                    }
                }
            }
        }
        if self.found_in_current_file {
            // If there are results after processing a module where we have found a result,
            // we're probably good to abort. This is a speed optimization.
            return None;
        }
        self.current_file = self.potential_files.next()?;
        self.matches = self
            .regex
            .find_iter(self.current_file.tree.code())
            .take(PER_FILE_SEARCH_NAME_LIMIT);
        self.next()
    }
}
