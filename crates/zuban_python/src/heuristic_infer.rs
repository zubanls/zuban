use std::rc::Rc;

use parsa_python_cst::{
    Arguments, ArgumentsDetails, Atom, AtomContent, Comprehension, Expression, ExpressionContent,
    ExpressionPart, FunctionDef, GotoNode, Name, NameParent, NodeIndex, Primary, PrimaryContent,
    PrimaryOrAtom, ReturnOrYield, Scope, StarExpressionContent, StarExpressions, TypeLike,
};
use regex::{Matches, Regex};
use utils::FastHashMap;

use crate::{
    arguments::{ArgKind, Args as _, SimpleArgs},
    database::{Database, PointKind, PointLink},
    debug,
    file::{FuncNodeRef, Inference, PythonFile},
    goto::{
        FollowImportResult, PositionalDocument, check_node_ref_and_maybe_follow_import,
        try_to_follow,
    },
    inference_state::{InferenceState, Mode},
    inferred::Inferred,
    node_ref::NodeRef,
    params::{InferrableParam, ParamArgument},
    result_context::ResultContext,
    type_::{FunctionKind, Type},
    type_helpers::{Function, FunctionParam},
    utils::{debug_indent, limit_length_for_debug},
};

// Stats from a 2016 Lenovo Notebook running Linux:
// With os.walk, it takes about 10s to scan 11'000 files (without filesystem
// caching). Once cached it only takes 5s.
const OPENED_FILE_LIMIT: usize = 200;
const PARSED_FILE_LIMIT: usize = 10;
const MAX_PARAM_SEARCHES: usize = 20;
const PER_FILE_SEARCH_NAME_LIMIT: usize = 20;

#[derive(Debug, Copy, Clone)]
enum ArgumentsFrameKind {
    Arguments(NodeIndex),
    Comprehension(NodeIndex),
}

#[derive(Debug)]
struct ArgumentsFrame<'db> {
    file: &'db PythonFile,
    primary_node_index: NodeIndex,
    kind: ArgumentsFrameKind,
}

struct HeuristicState<'db> {
    callable_search_cache: FastHashMap<PointLink, Rc<[FoundExecution<'db>]>>,
    call_stack: Vec<(FuncNodeRef<'db>, ArgumentsFrame<'db>)>,
}

struct HeuristicInference<'db, 'state, 'i_s> {
    state: &'state mut HeuristicState<'db>,
    inference: Inference<'db, 'db, 'i_s>,
}

enum Heuristic {
    WellKnown(Inferred),
    Guess(Inferred),
}

impl From<Heuristic> for Inferred {
    fn from(value: Heuristic) -> Self {
        match value {
            Heuristic::WellKnown(inferred) | Heuristic::Guess(inferred) => inferred,
        }
    }
}

impl Heuristic {
    fn new_any_due_to_error() -> Self {
        Self::WellKnown(Inferred::new_any_from_error())
    }

    fn maybe_guessed(self) -> Option<Inferred> {
        match self {
            Heuristic::WellKnown(_) => None,
            Heuristic::Guess(inferred) => Some(inferred),
        }
    }
}

impl<'db, 'state> HeuristicInference<'db, '_, 'state> {
    fn with_different_file<T>(
        &mut self,
        file: &'db PythonFile,
        callback: impl FnOnce(&mut HeuristicInference<'db, '_, '_>) -> T,
    ) -> T {
        InferenceState::new(self.inference.i_s.db, file)
            .avoid_errors_within(|i_s| {
                callback(&mut HeuristicInference {
                    state: self.state,
                    inference: file.inference(i_s),
                })
            })
            .0
    }

    fn infer_name(&mut self, name: Name<'db>) -> Option<Inferred> {
        match name.parent() {
            NameParent::Atom(_) | NameParent::Error => self.infer_name_reference(name),
            NameParent::NameDef(name_def) => match name_def.expect_type() {
                TypeLike::ParamName(_) => {
                    let func = name.expect_as_param_of_function();
                    let func_node_ref = FuncNodeRef::new(self.inference.file, func.index());
                    if let Some((_, args_frame)) = self
                        .state
                        .call_stack
                        .iter()
                        .find(|frame| frame.0 == func_node_ref)
                    {
                        let details = match args_frame.kind {
                            ArgumentsFrameKind::Arguments(args_index) => ArgumentsDetails::Node(
                                Arguments::by_index(&args_frame.file.tree, args_index),
                            ),
                            ArgumentsFrameKind::Comprehension(comp_index) => {
                                ArgumentsDetails::Comprehension(Comprehension::by_index(
                                    &args_frame.file.tree,
                                    comp_index,
                                ))
                            }
                        };
                        let args = SimpleArgs::new(
                            InferenceState::new(self.inference.i_s.db, args_frame.file),
                            args_frame.file,
                            args_frame.primary_node_index,
                            details,
                        );
                        let func = Function::new_with_unknown_parent(
                            self.inference.i_s.db,
                            NodeRef::new(self.inference.file, func.index()),
                        );
                        let mut skip_first_param = false;
                        if func.class.is_some() {
                            match func.kind(self.inference.i_s) {
                                FunctionKind::Staticmethod => (),
                                _ => skip_first_param = true,
                            }
                        }
                        return self.infer_param_with_args(&func, args, skip_first_param, name);
                    }
                    self.search_callable_arguments(func, name)
                }
                TypeLike::Assignment(_) => None, // TODO
                _ => None,
            },
            NameParent::Primary(primary) => self.infer_primary(primary).maybe_guessed(),
            /*
            NameParent::PrimaryTarget(primary_target) => (),
            NameParent::KeywordPattern(keyword_pattern) => (),
            NameParent::DottedPatternName(dotted_pattern_name) => (),
            NameParent::FStringConversion(fstring_conversion) => (),
            */
            _ => None,
        }
    }

    fn infer_name_reference(&mut self, name: Name) -> Option<Inferred> {
        debug!("Heuristic follow name: {}", name.as_code());
        match try_to_follow(
            self.inference.i_s.db,
            NodeRef::new(self.inference.file, name.index()),
            true,
        )?? {
            FollowImportResult::File(file_index) => Some(Inferred::new_file_reference(file_index)),
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

        executions
            .iter()
            .filter_map(|execution| {
                let args = SimpleArgs::new(
                    InferenceState::new(db, execution.file),
                    execution.file,
                    execution.primary.index(),
                    execution.details,
                );
                self.infer_param_with_args(&func, args, skip_first_param, param_name)
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

    fn infer_param_with_args(
        &mut self,
        func: &Function,
        args: SimpleArgs<'db, 'db>,
        skip_first_param: bool,
        search_param_name: Name,
    ) -> Option<Inferred> {
        for param in func.iter_args_with_params(
            self.inference.i_s.db,
            args.iter(Mode::Normal),
            skip_first_param,
        ) {
            if param.param.name_def().name_index() == search_param_name.index() {
                if let Some(found) =
                    self.with_different_file(args.file, |h| h.infer_param(args.file, param))
                {
                    return Some(found);
                }
            }
        }
        None
    }

    fn infer_param(
        &mut self,
        argument_file: &'db PythonFile,
        param: InferrableParam<FunctionParam>,
    ) -> Option<Inferred> {
        let result = self.with_different_file(argument_file, |h| h.infer_argument(param.argument));
        if let Some(default) = param.param.default() {
            let inferred_default: Inferred = self.infer_expression(default).into();
            if let Some(result) = result {
                return Some(Inferred::from_type(
                    result
                        .as_type(&InferenceState::new(self.inference.i_s.db, argument_file))
                        .union(inferred_default.as_type(self.inference.i_s)),
                ));
            }
            return Some(inferred_default);
        }
        result
    }

    fn infer_argument(&mut self, argument: ParamArgument) -> Option<Inferred> {
        match argument {
            ParamArgument::None => None,
            ParamArgument::Argument(arg) => match arg.kind {
                ArgKind::Positional(arg) => {
                    Some(self.infer_expression(arg.named_expr.expression()).into())
                }
                ArgKind::Keyword(kw) => Some(self.infer_expression(kw.expression).into()),
                ArgKind::Inferred { inferred, .. }
                | ArgKind::InferredWithCustomAddIssue { inferred, .. }
                | ArgKind::Overridden { inferred, .. } => Some(inferred),
                ArgKind::StarredWithUnpack { .. } | ArgKind::ParamSpec { .. } => None,
                ArgKind::Comprehension { comprehension, .. } => todo!(),
            },
            ParamArgument::TupleUnpack(_args) => todo!(),
            ParamArgument::MatchedUnpackedTypedDictMember { type_, .. } => todo!(),
            ParamArgument::ParamSpecArgs(..) => todo!(),
        }
    }

    pub fn infer_atom(&mut self, atom: Atom) -> Heuristic {
        let inf = self.inference.infer_atom(atom, &mut ResultContext::Unknown);
        self.create_heuristic_if_necessary(inf, |slf| {
            debug!(
                "Heuristics for atom: {}",
                limit_length_for_debug(atom.as_code())
            );
            match atom.unpack() {
                AtomContent::Name(name) => return slf.infer_name_reference(name),
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
            }
            .maybe_guessed()
        })
    }

    fn infer_primary(&mut self, primary: Primary) -> Heuristic {
        let inf = self
            .inference
            .infer_primary(primary, &mut ResultContext::Unknown);
        self.create_heuristic_if_necessary(inf, |slf| {
            let first = slf.infer_primary_or_atom(primary.first()).into();
            slf.infer_primary_or_primary_t_content(first, primary.index(), primary.second())?
                .maybe_guessed()
        })
    }

    fn create_heuristic_if_necessary(
        &mut self,
        inf: Inferred,
        infer_heuristic: impl FnOnce(&mut Self) -> Option<Inferred>,
    ) -> Heuristic {
        let t = inf.as_cow_type(self.inference.i_s);
        if let Some(mut without_any) = t.maybe_remove_any(self.inference.i_s.db) {
            if let Some(new) = infer_heuristic(self) {
                without_any.union_in_place(new.into_type(self.inference.i_s));
                return Heuristic::Guess(Inferred::from_type(without_any));
            }
        }
        Heuristic::WellKnown(inf)
    }

    fn infer_primary_or_primary_t_content(
        &mut self,
        base: Inferred,
        primary_node_index: NodeIndex,
        content: PrimaryContent,
    ) -> Option<Heuristic> {
        match content {
            PrimaryContent::Attribute(_) => None,
            PrimaryContent::Execution(details) => {
                let node_ref = base.maybe_saved_node_ref(self.inference.i_s.db)?;
                node_ref.maybe_function()?;
                let func_node_ref = FuncNodeRef::from_node_ref(node_ref);
                if func_node_ref.is_generator() {
                    return None; // TODO make generators possible
                }

                let args_frame = ArgumentsFrame {
                    file: self.inference.file,
                    kind: match details {
                        ArgumentsDetails::None => return None,
                        ArgumentsDetails::Node(arguments) => {
                            ArgumentsFrameKind::Arguments(arguments.index())
                        }
                        ArgumentsDetails::Comprehension(comprehension) => {
                            ArgumentsFrameKind::Comprehension(comprehension.index())
                        }
                    },
                    primary_node_index,
                };
                self.state.call_stack.push((func_node_ref, args_frame));
                let mut result_t = Type::NEVER;
                for ret_or_yield in func_node_ref.iter_return_or_yield() {
                    match ret_or_yield {
                        ReturnOrYield::Return(return_stmt) => {
                            let inferred = match return_stmt.star_expressions() {
                                Some(star_exprs) => self.infer_star_exprs(star_exprs)?.into(),
                                None => Inferred::new_none(),
                            };
                            result_t.union_in_place(inferred.into_type(self.inference.i_s))
                        }
                        ReturnOrYield::Yield(_yield_expr) => todo!(),
                    }
                }
                self.state.call_stack.pop();
                if result_t.is_never() {
                    return None;
                }
                Some(Heuristic::Guess(Inferred::from_type(result_t)))
            }
            PrimaryContent::GetItem(_) => None,
        }
    }

    fn infer_star_exprs(&mut self, star_exprs: StarExpressions) -> Option<Heuristic> {
        Some(match star_exprs.unpack() {
            StarExpressionContent::Expression(expr) => self.infer_expression(expr),
            // This is invalid anyway
            StarExpressionContent::StarExpression(_) => Heuristic::new_any_due_to_error(),
            StarExpressionContent::Tuple(_tuple) => {
                // TODO implement
                return None;
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
        self.create_heuristic_if_necessary(inf, |slf| {
            debug!(
                "Heuristics for expr: {}",
                limit_length_for_debug(expr.as_code())
            );
            match expr.unpack() {
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
                ExpressionContent::Ternary(_ternary) => todo!(),
                ExpressionContent::Lambda(_lambda) => todo!(),
            }
            .maybe_guessed()
        })
    }
}

impl<'db> PositionalDocument<'db, GotoNode<'db>> {
    pub fn infer_heuristics_if_possible(&self) -> Option<Inferred> {
        debug!("Try to find heuristics");
        self.with_i_s(|i_s| {
            let mut heuristic = HeuristicInference {
                state: &mut HeuristicState {
                    callable_search_cache: Default::default(),
                    call_stack: Default::default(),
                },
                inference: self.file.inference(i_s),
            };
            match self.node {
                GotoNode::Name(name) => heuristic.infer_name(name),
                GotoNode::Primary(primary) => heuristic.infer_primary(primary).maybe_guessed(),
                /*
                GotoNode::PrimaryTarget(primary) => (),
                GotoNode::ImportFromAsName { .. } => (),
                GotoNode::GlobalName(_) | GotoNode::NonlocalName(_) | GotoNode::Atom(_) => (),
                GotoNode::Operator { .. } | GotoNode::AugAssignOperator { .. } | GotoNode::None => (),
                */
                _ => None,
            }
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
