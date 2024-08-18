use std::cell::RefCell;

use parsa_python_cst::*;

use crate::{
    database::{
        ClassStorage, ComplexPoint, FileIndex, Locality, ParentScope, Point, PointKind, Points,
        Specific,
    },
    debug,
    diagnostics::{Diagnostics, Issue, IssueKind},
    file::{python_file::StarImport, ComplexValues},
    python_state::NAME_TO_FUNCTION_DIFF,
    type_::StringSlice,
    utils::SymbolTable,
    TypeCheckerFlags,
};

use super::python_file::MultiDefinitionIterator;

pub const GLOBAL_NONLOCAL_TO_NAME_DIFFERENCE: NodeIndex = 2;

#[derive(PartialEq, Debug)]
enum NameBinderKind {
    Global,
    Function { is_async: bool },
    Class,
    Lambda,
    Comprehension,
}

enum Unresolved<'db> {
    FunctionDef {
        func: FunctionDef<'db>,
        is_method: bool,
        is_async: bool,
    },
    Lambda(Lambda<'db>),
    Comprehension(Comprehension<'db>),
    #[allow(dead_code)] // TODO remove this
    DictComprehension(DictComprehension<'db>),
    Name(Name<'db>),
}

struct UnresolvedClass<'db> {
    class_def: ClassDef<'db>,
    parent_scope: ParentScope,
    class_symbol_table: SymbolTable,
    abstract_attributes: Box<[NodeIndex]>,
}

#[derive(Clone, Copy)]
pub struct DbInfos<'db> {
    pub flags: &'db TypeCheckerFlags,
    pub tree: &'db Tree,
    pub points: &'db Points,
    pub complex_points: &'db ComplexValues,
    pub issues: &'db Diagnostics,
    pub star_imports: &'db RefCell<Vec<StarImport>>,
    pub file_index: FileIndex,
    pub is_stub: bool,
}

pub(crate) struct NameBinder<'db> {
    db_infos: DbInfos<'db>,
    kind: NameBinderKind,
    scope_node: NodeIndex,
    symbol_table: SymbolTable,
    unordered_references: Vec<UnorderedReference<'db>>,
    unresolved_nodes: Vec<Unresolved<'db>>,
    names_to_be_resolved_in_parent: Vec<Name<'db>>,
    unresolved_class_self_vars: Vec<UnresolvedClass<'db>>,
    annotation_names: Vec<Name<'db>>,
    references_need_flow_analysis: bool,
    parent: Option<*mut NameBinder<'db>>,
}

impl<'db> NameBinder<'db> {
    fn new(
        db_infos: DbInfos<'db>,
        kind: NameBinderKind,
        scope_node: NodeIndex,
        parent: Option<*mut Self>,
    ) -> Self {
        Self {
            db_infos,
            kind,
            scope_node,
            symbol_table: SymbolTable::default(),
            unordered_references: vec![],
            unresolved_nodes: vec![],
            names_to_be_resolved_in_parent: vec![],
            unresolved_class_self_vars: vec![],
            annotation_names: vec![],
            references_need_flow_analysis: false,
            parent,
        }
    }

    pub(crate) fn with_global_binder(
        db_infos: DbInfos<'db>,
        func: impl FnOnce(&mut NameBinder<'db>),
    ) -> SymbolTable {
        let mut binder = NameBinder::new(db_infos, NameBinderKind::Global, 0, None);
        func(&mut binder);
        binder.close();

        // At the end of
        while let Some(unresolved_class) = binder.unresolved_class_self_vars.pop() {
            let self_symbol_table = binder.index_self_vars(unresolved_class.class_def);
            let mut slots = None;
            if let Some(slots_index) = unresolved_class
                .class_symbol_table
                .lookup_symbol("__slots__")
            {
                if let Some(assignment) =
                    Name::by_index(db_infos.tree, slots_index).maybe_assignment_definition_name()
                {
                    slots = gather_slots(db_infos.file_index, assignment);
                }
            }
            binder.db_infos.complex_points.insert(
                binder.db_infos.points,
                unresolved_class.class_def.index(),
                ComplexPoint::Class(Box::new(ClassStorage {
                    class_symbol_table: unresolved_class.class_symbol_table,
                    abstract_attributes: unresolved_class.abstract_attributes,
                    self_symbol_table,
                    parent_scope: unresolved_class.parent_scope,
                    promote_to: Default::default(),
                    slots,
                })),
                Locality::File,
            );
        }
        for annotation_name in &binder.annotation_names {
            try_to_process_reference_for_symbol_table(
                &mut binder.symbol_table,
                binder.db_infos.file_index,
                binder.db_infos.points,
                *annotation_name,
                false,
            );
        }
        binder.symbol_table
    }

    fn with_nested(
        &mut self,
        kind: NameBinderKind,
        scope_node: NodeIndex,
        func: impl FnOnce(&mut NameBinder<'db>),
    ) -> SymbolTable {
        let mut name_binder = NameBinder::new(self.db_infos, kind, scope_node, Some(self));
        name_binder.references_need_flow_analysis = self.references_need_flow_analysis;
        func(&mut name_binder);
        name_binder.close();
        let NameBinder {
            unresolved_nodes,
            names_to_be_resolved_in_parent,
            annotation_names,
            unresolved_class_self_vars,
            mut symbol_table,
            ..
        } = name_binder;
        self.unresolved_class_self_vars
            .extend(unresolved_class_self_vars);
        self.unresolved_nodes.extend(
            names_to_be_resolved_in_parent
                .into_iter()
                .map(Unresolved::Name),
        );
        self.unresolved_nodes.extend(unresolved_nodes);
        for annotation_name in annotation_names {
            if !try_to_process_reference_for_symbol_table(
                &mut symbol_table,
                self.db_infos.file_index,
                self.db_infos.points,
                annotation_name,
                false,
            ) {
                self.annotation_names.push(annotation_name);
            }
        }
        symbol_table
    }

    fn add_issue(&self, node_index: NodeIndex, kind: IssueKind) {
        let issue = Issue::from_node_index(self.db_infos.tree, node_index, kind);
        let maybe_ignored = self
            .db_infos
            .tree
            .type_ignore_comment_for(issue.start_position, issue.end_position);
        match self
            .db_infos
            .issues
            .add_if_not_ignored(issue, maybe_ignored)
        {
            Ok(issue) => debug!("New name binder issue: {:?}", issue.kind),
            Err(issue) => debug!("New ignored name binder issue: {:?}", issue.kind),
        }
    }

    fn add_new_walrus_definition(&mut self, name_def: NameDef<'db>) {
        if matches!(self.kind, NameBinderKind::Comprehension) {
            // Walrus `:=` operators are available outside of comprehensions and therefore need to
            // be added to the parent.
            unsafe { &mut *self.parent.unwrap() }.add_new_walrus_definition(name_def)
        } else {
            self.add_new_definition(name_def, Point::new_uncalculated())
        }
    }

    fn add_new_definition(&mut self, name_def: NameDef<'db>, point: Point) {
        if let Some(first) = self.symbol_table.lookup_symbol(name_def.as_code()) {
            self.ensure_multi_definition(name_def, first)
        } else {
            self.symbol_table.add_or_replace_symbol(name_def.name());
        }
        self.db_infos.points.set(name_def.index(), point);
    }

    fn ensure_multi_definition(&mut self, name_def: NameDef, first_index: NodeIndex) {
        let mut latest_name_index = first_index;
        loop {
            let point = self.db_infos.points.get(latest_name_index);
            if point.calculated()
                && point.specific() == Specific::NameOfNameDef
                && point.node_index() > first_index
            {
                debug_assert_ne!(latest_name_index, point.node_index());
                latest_name_index = point.node_index()
            } else {
                let new_index = name_def.name().index();
                self.references_need_flow_analysis = true;
                self.db_infos.points.set(
                    latest_name_index,
                    Point::new_name_of_name_def(new_index, Locality::File),
                );
                // Here we create a loop, so it's easy to find the relevant definitions from
                // any point.
                self.db_infos.points.set(
                    new_index,
                    Point::new_name_of_name_def(first_index, Locality::File),
                );
                break;
            }
        }
    }

    fn add_point_definition(&mut self, name_def: NameDef<'db>, specific: Specific) {
        self.add_new_definition(name_def, Point::new_specific(specific, Locality::Stmt));
    }

    pub(crate) fn index_file(&mut self, file_node: File<'db>) {
        self.index_stmts(file_node.iter_stmt_likes(), true);
    }

    fn index_block(&mut self, block: Block<'db>, ordered: bool) -> NodeIndex {
        // Returns the latest return/yield index
        // Theory:
        // - while_stmt, for_stmt: ignore order (at least mostly)
        // - match_stmt, if_stmt, try_stmt (only in coresponding blocks and after)
        // - sync_for_if_clause: reversed order and only in scope
        // - lambda: only in scope
        // - function_def, class_def: ignore
        self.index_stmts(block.iter_stmt_likes(), ordered)
    }

    fn index_stmts(&mut self, mut stmts: StmtLikeIterator<'db>, ordered: bool) -> NodeIndex {
        let mut latest_return_or_yield = 0;
        let mut last_was_an_error = false;
        for stmt_like in stmts.by_ref() {
            let return_or_yield = match stmt_like.node {
                StmtLikeContent::Assignment(assignment) => {
                    let unpacked = assignment.unpack_with_simple_targets();
                    // First we have to index the right side, before we can begin indexing the left
                    // side.
                    match &unpacked {
                        AssignmentContentWithSimpleTargets::Normal(_, right)
                        | AssignmentContentWithSimpleTargets::WithAnnotation(_, _, Some(right))
                        | AssignmentContentWithSimpleTargets::AugAssign(_, _, right) => {
                            let latest = match right {
                                AssignmentRightSide::YieldExpr(yield_expr) => {
                                    self.index_non_block_node(yield_expr, ordered)
                                }
                                AssignmentRightSide::StarExpressions(star_exprs) => {
                                    self.index_non_block_node(star_exprs, ordered)
                                }
                            };
                            latest_return_or_yield =
                                self.merge_latest_return_or_yield(latest_return_or_yield, latest);
                        }
                        _ => (),
                    };
                    match unpacked {
                        AssignmentContentWithSimpleTargets::Normal(targets, _) => {
                            for target in targets {
                                let l = self.index_non_block_node(&target, ordered);
                                latest_return_or_yield =
                                    self.merge_latest_return_or_yield(latest_return_or_yield, l);
                            }
                            0
                        }
                        AssignmentContentWithSimpleTargets::WithAnnotation(
                            target,
                            annotation,
                            _,
                        ) => {
                            self.index_annotation_expression(&annotation.expression());
                            self.index_non_block_node(&target, ordered)
                        }
                        AssignmentContentWithSimpleTargets::AugAssign(target, _, _) => {
                            self.index_non_block_node(&target, ordered)
                        }
                    }
                }
                StmtLikeContent::ReturnStmt(return_stmt) => {
                    if !matches!(self.kind, NameBinderKind::Function { .. }) {
                        self.add_issue(
                            return_stmt.index(),
                            IssueKind::StmtOutsideFunction { keyword: "return" },
                        )
                    }
                    if let Some(return_expr) = return_stmt.star_expressions() {
                        let l = self.index_non_block_node_full(&return_expr, ordered, false);
                        latest_return_or_yield =
                            self.merge_latest_return_or_yield(latest_return_or_yield, l);
                    }
                    self.index_return_or_yield(&mut latest_return_or_yield, return_stmt.index());
                    break;
                }
                StmtLikeContent::AssertStmt(assert_stmt) => {
                    let (assert_expr, error_expr) = assert_stmt.unpack();
                    let latest = self.index_non_block_node_full(&assert_expr, ordered, false);
                    self.references_need_flow_analysis = true;
                    if let Some(error_expr) = error_expr {
                        self.index_non_block_node_full(&error_expr, ordered, false);
                    }
                    if is_expr_reachable_for_name_binder(self.db_infos.flags, assert_expr)
                        == Truthiness::False
                    {
                        self.db_infos.points.set(
                            assert_stmt.index(),
                            Point::new_specific(Specific::AssertAlwaysFails, Locality::File),
                        );
                        latest_return_or_yield =
                            self.merge_latest_return_or_yield(latest_return_or_yield, latest);
                        break;
                    }
                    latest
                }
                StmtLikeContent::ImportFrom(import) => {
                    match import.unpack_targets() {
                        ImportFromTargets::Star(star) => {
                            self.db_infos.star_imports.borrow_mut().push(StarImport {
                                scope: self.scope_node,
                                import_from_node: import.index(),
                                star_node: star.index(),
                            })
                        }
                        ImportFromTargets::Iterator(targets) => {
                            for target in targets {
                                self.index_non_block_node(&target, ordered);
                            }
                        }
                    };
                    0
                }
                StmtLikeContent::RaiseStmt(raise_stmt) => {
                    let l = self.index_non_block_node(&raise_stmt, ordered);
                    latest_return_or_yield =
                        self.merge_latest_return_or_yield(latest_return_or_yield, l);
                    break;
                }
                StmtLikeContent::BreakStmt(_) | StmtLikeContent::ContinueStmt(_) => break,
                StmtLikeContent::DelStmt(del_stmt) => {
                    self.references_need_flow_analysis = true;
                    self.index_non_block_node(&del_stmt, ordered)
                }
                StmtLikeContent::StarExpressions(s) => self.index_non_block_node(&s, ordered),
                StmtLikeContent::YieldExpr(y) => self.index_non_block_node(&y, ordered),
                StmtLikeContent::ImportName(i) => self.index_non_block_node(&i, ordered),
                StmtLikeContent::GlobalStmt(g) => self.index_non_block_node(&g, ordered),
                StmtLikeContent::NonlocalStmt(n) => self.index_non_block_node(&n, ordered),
                StmtLikeContent::FunctionDef(func) => {
                    self.index_function_name_and_param_defaults(
                        func, ordered, false, // decorators
                        false, // is_async
                    );
                    0
                }
                StmtLikeContent::ClassDef(class) => {
                    self.index_class(class, false);
                    0
                }
                StmtLikeContent::Decorated(decorated) => {
                    for decorator in decorated.decorators().iter() {
                        self.index_non_block_node(&decorator, ordered);
                    }
                    match decorated.decoratee() {
                        Decoratee::FunctionDef(func) => {
                            self.index_function_name_and_param_defaults(
                                func, ordered, true, false, // is_async
                            );
                        }
                        Decoratee::AsyncFunctionDef(func) => {
                            self.index_function_name_and_param_defaults(
                                func, ordered, true, true, // is_async
                            );
                        }
                        Decoratee::ClassDef(cls) => {
                            self.index_class(cls, true);
                        }
                    }
                    0
                }
                StmtLikeContent::IfStmt(if_stmt) => self.index_if_stmt(if_stmt, ordered),
                StmtLikeContent::ForStmt(for_stmt) => self.index_for_stmt(for_stmt, ordered),
                StmtLikeContent::TryStmt(try_stmt) => self.index_try_stmt(try_stmt, ordered),
                StmtLikeContent::WhileStmt(while_stmt) => {
                    self.index_while_stmt(while_stmt, ordered)
                }
                StmtLikeContent::WithStmt(with_stmt) => self.index_with_stmt(with_stmt, ordered),
                StmtLikeContent::MatchStmt(match_stmt) => {
                    self.index_match_stmt(match_stmt, ordered)
                }
                StmtLikeContent::AsyncStmt(async_stmt) => match async_stmt.unpack() {
                    AsyncStmtContent::FunctionDef(function_def) => {
                        self.index_function_name_and_param_defaults(
                            function_def,
                            ordered,
                            false, // decorators
                            true,
                        );
                        0
                    }
                    AsyncStmtContent::ForStmt(for_stmt) => self.index_for_stmt(for_stmt, ordered),
                    AsyncStmtContent::WithStmt(with_stmt) => {
                        self.index_with_stmt(with_stmt, ordered)
                    }
                },
                StmtLikeContent::Error(error) => {
                    if !last_was_an_error {
                        last_was_an_error = true;
                        self.add_issue(error.index(), IssueKind::InvalidSyntax);
                    }
                    continue;
                }
                StmtLikeContent::Newline | StmtLikeContent::PassStmt(_) => 0,
            };
            last_was_an_error = false;
            latest_return_or_yield =
                self.merge_latest_return_or_yield(latest_return_or_yield, return_or_yield);
        }
        for stmt_like in stmts {
            if let StmtLikeContent::YieldExpr(y) = stmt_like.node {
                self.index_return_or_yield(&mut latest_return_or_yield, y.index());
            }
        }
        latest_return_or_yield
    }

    fn merge_latest_return_or_yield(&self, first: NodeIndex, mut second: NodeIndex) -> NodeIndex {
        if first != 0 && second != 0 {
            loop {
                let point = self.db_infos.points.get(second);
                let node_index = point.node_index();
                if node_index == 0 {
                    // Now that we have the first node in the chain of the second nodes, link that
                    // to the first one (like a linked list)
                    self.db_infos.points.set(
                        second,
                        Point::new_node_analysis_with_node_index(Locality::File, first),
                    );
                    break;
                } else {
                    assert!(node_index < second);
                    second = node_index;
                }
            }
        }
        if second == 0 {
            first
        } else {
            second
        }
    }

    fn close(&mut self) {
        if self.kind != NameBinderKind::Class {
            while let Some(n) = self.unresolved_nodes.pop() {
                match n {
                    Unresolved::Name(name) => {
                        if !self.try_to_process_reference(name) {
                            self.names_to_be_resolved_in_parent.push(name);
                        }
                    }
                    Unresolved::FunctionDef {
                        func,
                        is_method,
                        is_async,
                    } => {
                        let symbol_table = self.with_nested(
                            NameBinderKind::Function { is_async },
                            func.index(),
                            |binder| binder.index_function_body(func, is_method),
                        );
                    }
                    Unresolved::Lambda(lambda) => {
                        self.with_nested(NameBinderKind::Lambda, lambda.index(), |binder| {
                            binder.index_lambda(lambda)
                        });
                    }
                    Unresolved::Comprehension(comp) => self.index_comprehension(comp, true),
                    Unresolved::DictComprehension(comp) => {
                        self.index_dict_comprehension(comp, true)
                    }
                };
            }
        }
        self.index_unordered_references();
        debug_assert_eq!(self.unordered_references.len(), 0);
    }

    fn index_for_stmt(&mut self, for_stmt: ForStmt<'db>, ordered: bool) -> NodeIndex {
        let mut latest_return_or_yield = 0;
        let (star_targets, star_expressions, block, else_block) = for_stmt.unpack();
        let latest = self.index_non_block_node(&star_targets, ordered);
        latest_return_or_yield = self.merge_latest_return_or_yield(latest_return_or_yield, latest);
        let latest = self.index_non_block_node(&star_expressions, ordered);
        latest_return_or_yield = self.merge_latest_return_or_yield(latest_return_or_yield, latest);

        self.references_need_flow_analysis = true;
        let latest = self.index_block(block, false);
        latest_return_or_yield = self.merge_latest_return_or_yield(latest_return_or_yield, latest);

        if ordered {
            self.index_unordered_references();
        }
        if let Some(else_block) = else_block {
            let latest = self.index_block(else_block.block(), ordered);
            latest_return_or_yield =
                self.merge_latest_return_or_yield(latest_return_or_yield, latest);
        }
        latest_return_or_yield
    }

    fn index_while_stmt(&mut self, while_stmt: WhileStmt<'db>, ordered: bool) -> NodeIndex {
        let mut latest_return_or_yield = 0;
        self.references_need_flow_analysis = true;
        let (condition, block, else_block) = while_stmt.unpack();
        let latest = self.index_non_block_node(&condition, ordered);
        latest_return_or_yield = self.merge_latest_return_or_yield(latest_return_or_yield, latest);
        let latest = self.index_block(block, false);
        latest_return_or_yield = self.merge_latest_return_or_yield(latest_return_or_yield, latest);
        if ordered {
            self.index_unordered_references();
        }
        if let Some(else_block) = else_block {
            // "else" ":" block
            let latest = self.index_block(else_block.block(), ordered);
            latest_return_or_yield =
                self.merge_latest_return_or_yield(latest_return_or_yield, latest);
        }
        latest_return_or_yield
    }

    fn index_with_stmt(&mut self, with_stmt: WithStmt<'db>, ordered: bool) -> NodeIndex {
        self.references_need_flow_analysis = true;
        let mut latest_return_or_yield = 0;
        let (with_items, block) = with_stmt.unpack();
        for with_item in with_items.iter() {
            let latest = self.index_non_block_node(&with_item, ordered);
            latest_return_or_yield =
                self.merge_latest_return_or_yield(latest_return_or_yield, latest);
        }
        let latest = self.index_block(block, ordered);
        self.merge_latest_return_or_yield(latest_return_or_yield, latest)
    }

    fn index_if_stmt(&mut self, if_stmt: IfStmt<'db>, ordered: bool) -> NodeIndex {
        self.references_need_flow_analysis = true;
        let mut latest_return_or_yield = 0;
        let mut block_iterator = if_stmt.iter_blocks();
        for if_block in block_iterator.by_ref() {
            let latest = match if_block {
                IfBlockType::If(expr, block) => {
                    let latest = self.index_non_block_node(&expr, ordered);
                    latest_return_or_yield =
                        self.merge_latest_return_or_yield(latest_return_or_yield, latest);
                    let set_block_specific = |if_block: IfBlockType, specific| {
                        self.db_infos.points.set(
                            if_block.first_leaf_index(),
                            Point::new_specific(specific, Locality::File),
                        )
                    };
                    match is_expr_reachable_for_name_binder(self.db_infos.flags, expr.expression())
                    {
                        Truthiness::True {
                            in_type_checking_block,
                        } => {
                            let latest = self.index_block(block, ordered);
                            self.merge_latest_return_or_yield(latest_return_or_yield, latest);
                            set_block_specific(
                                if_block,
                                if in_type_checking_block {
                                    Specific::IfBranchAlwaysReachableInTypeCheckingBlock
                                } else {
                                    Specific::IfBranchAlwaysReachableInNameBinder
                                },
                            );
                            for other_block in block_iterator {
                                set_block_specific(
                                    other_block,
                                    Specific::IfBranchAfterAlwaysReachableInNameBinder,
                                );
                            }
                            break;
                        }
                        Truthiness::False => {
                            set_block_specific(
                                if_block,
                                Specific::IfBranchAlwaysUnreachableInNameBinder,
                            );
                            0
                        }
                        Truthiness::Unknown => self.index_block(block, ordered),
                    }
                }
                IfBlockType::Else(else_block) => self.index_block(else_block.block(), ordered),
            };
            latest_return_or_yield =
                self.merge_latest_return_or_yield(latest_return_or_yield, latest);
        }
        latest_return_or_yield
    }

    fn index_try_stmt(&mut self, try_stmt: TryStmt<'db>, ordered: bool) -> NodeIndex {
        self.references_need_flow_analysis = true;
        let mut latest_return_or_yield = 0;
        for b in try_stmt.iter_blocks() {
            let latest = match b {
                TryBlockType::Try(block) => self.index_block(block, ordered),
                TryBlockType::Except(except) => {
                    let (except_expression, block) = except.unpack();
                    if let Some(except_expression) = except_expression {
                        self.index_except_expression_with_block(except_expression, block, ordered)
                    } else {
                        self.index_block(block, ordered)
                    }
                }
                TryBlockType::ExceptStar(except_star) => {
                    let (except_expression, block) = except_star.unpack();
                    self.index_except_expression_with_block(except_expression, block, ordered)
                }
                TryBlockType::Else(else_) => self.index_block(else_.block(), ordered),
                TryBlockType::Finally(finally) => self.index_block(finally.block(), ordered),
            };
            latest_return_or_yield =
                self.merge_latest_return_or_yield(latest_return_or_yield, latest);
        }
        latest_return_or_yield
    }

    fn index_except_expression_with_block(
        &mut self,
        except_expr: ExceptExpression<'db>,
        block: Block<'db>,
        ordered: bool,
    ) -> NodeIndex {
        let (expression, name_def) = except_expr.unpack();
        if let Some(name_def) = name_def {
            self.add_new_definition(name_def, Point::new_uncalculated())
        }
        let latest1 = self.index_non_block_node(&expression, ordered);
        let latest2 = self.index_block(block, ordered);
        self.merge_latest_return_or_yield(latest1, latest2)
    }

    fn index_class(&mut self, class_def: ClassDef<'db>, is_decorated: bool) {
        let (arguments, block) = class_def.unpack();
        if let Some(arguments) = arguments {
            self.index_non_block_node(&arguments, true);
        }
        let class_symbol_table =
            self.with_nested(NameBinderKind::Class, class_def.index(), |binder| {
                binder.index_block(block, true);
            });

        let abstract_attributes = self.search_abstract_method_likes(&class_symbol_table);
        self.unresolved_class_self_vars.push(UnresolvedClass {
            class_def,
            class_symbol_table,
            abstract_attributes,
            parent_scope: match self.kind {
                NameBinderKind::Global => ParentScope::Module,
                NameBinderKind::Class => ParentScope::Class(self.scope_node),
                NameBinderKind::Function { .. } => ParentScope::Function(self.scope_node),
                _ => unreachable!(),
            },
        });
        // Need to first index the class, because the class body does not have access to
        // the class name.
        self.add_new_definition(class_def.name_def(), Point::new_uncalculated());
    }

    fn index_self_vars(&mut self, class: ClassDef<'db>) -> SymbolTable {
        let mut symbol_table = SymbolTable::default();
        for (self_name, name) in class.search_potential_self_assignments() {
            if self.is_self_param(self_name) {
                if let Some(index) = symbol_table.lookup_symbol(name.as_code()) {
                    self.ensure_multi_definition(name.name_def().unwrap(), index)
                } else {
                    symbol_table.add_or_replace_symbol(name);
                }
            }
        }
        symbol_table
    }

    fn is_self_param(&self, name: Name<'db>) -> bool {
        let point = self.db_infos.points.get(name.index());
        if point.calculated() && point.kind() == PointKind::Redirect {
            let param_index = point.node_index();
            // Points to the name and not the name definition, therefore check that.
            // It should be safe to check the index before, because the name binder only ever
            // redirects to ame definitions.
            let param_point = self
                .db_infos
                .points
                .get(param_index - NAME_DEF_TO_NAME_DIFFERENCE);
            if param_point.calculated()
                && param_point.kind() == PointKind::Specific
                && param_point.specific() == Specific::MaybeSelfParam
            {
                return true;
            }
        }
        false
    }

    fn search_abstract_method_likes(&self, class_symbol_table: &SymbolTable) -> Box<[NodeIndex]> {
        let mut result = vec![];
        for (name, &node_index) in class_symbol_table.iter() {
            let function_index = node_index - NAME_TO_FUNCTION_DIFF;
            if let Some(func) = FunctionDef::maybe_by_index(self.db_infos.tree, function_index) {
                if let Some(decorated) = func.maybe_decorated() {
                    // We could use a more sophisticated logic for abstracmethod/abstractproperty,
                    // but it also seems kind of fine for now.
                    if decorated.decorators().iter().any(|d| {
                        matches!(
                            d.named_expression().as_code(),
                            "abstractmethod" | "abstractproperty"
                        )
                    }) {
                        // Check if it's already in the list
                        if !result
                            .iter()
                            .any(|&i| self.db_infos.tree.code_of_index(i) == name)
                        {
                            result.push(node_index)
                        }
                    }
                }
            }
        }
        result.sort();
        result.into()
    }

    fn index_match_stmt(&mut self, match_stmt: MatchStmt<'db>, ordered: bool) -> NodeIndex {
        debug!("TODO match_stmt name binding");
        0
    }

    fn index_non_block_node<T: InterestingNodeSearcher<'db>>(
        &mut self,
        node: &T,
        ordered: bool,
    ) -> NodeIndex {
        self.index_non_block_node_full(node, ordered, false)
    }

    fn index_annotation_expression(&mut self, node: &Expression<'db>) -> NodeIndex {
        self.index_non_block_node_full(node, true, true)
    }

    #[inline]
    fn index_non_block_node_full<T: InterestingNodeSearcher<'db>>(
        &mut self,
        node: &T,
        ordered: bool,
        from_annotation: bool,
    ) -> NodeIndex {
        let mut latest_return_or_yield = 0;
        for n in node.search_interesting_nodes() {
            let mut check_bool_op = |(left, right)| {
                self.index_non_block_node_full(&left, ordered, from_annotation);
                let old_value = self.references_need_flow_analysis;
                self.references_need_flow_analysis = true;
                self.index_non_block_node_full(&right, ordered, from_annotation);
                self.references_need_flow_analysis = old_value;
            };
            match n {
                InterestingNode::Name(name) => {
                    match name.parent() {
                        NameParent::Atom => {
                            if from_annotation {
                                self.annotation_names.push(name);
                            } else {
                                self.maybe_add_reference(name, ordered);
                            }
                        }
                        NameParent::NameDef(name_def) => {
                            match name_def.parent() {
                                NameDefParent::Other => {
                                    // The types are inferred later.
                                    self.add_new_definition(name_def, Point::new_uncalculated())
                                }
                                NameDefParent::GlobalStmt => {
                                    let name_index = name.index();
                                    let name_str = name_def.as_code();
                                    if let Some(local_index) =
                                        self.symbol_table.lookup_symbol(name_str)
                                    {
                                        if self.has_specific_in_multi_definitions(
                                            local_index,
                                            Specific::NonlocalVariable,
                                        ) {
                                            self.add_issue(
                                                name_index,
                                                IssueKind::NonlocalAndGlobal {
                                                    name: name_str.into(),
                                                },
                                            )
                                        } else {
                                            todo!()
                                        }
                                    } else {
                                        let p = if let Some(i) =
                                            self.lookup_in_global_scope(name_str)
                                        {
                                            Point::new_redirect(
                                                self.db_infos.file_index,
                                                i,
                                                Locality::File,
                                            )
                                        } else {
                                            Point::new_uncalculated()
                                        };
                                        self.db_infos.points.set(
                                            name_index - GLOBAL_NONLOCAL_TO_NAME_DIFFERENCE,
                                            p,
                                        );
                                        self.add_point_definition(
                                            name.name_def().unwrap(),
                                            Specific::GlobalVariable,
                                        );
                                    }
                                }
                                NameDefParent::NonlocalStmt => {
                                    if let Some(parent) = self.lookup_nonlocal_in_parent(name) {
                                        let name_str = name.as_code();
                                        // If there is no parent, an error was added
                                        if let Some(local_index) =
                                            self.symbol_table.lookup_symbol(name_str)
                                        {
                                            let issue = if self.has_specific_in_multi_definitions(
                                                local_index,
                                                Specific::GlobalVariable,
                                            ) {
                                                IssueKind::NonlocalAndGlobal {
                                                    name: name_str.into(),
                                                }
                                            } else {
                                                IssueKind::NameDefinedInLocalScopeBeforeNonlocal {
                                                    name: name_str.into(),
                                                }
                                            };
                                            self.add_issue(name.index(), issue)
                                        } else {
                                            self.add_point_definition(
                                                name.name_def().unwrap(),
                                                Specific::NonlocalVariable,
                                            );
                                            self.db_infos.points.set(
                                                name.index() - GLOBAL_NONLOCAL_TO_NAME_DIFFERENCE,
                                                Point::new_redirect(
                                                    self.db_infos.file_index,
                                                    parent,
                                                    Locality::File,
                                                ),
                                            );
                                        }
                                    }
                                }
                                NameDefParent::Primary => (),
                            }
                        }
                        _ => {
                            // All other names are not references or part of imports and should be
                            // resolved later.
                        }
                    }
                }
                InterestingNode::Conjunction(conjunction) => check_bool_op(conjunction.unpack()),
                InterestingNode::Disjunction(disjunction) => check_bool_op(disjunction.unpack()),
                InterestingNode::YieldExpr(n) => {
                    let is_yield_from = match n.unpack() {
                        YieldExprContent::StarExpressions(s) => {
                            self.index_non_block_node_full(&s, ordered, from_annotation);
                            false
                        }
                        YieldExprContent::YieldFrom(y) => {
                            self.index_non_block_node_full(&y, ordered, from_annotation);
                            true
                        }
                        YieldExprContent::None => false,
                    };
                    let keyword = match is_yield_from {
                        true => "yield from",
                        false => "yield",
                    };
                    match self.kind {
                        NameBinderKind::Function { is_async: true } if is_yield_from => {
                            self.add_issue(n.index(), IssueKind::YieldFromInAsyncFunction)
                        }
                        NameBinderKind::Function { .. } => (),
                        NameBinderKind::Comprehension => self.add_issue(
                            n.index(),
                            IssueKind::YieldOrYieldFromInsideComprehension { keyword },
                        ),
                        _ => self.add_issue(n.index(), IssueKind::StmtOutsideFunction { keyword }),
                    }
                    self.index_return_or_yield(&mut latest_return_or_yield, n.index());
                }
                InterestingNode::Lambda(lambda) => {
                    self.index_lambda_param_defaults(lambda, ordered);
                    self.unresolved_nodes.push(Unresolved::Lambda(lambda));
                }
                InterestingNode::Comprehension(comp) => {
                    // Index the first expression of a comprehension, which is always executed
                    // in the current scope.
                    self.references_need_flow_analysis = true;
                    if comp.is_generator() {
                        self.unresolved_nodes.push(Unresolved::Comprehension(comp));
                    } else {
                        self.index_comprehension(comp, ordered);
                    }
                }
                InterestingNode::DictComprehension(comp) => {
                    self.references_need_flow_analysis = true;
                    self.index_dict_comprehension(comp, ordered);
                }
                InterestingNode::Ternary(ternary) => {
                    let (if_, condition, else_) = ternary.unpack();
                    self.index_non_block_node_full(&condition, ordered, from_annotation);
                    self.references_need_flow_analysis = true;
                    self.index_non_block_node_full(&if_, ordered, from_annotation);
                    self.index_non_block_node_full(&else_, ordered, from_annotation);
                }
                InterestingNode::Walrus(walrus) => {
                    let (name_def, expr) = walrus.unpack();
                    self.index_non_block_node_full(&expr, ordered, from_annotation);
                    self.add_new_walrus_definition(name_def)
                }
            }
        }
        latest_return_or_yield
    }

    fn index_return_or_yield(&self, latest_return_or_yield: &mut NodeIndex, node_index: NodeIndex) {
        let keyword_index = node_index + 1;
        self.db_infos.points.set(
            keyword_index,
            Point::new_node_analysis_with_node_index(Locality::File, *latest_return_or_yield),
        );
        *latest_return_or_yield = keyword_index
    }

    fn index_comprehension(&mut self, comp: Comprehension<'db>, ordered: bool) {
        // TODO the ordered argument is not used here currently and it should probably be used.
        let (named_expr, for_if_clauses) = comp.unpack();
        let mut clauses = for_if_clauses.iter();
        self.index_comprehension_clause(&clauses.next().unwrap(), &mut clauses, |binder| {
            binder.index_non_block_node(&named_expr, true);
        })
    }

    fn index_dict_comprehension(&mut self, comp: DictComprehension<'db>, ordered: bool) {
        let (key_value, for_if_clauses) = comp.unpack();
        let mut clauses = for_if_clauses.iter();
        self.index_comprehension_clause(&clauses.next().unwrap(), &mut clauses, |binder| {
            binder.index_non_block_node(&key_value, true);
        })
    }

    fn index_comprehension_clause(
        &mut self,
        clause: &ForIfClause<'db>,
        clauses: &mut ForIfClauseIterator<'db>,
        on_expr: impl FnOnce(&mut NameBinder<'db>),
    ) {
        let (targets, ifs) = match clause {
            ForIfClause::Sync(sync_for_if_clause) | ForIfClause::Async(sync_for_if_clause) => {
                let (targets, from, ifs) = sync_for_if_clause.unpack();
                self.index_non_block_node(&from, true);
                (targets, ifs)
            }
        };
        // TODO this is not exactly correct for named expressions and their scopes.
        self.with_nested(NameBinderKind::Comprehension, clause.index(), |binder| {
            binder.index_non_block_node(&targets, true);
            for if_ in ifs {
                binder.index_non_block_node(&if_, true);
            }

            if let Some(clause) = clauses.next() {
                binder.index_comprehension_clause(&clause, clauses, on_expr);
            } else {
                on_expr(binder)
            }
        });
    }

    fn lookup_in_global_scope(&self, name: &str) -> Option<NodeIndex> {
        if let Some(parent) = self.parent {
            unsafe { &*parent }.lookup_in_global_scope(name)
        } else {
            self.symbol_table.lookup_symbol(name)
        }
    }

    fn lookup_nonlocal_in_parent(&self, name: Name) -> Option<NodeIndex> {
        if let Some(parent) = self.parent {
            let parent = unsafe { &*parent };
            let name_str = name.as_code();
            let result = parent.symbol_table.lookup_symbol(name_str);
            if result.is_none() || !matches!(parent.kind, NameBinderKind::Function { .. }) {
                self.add_issue(
                    name.index(),
                    IssueKind::NonlocalNoBindingFound {
                        name: name_str.into(),
                    },
                );
            }
            result
        } else {
            self.add_issue(name.index(), IssueKind::NonlocalAtModuleLevel);
            None
        }
    }

    fn has_specific_in_multi_definitions(&self, name_index: NodeIndex, search: Specific) -> bool {
        let p = self.db_infos.points.get(name_index);
        if p.calculated() && p.specific() == Specific::NameOfNameDef {
            MultiDefinitionIterator::new(self.db_infos.points, name_index).any(|index| {
                self.db_infos
                    .points
                    .get(index)
                    .maybe_calculated_and_specific()
                    .is_some_and(|specific| {
                        todo!("This case is currently not reached, but probably necessary")
                    })
            })
        } else {
            self.db_infos
                .points
                .get(name_index - NAME_DEF_TO_NAME_DIFFERENCE)
                .maybe_calculated_and_specific()
                .is_some_and(|specific| specific == search)
        }
    }

    fn index_function_name_and_param_defaults(
        &mut self,
        func: FunctionDef<'db>,
        ordered: bool,
        is_decorated: bool,
        is_async: bool,
    ) {
        // If there is no parent, this does not have to be resolved immediately in theory, but for
        // now we just do.
        self.unresolved_nodes.push(Unresolved::FunctionDef {
            func,
            is_method: self.kind == NameBinderKind::Class,
            is_async,
        });

        let (name_def, params, return_annotation, _) = func.unpack();
        for param in params.iter() {
            // expressions are resolved immediately while annotations are inferred at the
            // end of a module.
            if let Some(param_annotation) = param.annotation() {
                match param_annotation.maybe_starred() {
                    Ok(starred) => self.index_non_block_node_full(&starred, true, true),
                    Err(expr) => self.index_annotation_expression(&expr),
                };
            }
            if let Some(expression) = param.default() {
                self.index_non_block_node(&expression, ordered);
            }
        }
        if let Some(return_annotation) = return_annotation {
            // This is the -> annotation
            self.index_annotation_expression(&return_annotation.expression());
        }

        self.add_new_definition(name_def, Point::new_uncalculated());
    }

    pub(crate) fn index_function_body(&mut self, func: FunctionDef<'db>, is_method: bool) {
        // Function name was indexed already.
        let (_, params, _, block) = func.unpack();

        self.index_param_name_defs(params.iter().map(|param| param.name_def()), is_method);

        let latest_return_index = self.index_block(block, true);
        // It's kind of hard to know where to store the latest reference statement.
        self.db_infos.points.set(
            func.index() + 1,
            Point::new_node_analysis_with_node_index(
                Locality::ClassOrFunction,
                latest_return_index,
            ),
        );
    }

    fn index_param_name_defs(
        &mut self,
        mut names: impl Iterator<Item = NameDef<'db>>,
        is_method: bool,
    ) {
        if is_method {
            if let Some(name_def) = names.next() {
                self.add_point_definition(name_def, Specific::MaybeSelfParam);
            }
        }
        for name_def in names {
            self.add_point_definition(name_def, Specific::Param);
        }
    }

    fn index_lambda_param_defaults(&mut self, lambda: Lambda<'db>, ordered: bool) {
        // lambda: "lambda" [lambda_parameters] ":" expression
        for param in lambda.params() {
            if let Some(default) = param.default() {
                self.index_non_block_node(&default, ordered);
            }
        }
    }

    fn index_lambda(&mut self, lambda: Lambda<'db>) {
        let (params, expr) = lambda.unpack();
        self.index_param_name_defs(params.map(|param| param.name_def()), false);
        self.index_non_block_node(&expr, true);
    }

    #[inline]
    fn maybe_add_reference(&mut self, name: Name<'db>, ordered: bool) {
        if !self.try_to_process_reference(name) {
            if !ordered || self.kind != NameBinderKind::Class {
                self.unordered_references
                    .push(UnorderedReference { name, ordered });
            } else {
                self.names_to_be_resolved_in_parent.push(name);
            }
        }
    }

    #[inline]
    fn try_to_process_reference(&mut self, name: Name<'db>) -> bool {
        try_to_process_reference_for_symbol_table(
            &mut self.symbol_table,
            self.db_infos.file_index,
            self.db_infos.points,
            name,
            self.references_need_flow_analysis,
        )
    }

    fn index_unordered_references(&mut self) {
        for unordered_reference in &self.unordered_references {
            if try_to_process_reference_for_symbol_table(
                &mut self.symbol_table,
                self.db_infos.file_index,
                self.db_infos.points,
                unordered_reference.name,
                self.references_need_flow_analysis,
            ) {
                if unordered_reference.ordered && !self.db_infos.is_stub {
                    self.add_issue(
                        unordered_reference.name.index(),
                        IssueKind::NameUsedBeforeDefinition {
                            name: unordered_reference.name.as_code().into(),
                        },
                    );
                }
            } else {
                self.names_to_be_resolved_in_parent
                    .push(unordered_reference.name);
            }
        }
        self.unordered_references.truncate(0);
    }
}

fn gather_slots(file_index: FileIndex, assignment: Assignment) -> Option<Box<[StringSlice]>> {
    let right_side = match assignment.unpack() {
        AssignmentContent::Normal(targets, right_side) => {
            if targets.count() > 1 {
                // Apparently multi assignments are currently invalid.
                return None;
            }
            right_side
        }
        AssignmentContent::WithAnnotation(_, _, right_side) => right_side?,
        AssignmentContent::AugAssign(..) => return None,
    };
    let AssignmentRightSide::StarExpressions(star_exprs) = right_side else {
        return None;
    };
    let maybe_str = |expr: Expression| StringSlice::from_string_in_expression(file_index, expr);
    let check_expressions = |expressions| {
        let mut slots = vec![];
        for element in expressions {
            let expr = match element {
                StarLikeExpression::Expression(expr) => expr,
                StarLikeExpression::NamedExpression(n) => n.expression(),
                StarLikeExpression::StarNamedExpression(_)
                | StarLikeExpression::StarExpression(_) => return None,
            };
            slots.push(maybe_str(expr)?);
        }
        Some(slots.into())
    };
    match star_exprs.unpack() {
        StarExpressionContent::Expression(expr) => {
            if let ExpressionContent::ExpressionPart(ExpressionPart::Atom(atom)) = expr.unpack() {
                match atom.unpack() {
                    AtomContent::Dict(dict) => {
                        let mut slots = vec![];
                        for dict_element in dict.iter_elements() {
                            match dict_element {
                                DictElement::KeyValue(key_value) => {
                                    slots.push(maybe_str(key_value.key())?);
                                }
                                DictElement::Star(_) => return None,
                            }
                        }
                        Some(slots.into())
                    }
                    AtomContent::Tuple(set) => check_expressions(set.iter()),
                    AtomContent::List(list) => check_expressions(list.unpack()),
                    AtomContent::Set(tuple) => check_expressions(tuple.unpack()),
                    AtomContent::Strings(s) => Some(Box::new([maybe_str(expr)?])),
                    // Invalid __slots__ will be checked elsewhere.
                    _ => None,
                }
            } else {
                None
            }
        }
        StarExpressionContent::Tuple(tup) => {
            let mut slots = vec![];
            for element in tup.iter() {
                let expr = match element {
                    StarLikeExpression::Expression(expr) => expr,
                    StarLikeExpression::NamedExpression(n) => n.expression(),
                    StarLikeExpression::StarNamedExpression(_)
                    | StarLikeExpression::StarExpression(_) => return None,
                };
                slots.push(maybe_str(expr)?);
            }
            Some(slots.into())
        }
        StarExpressionContent::StarExpression(_) => None,
    }
}

#[inline]
fn try_to_process_reference_for_symbol_table(
    symbol_table: &mut SymbolTable,
    file_index: FileIndex,
    points: &Points,
    name: Name,
    needs_flow_analysis: bool,
) -> bool {
    let point = {
        if let Some(definition) = symbol_table.lookup_symbol(name.as_str()) {
            Point::new_redirect(file_index, definition, Locality::File)
                .with_needs_flow_analysis(needs_flow_analysis)
        } else {
            return false;
        }
    };
    points.set(name.index(), point);
    true
}

#[derive(PartialEq, Debug)]
pub enum Truthiness {
    True { in_type_checking_block: bool }, // in_type_checking_block for `if TYPE_CHECKING:`
    False,
    Unknown,
}

impl From<bool> for Truthiness {
    fn from(item: bool) -> Self {
        match item {
            false => Truthiness::False,
            true => Truthiness::True {
                in_type_checking_block: false,
            },
        }
    }
}

impl std::ops::BitAnd for Truthiness {
    type Output = Self;
    fn bitand(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (
                Self::True {
                    in_type_checking_block: in_type_checking_block1,
                },
                Self::True {
                    in_type_checking_block: in_type_checking_block2,
                },
            ) => Self::True {
                in_type_checking_block: in_type_checking_block1 && in_type_checking_block2,
            },
            (Self::Unknown, _) | (_, Self::Unknown) => Self::Unknown,
            _ => Self::False,
        }
    }
}

impl Truthiness {
    fn invert(self) -> Truthiness {
        match self {
            Self::True { .. } => Self::False,
            Self::False => Self::True {
                in_type_checking_block: false,
            },
            Self::Unknown => Self::Unknown,
        }
    }
    fn or_else(self, callback: impl FnOnce() -> Truthiness) -> Truthiness {
        match self {
            Self::False => callback(),
            Self::Unknown => {
                let truthy = callback();
                if matches!(truthy, Self::True { .. }) {
                    truthy
                } else {
                    self
                }
            }
            _ => self,
        }
    }
}

fn check_comparison_reachability(
    flags: &TypeCheckerFlags,
    comp: ComparisonContent,
    check: ExpressionPart,
    other: ExpressionPart,
) -> Truthiness {
    if let ExpressionPart::Primary(primary) = check {
        if maybe_sys_name(primary, "platform")
            && matches!(
                comp,
                ComparisonContent::Equals(..) | ComparisonContent::NotEquals(..)
            )
        {
            if let ExpressionPart::Atom(a) = other {
                if let Some(s) = a.unpack().maybe_single_string_literal() {
                    if let Some(to_compare) = s.as_python_string().as_str() {
                        let mut result = to_compare == flags.computed_platform();
                        if matches!(comp, ComparisonContent::NotEquals(..)) {
                            result = !result;
                        }
                        if result {
                            return Truthiness::True {
                                in_type_checking_block: false,
                            };
                        } else {
                            return Truthiness::False;
                        }
                    }
                }
            }
        }

        if maybe_sys_name(primary, "version_info") {
            return python_version_matches_tuple(flags, comp, other, 0);
        }
        if let PrimaryContent::GetItem(slice_type) = primary.second() {
            if let PrimaryOrAtom::Primary(first) = primary.first() {
                if maybe_sys_name(first, "version_info") {
                    return python_version_matches_slice(flags, comp, slice_type, other);
                }
            }
        }
    }
    Truthiness::Unknown
}

fn python_version_matches_tuple(
    flags: &TypeCheckerFlags,
    comp: ComparisonContent,
    other: ExpressionPart,
    from: usize,
) -> Truthiness {
    let Some(AtomContent::Tuple(tup)) = other.maybe_unpacked_atom() else {
        return Truthiness::Unknown;
    };
    if tup.iter().count() + from > 2 {
        // (major, minor, bugfix) is currently not supported
        return Truthiness::Unknown;
    }
    for (current, tup_entry) in [flags.python_version.major, flags.python_version.minor][from..]
        .iter()
        .zip(tup.iter())
    {
        let expr = match tup_entry {
            StarLikeExpression::Expression(expr) => expr,
            StarLikeExpression::NamedExpression(n) => n.expression(),
            _ => return Truthiness::Unknown,
        };
        let Some(AtomContent::Int(n)) = expr.maybe_unpacked_atom() else {
            return Truthiness::Unknown;
        };
        if let Some(n_in_tup) = n
            .parse()
            .and_then(|i| <i64 as TryInto<usize>>::try_into(i).ok())
        {
            if let Some(result) = comp.compare_with_operand(*current, n_in_tup) {
                if !result {
                    return Truthiness::False;
                }
            } else {
                return Truthiness::Unknown;
            }
        } else {
            return Truthiness::Unknown;
        }
    }
    Truthiness::True {
        in_type_checking_block: false,
    }
}

fn python_version_matches_slice(
    flags: &TypeCheckerFlags,
    comp: ComparisonContent,
    slice_type: SliceType,
    other: ExpressionPart,
) -> Truthiness {
    match slice_type {
        SliceType::Slice(slice) => {
            let (first, second, third) = slice.unpack();
            if third.is_none() {
                let from = first.map(|expr| expr.maybe_simple_int());
                if from != Some(None) {
                    return python_version_matches_tuple(
                        flags,
                        comp,
                        other,
                        from.flatten().unwrap_or(0),
                    );
                }
            }
        }
        SliceType::NamedExpression(ne) => {
            if let Some(AtomContent::Int(nth)) = ne.expression().maybe_unpacked_atom() {
                if let Some(AtomContent::Int(wanted)) = other.maybe_unpacked_atom() {
                    if nth.parse() == Some(0) {
                        if let Some(result) = wanted
                            .parse_as_usize()
                            .and_then(|x| comp.compare_with_operand(flags.python_version.major, x))
                        {
                            return result.into();
                        }
                    }
                }
            }
        }
        _ => (),
    }
    Truthiness::Unknown
}

fn maybe_sys_name(primary: Primary, name: &str) -> bool {
    if let PrimaryContent::Attribute(attr) = primary.second() {
        attr.as_code() == name && primary.first().as_code() == "sys"
    } else {
        false
    }
}

fn maybe_sys_platform_startswith(
    flags: &TypeCheckerFlags,
    before: Primary,
    arguments: ArgumentsDetails,
) -> Truthiness {
    if let PrimaryContent::Attribute(attr) = before.second() {
        if let PrimaryOrAtom::Primary(prim) = before.first() {
            if attr.as_code() == "startswith" && maybe_sys_name(prim, "platform") {
                if let Some(named_expr) = arguments.maybe_single_named_expr() {
                    if let Some(s) = named_expr.maybe_single_string_literal() {
                        if let Some(to_compare) = s.as_python_string().as_str() {
                            if flags.computed_platform().starts_with(to_compare) {
                                return Truthiness::True {
                                    in_type_checking_block: false,
                                };
                            } else {
                                return Truthiness::False;
                            }
                        }
                    }
                }
            }
        }
    }
    Truthiness::Unknown
}

fn is_expr_reachable_for_name_binder(flags: &TypeCheckerFlags, expr: Expression) -> Truthiness {
    match expr.unpack() {
        ExpressionContent::ExpressionPart(p) => is_expr_part_reachable_for_name_binder(flags, p),
        _ => Truthiness::Unknown,
    }
}

pub fn is_expr_part_reachable_for_name_binder(
    flags: &TypeCheckerFlags,
    expr_part: ExpressionPart,
) -> Truthiness {
    match expr_part {
        ExpressionPart::Atom(atom) => match atom.unpack() {
            AtomContent::Name(name) => {
                let n = name.as_code();
                if ["MYPY", "TYPE_CHECKING"].contains(&n) {
                    return Truthiness::True {
                        in_type_checking_block: true,
                    };
                } else if "PY3" == n || flags.always_true_symbols.iter().any(|s| s == n) {
                    return Truthiness::True {
                        in_type_checking_block: false,
                    };
                } else if n == "PY2" || flags.always_false_symbols.iter().any(|s| s == n) {
                    return Truthiness::False;
                }
            }
            AtomContent::NamedExpression(named_expr) => {
                return is_expr_reachable_for_name_binder(flags, named_expr.expression())
            }
            _ => (),
        },
        ExpressionPart::Primary(primary) => match primary.second() {
            PrimaryContent::Attribute(second) => {
                let second = second.as_code();
                if second == "TYPE_CHECKING" {
                    if let PrimaryOrAtom::Atom(atom) = primary.first() {
                        if atom.as_code() == "typing" {
                            return Truthiness::True {
                                in_type_checking_block: true,
                            };
                        }
                    }
                }
            }
            PrimaryContent::Execution(execution) => {
                if let PrimaryOrAtom::Primary(prim) = primary.first() {
                    return maybe_sys_platform_startswith(flags, prim, execution);
                }
            }
            _ => (),
        },
        ExpressionPart::Inversion(inv) => {
            return is_expr_part_reachable_for_name_binder(flags, inv.expression()).invert()
        }
        ExpressionPart::Comparisons(comps) => {
            let mut iterator = comps.iter();
            let first = iterator.next().unwrap();
            if iterator.next().is_none() {
                let left = first.left();
                let right = first.right();
                let result = check_comparison_reachability(flags, first, left, right);
                if result == Truthiness::Unknown {
                    return check_comparison_reachability(flags, first, right, left);
                }
                return result;
            }
        }
        ExpressionPart::Conjunction(conjunction) => {
            let (left, right) = conjunction.unpack();
            return is_expr_part_reachable_for_name_binder(flags, left)
                & is_expr_part_reachable_for_name_binder(flags, right);
        }
        ExpressionPart::Disjunction(disjunction) => {
            let (left, right) = disjunction.unpack();
            return is_expr_part_reachable_for_name_binder(flags, left)
                .or_else(|| is_expr_part_reachable_for_name_binder(flags, right));
        }
        _ => (),
    }
    Truthiness::Unknown
}

struct UnorderedReference<'db> {
    name: Name<'db>,
    ordered: bool,
}
