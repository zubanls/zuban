use crate::database::{
    ClassStorage, ComplexPoint, FileIndex, FunctionType, Locality, Overload, Point, PointLink,
    PointType, Points, Specific,
};
use crate::file::ComplexValues;
use crate::utils::SymbolTable;
use parsa_python_ast::{
    AsyncStmtContent, AtomContent, Block, BlockContent, ClassDef, CommonComprehensionExpression,
    Comprehension, Decoratee, Decorators, DictComprehension, Expression, ExpressionContent,
    ExpressionPart, File, ForIfClause, ForIfClauseIterator, ForStmt, FunctionDef, IfBlockType,
    IfStmt, InterestingNode, InterestingNodeSearcher, Lambda, MatchStmt, Name, NameDefinition,
    NameParent, NodeIndex, StmtContent, StmtIterator, Tree, TryBlockType, TryStmt, WhileStmt,
    WithStmt,
};

pub enum NameBinderType {
    Global,
    Function,
    Class,
    Lambda,
    Comprehension,
}

enum Unresolved<'db> {
    FunctionDef(FunctionDef<'db>),
    Lambda(Lambda<'db>),
    Expression(Expression<'db>),
    Comprehension(Comprehension<'db>),
    DictComprehension(DictComprehension<'db>),
    Name(Name<'db>),
}

pub struct NameBinder<'db, 'a> {
    tree: &'db Tree,
    type_: NameBinderType,
    symbol_table: &'a SymbolTable,
    points: &'db Points,
    complex_points: &'db ComplexValues,
    unordered_references: Vec<Name<'db>>,
    unresolved_nodes: Vec<Unresolved<'db>>,
    unresolved_names: Vec<Name<'db>>,
    file_index: FileIndex,
    parent_lookup_not_finished: bool,
    parent: Option<&'a NameBinder<'db, 'a>>,
}

impl<'db, 'a> NameBinder<'db, 'a> {
    fn new(
        tree: &'db Tree,
        type_: NameBinderType,
        symbol_table: &'a SymbolTable,
        points: &'db Points,
        complex_points: &'db ComplexValues,
        file_index: FileIndex,
        parent: Option<&'a Self>,
    ) -> Self {
        Self {
            tree,
            type_,
            symbol_table,
            points,
            complex_points,
            unordered_references: vec![],
            unresolved_nodes: vec![],
            unresolved_names: vec![],
            file_index,
            parent_lookup_not_finished: false,
            parent,
        }
    }

    pub fn with_global_binder(
        tree: &'db Tree,
        symbol_table: &'a SymbolTable,
        points: &'db Points,
        complex_points: &'db ComplexValues,
        file_index: FileIndex,
        func: impl FnOnce(&mut NameBinder<'db, 'db>),
    ) where
        'a: 'db,
    {
        let mut binder = NameBinder::new(
            tree,
            NameBinderType::Global,
            symbol_table,
            points,
            complex_points,
            file_index,
            None,
        );
        func(&mut binder);
        binder.close();
    }

    pub fn with_nested(
        &mut self,
        type_: NameBinderType,
        symbol_table: &'_ SymbolTable,
        mut func: impl FnMut(&mut NameBinder<'db, '_>),
    ) {
        let mut name_binder = NameBinder::new(
            self.tree,
            type_,
            symbol_table,
            self.points,
            self.complex_points,
            self.file_index,
            Some(self),
        );
        func(&mut name_binder);
        name_binder.close();
        let unresolved_names = name_binder.unresolved_names;
        self.unresolved_nodes
            .extend(unresolved_names.into_iter().map(Unresolved::Name));
    }

    fn add_new_definition(
        &self,
        name_def: NameDefinition<'db>,
        mut point: Point,
        in_base_scope: bool,
    ) {
        let name = name_def.name();
        let replaced = self.symbol_table.add_or_replace_symbol(name);
        if !in_base_scope {
            if let Some(replaced) = replaced {
                self.points.set(name_def.index(), point);
                point = Point::new_multi_definition(replaced, Locality::File);
            }
        }
        self.points.set(name.index(), point);
    }

    fn add_point_definition(
        &mut self,
        name_def: NameDefinition<'db>,
        type_: Specific,
        in_base_scope: bool,
    ) {
        self.add_new_definition(
            name_def,
            Point::new_simple_specific(type_, Locality::Stmt),
            in_base_scope,
        );
    }

    fn add_redirect_definition(
        &mut self,
        name_def: NameDefinition<'db>,
        node_index: NodeIndex,
        in_base_scope: bool,
    ) {
        self.add_new_definition(
            name_def,
            Point::new_redirect(self.file_index, node_index, Locality::Stmt),
            in_base_scope,
        );
    }

    pub fn index_file(&mut self, file_node: File<'db>) {
        self.index_stmts(file_node.iter_stmts(), true, true);
    }

    fn index_block(&mut self, block: Block<'db>, ordered: bool, in_base_scope: bool) -> NodeIndex {
        // Returns the latest return/yield index
        // Theory:
        // - while_stmt, for_stmt: ignore order (at least mostly)
        // - match_stmt, if_stmt, try_stmt (only in coresponding blocks and after)
        // - sync_for_if_clause: reversed order and only in scope
        // - lambda: only in scope
        // - function_def, class_def: ignore
        match block.unpack() {
            BlockContent::OneLine(simple) => {
                self.index_non_block_node(&simple, ordered, in_base_scope)
            }
            BlockContent::Indented(stmts) => self.index_stmts(stmts, ordered, in_base_scope),
        }
    }

    fn index_stmts(
        &mut self,
        stmts: StmtIterator<'db>,
        ordered: bool,
        in_base_scope: bool,
    ) -> NodeIndex {
        let mut latest_return_or_yield = 0;
        for stmt in stmts {
            let return_or_yield = match stmt.unpack() {
                StmtContent::SimpleStmts(simple) => {
                    self.index_non_block_node(&simple, ordered, in_base_scope)
                }
                StmtContent::FunctionDef(func) => {
                    self.index_function_name_and_param_defaults(
                        func,
                        ordered,
                        in_base_scope,
                        None,  // decorators
                        false, // is_async
                    );
                    0
                }
                StmtContent::ClassDef(class) => {
                    self.index_class(class, false, in_base_scope);
                    0
                }
                StmtContent::Decorated(decorated) => {
                    match decorated.decoratee() {
                        Decoratee::FunctionDef(func) => {
                            self.index_function_name_and_param_defaults(
                                func,
                                ordered,
                                in_base_scope,
                                Some(decorated.decorators()),
                                false, // is_async
                            );
                        }
                        Decoratee::AsyncFunctionDef(func) => {
                            self.index_function_name_and_param_defaults(
                                func,
                                ordered,
                                in_base_scope,
                                Some(decorated.decorators()),
                                true, // is_async
                            );
                        }
                        Decoratee::ClassDef(cls) => {
                            self.index_class(cls, true, in_base_scope);
                        }
                    }
                    0
                }
                StmtContent::IfStmt(if_stmt) => self.index_if_stmt(if_stmt, ordered),
                StmtContent::ForStmt(for_stmt) => self.index_for_stmt(for_stmt, ordered),
                StmtContent::TryStmt(try_stmt) => self.index_try_stmt(try_stmt, ordered),
                StmtContent::WhileStmt(while_stmt) => self.index_while_stmt(while_stmt, ordered),
                StmtContent::WithStmt(with_stmt) => self.index_with_stmt(with_stmt, ordered),
                StmtContent::MatchStmt(match_stmt) => self.index_match_stmt(match_stmt, ordered),
                StmtContent::AsyncStmt(async_stmt) => match async_stmt.unpack() {
                    AsyncStmtContent::FunctionDef(function_def) => {
                        self.index_function_name_and_param_defaults(
                            function_def,
                            ordered,
                            in_base_scope,
                            None, // decorators
                            true,
                        );
                        0
                    }
                    AsyncStmtContent::ForStmt(for_stmt) => self.index_for_stmt(for_stmt, ordered),
                    AsyncStmtContent::WithStmt(with_stmt) => {
                        self.index_with_stmt(with_stmt, ordered)
                    }
                },
                StmtContent::Newline => 0,
            };
            latest_return_or_yield =
                self.merge_latest_return_or_yield(latest_return_or_yield, return_or_yield);
        }
        latest_return_or_yield
    }

    fn merge_latest_return_or_yield(&self, first: NodeIndex, mut second: NodeIndex) -> NodeIndex {
        if first != 0 && second != 0 {
            loop {
                let point = self.points.get(second);
                let node_index = point.node_index();
                if node_index == 0 {
                    // Now that we have the first node in the chain of the second nodes, link that
                    // to the first one (like a linked list)
                    self.points.set(
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
        self.index_unordered_references();

        self.parent_lookup_not_finished = true;
        while let Some(n) = self.unresolved_nodes.pop() {
            match n {
                Unresolved::Name(name) => self.maybe_add_reference(name, true),
                Unresolved::Expression(expr) => {
                    self.index_non_block_node(&expr, true, false);
                }
                Unresolved::FunctionDef(func) => {
                    let symbol_table = SymbolTable::default();
                    self.with_nested(NameBinderType::Function, &symbol_table, |binder| {
                        binder.index_function_body(func)
                    });
                }
                Unresolved::Lambda(lambda) => {
                    let symbol_table = SymbolTable::default();
                    self.with_nested(NameBinderType::Lambda, &symbol_table, |binder| {
                        binder.index_lambda(lambda)
                    });
                }
                Unresolved::Comprehension(comp) => self.index_comprehension(comp, true),
                Unresolved::DictComprehension(comp) => self.index_dict_comprehension(comp, true),
            };
        }
        debug_assert_eq!(self.unordered_references.len(), 0);
    }

    fn index_for_stmt(&mut self, for_stmt: ForStmt<'db>, ordered: bool) -> NodeIndex {
        let mut latest_return_or_yield = 0;
        let (star_targets, star_expressions, block, else_block) = for_stmt.unpack();
        let latest = self.index_non_block_node(&star_targets, ordered, false);
        latest_return_or_yield = self.merge_latest_return_or_yield(latest_return_or_yield, latest);
        let latest = self.index_non_block_node(&star_expressions, ordered, false);
        latest_return_or_yield = self.merge_latest_return_or_yield(latest_return_or_yield, latest);

        let latest = self.index_block(block, false, false);
        latest_return_or_yield = self.merge_latest_return_or_yield(latest_return_or_yield, latest);

        if ordered {
            self.index_unordered_references();
        }
        if let Some(else_block) = else_block {
            let latest = self.index_block(else_block.block(), ordered, false);
            latest_return_or_yield =
                self.merge_latest_return_or_yield(latest_return_or_yield, latest);
        }
        latest_return_or_yield
    }

    fn index_while_stmt(&mut self, while_stmt: WhileStmt<'db>, ordered: bool) -> NodeIndex {
        let mut latest_return_or_yield = 0;
        let (condition, block, else_block) = while_stmt.unpack();
        let latest = self.index_non_block_node(&condition, ordered, false);
        latest_return_or_yield = self.merge_latest_return_or_yield(latest_return_or_yield, latest);
        let latest = self.index_block(block, false, false);
        latest_return_or_yield = self.merge_latest_return_or_yield(latest_return_or_yield, latest);
        if ordered {
            self.index_unordered_references();
        }
        if let Some(else_block) = else_block {
            // "else" ":" block
            let latest = self.index_block(else_block.block(), ordered, false);
            latest_return_or_yield =
                self.merge_latest_return_or_yield(latest_return_or_yield, latest);
        }
        latest_return_or_yield
    }

    fn index_with_stmt(&mut self, with_stmt: WithStmt<'db>, ordered: bool) -> NodeIndex {
        let mut latest_return_or_yield = 0;
        let (with_items, block) = with_stmt.unpack();
        for with_item in with_items.iter() {
            let (expr, star_target) = with_item.unpack();
            let latest = self.index_non_block_node(&expr, ordered, false);
            latest_return_or_yield =
                self.merge_latest_return_or_yield(latest_return_or_yield, latest);
            if let Some(star_target) = star_target {
                let latest = self.index_non_block_node(&star_target, ordered, false);
            }
            latest_return_or_yield =
                self.merge_latest_return_or_yield(latest_return_or_yield, latest);
        }
        let latest = self.index_block(block, ordered, false);
        self.merge_latest_return_or_yield(latest_return_or_yield, latest)
    }

    fn index_if_stmt(&mut self, if_stmt: IfStmt<'db>, ordered: bool) -> NodeIndex {
        let mut latest_return_or_yield = 0;
        for if_block in if_stmt.iter_blocks() {
            let latest = match if_block {
                IfBlockType::If(expr, block) => {
                    let latest = self.index_non_block_node(&expr, ordered, false);
                    latest_return_or_yield =
                        self.merge_latest_return_or_yield(latest_return_or_yield, latest);
                    self.index_block(block, ordered, false)
                }
                IfBlockType::Else(block) => self.index_block(block, ordered, false),
            };
            latest_return_or_yield =
                self.merge_latest_return_or_yield(latest_return_or_yield, latest);
        }
        latest_return_or_yield
    }

    fn index_try_stmt(&mut self, try_stmt: TryStmt<'db>, ordered: bool) -> NodeIndex {
        let mut latest_return_or_yield = 0;
        for b in try_stmt.iter_blocks() {
            let latest = match b {
                TryBlockType::Try(block) => self.index_block(block, ordered, false),
                TryBlockType::Except(except) => {
                    let (expression, name_def, block) = except.unpack();
                    let latest = self.index_non_block_node(&expression, ordered, false);
                    latest_return_or_yield =
                        self.merge_latest_return_or_yield(latest_return_or_yield, latest);
                    if let Some(name_def) = name_def {
                        self.add_redirect_definition(name_def, expression.index() as u32, false);
                    }
                    self.index_block(block, ordered, false)
                }
                TryBlockType::Else(else_) => self.index_block(else_.block(), ordered, false),
                TryBlockType::Finally(finally) => self.index_block(finally.block(), ordered, false),
            };
            latest_return_or_yield =
                self.merge_latest_return_or_yield(latest_return_or_yield, latest);
        }
        latest_return_or_yield
    }

    fn index_class(&mut self, class: ClassDef<'db>, is_decorated: bool, in_base_scope: bool) {
        let symbol_table = SymbolTable::default();
        self.with_nested(NameBinderType::Class, &symbol_table, |binder| {
            let (arguments, block) = class.unpack();
            if let Some(arguments) = arguments {
                binder.index_non_block_node(&arguments, true, true);
            }
            binder.index_block(block, true, true);
        });
        self.index_self_vars(class, &symbol_table);
        self.complex_points.insert(
            self.points,
            class.index(),
            ComplexPoint::Class(Box::new(ClassStorage::new(symbol_table))),
        );
        // Need to first index the class, because the class body does not have access to
        // the class name.
        if is_decorated {
            self.add_point_definition(
                class.name_definition(),
                Specific::LazyInferredClass,
                in_base_scope,
            );
        } else {
            self.add_redirect_definition(class.name_definition(), class.index(), in_base_scope);
        }
    }

    fn index_self_vars(&mut self, class: ClassDef<'db>, symbol_table: &SymbolTable) {
        for (self_name, name) in class.search_potential_self_assignments() {
            if self.is_self_param(self_name.index()) {
                symbol_table.add_or_replace_symbol(name);
            }
        }
    }

    fn is_self_param(&self, name_index: NodeIndex) -> bool {
        let point = self.points.get(name_index);
        if let PointType::Redirect = point.type_() {
            let param_index = point.node_index();
            let param_point = self.points.get(param_index);
            if let PointType::Specific = param_point.type_() {
                if param_point.specific() == Specific::Param {
                    let name = Name::by_index(self.tree, param_index);
                    return name.has_self_param_position();
                }
            }
        }
        false
    }

    fn index_match_stmt(&mut self, match_stmt: MatchStmt<'db>, ordered: bool) -> NodeIndex {
        todo!("match_stmt")
    }

    fn index_non_block_node<T: InterestingNodeSearcher<'db>>(
        &mut self,
        node: &T,
        ordered: bool,
        in_base_scope: bool,
    ) -> NodeIndex {
        let mut latest_return_or_yield = 0;
        for n in node.search_interesting_nodes() {
            match n {
                InterestingNode::Name(name) => {
                    match name.parent() {
                        NameParent::Atom => {
                            self.maybe_add_reference(name, ordered);
                        }
                        NameParent::NameDefinition(name_def) => {
                            if name_def.is_not_primary() {
                                // The types are inferred later.
                                self.add_new_definition(
                                    name_def,
                                    Point::new_uncalculated(),
                                    in_base_scope,
                                )
                            }
                        }
                        NameParent::GlobalStmt => {
                            //self.maybe_add_reference(name, ordered);
                            dbg!("TODO unhandled global");
                        }
                        NameParent::NonlocalStmt => {
                            // TODO nonlocal
                        }
                        NameParent::Other => {
                            // All other names are not references or part of imports and should be
                            // resolved later.
                        }
                    }
                }
                InterestingNode::YieldExpr(n) => {
                    self.index_return_or_yield(&mut latest_return_or_yield, n.index());
                }
                InterestingNode::ReturnStmt(n) => {
                    self.index_return_or_yield(&mut latest_return_or_yield, n.index());
                }
                InterestingNode::Lambda(lambda) => {
                    self.index_lambda_param_defaults(lambda, ordered);
                    self.unresolved_nodes.push(Unresolved::Lambda(lambda));
                }
                InterestingNode::Comprehension(comp) => {
                    // Index the first expression of a comprehension, which is always executed
                    // in the current scope.
                    if comp.is_generator() {
                        self.unresolved_nodes.push(Unresolved::Comprehension(comp));
                    } else {
                        self.index_comprehension(comp, ordered);
                    }
                }
                InterestingNode::DictComprehension(comp) => {
                    self.index_dict_comprehension(comp, ordered);
                }
            }
        }
        latest_return_or_yield
    }

    fn index_return_or_yield(&self, latest_return_or_yield: &mut NodeIndex, node_index: NodeIndex) {
        let keyword_index = node_index + 1;
        self.points.set(
            keyword_index,
            Point::new_node_analysis_with_node_index(Locality::File, *latest_return_or_yield),
        );
        *latest_return_or_yield = keyword_index
    }

    fn index_comprehension(&mut self, comp: Comprehension<'db>, ordered: bool) {
        // TODO the ordered argument is not used here currently and it should probably be used.
        let (expr, for_if_clauses) = comp.unpack();
        let mut clauses = for_if_clauses.iter();
        self.index_comprehension_clause(&expr, &clauses.next().unwrap(), &mut clauses)
    }

    fn index_dict_comprehension(&mut self, comp: DictComprehension<'db>, ordered: bool) {
        let (expr, for_if_clauses) = comp.unpack();
        let mut clauses = for_if_clauses.iter();
        self.index_comprehension_clause(&expr, &clauses.next().unwrap(), &mut clauses)
    }

    fn index_comprehension_clause(
        &mut self,
        expr: &CommonComprehensionExpression<'db>,
        clause: &ForIfClause<'db>,
        clauses: &mut ForIfClauseIterator<'db>,
    ) {
        let targets = match clause {
            ForIfClause::Sync(sync_for_if_clause) | ForIfClause::Async(sync_for_if_clause) => {
                let (targets, from, ifs) = sync_for_if_clause.unpack();
                self.index_non_block_node(&from, true, false);
                for if_ in ifs {
                    self.index_non_block_node(&if_, true, false);
                }
                targets
            }
        };
        // TODO this is not exactly correct for named expressions and their scopes.
        let symbol_table = SymbolTable::default();
        self.with_nested(NameBinderType::Comprehension, &symbol_table, |binder| {
            binder.index_non_block_node(&targets, true, false);

            if let Some(clause) = clauses.next() {
                binder.index_comprehension_clause(expr, &clause, clauses);
            } else {
                match expr {
                    CommonComprehensionExpression::Single(named_expr) => {
                        binder.index_non_block_node(named_expr, true, false)
                    }
                    CommonComprehensionExpression::DictKeyValue(dict_key_value) => {
                        binder.index_non_block_node(dict_key_value, true, false)
                    }
                };
            }
        });
    }

    fn index_function_name_and_param_defaults(
        &mut self,
        func: FunctionDef<'db>,
        ordered: bool,
        in_base_scope: bool,
        decorators: Option<Decorators>,
        is_async: bool,
    ) {
        // If there is no parent, this does not have to be resolved immediately in theory, but for
        // now we just do.
        self.unresolved_nodes.push(Unresolved::FunctionDef(func));

        let (name_def, params, return_annotation, _) = func.unpack();
        for param in params.iter() {
            // expressions are resolved immediately while annotations are inferred at the
            // end of a module.
            if let Some(annotation) = param.annotation() {
                self.unresolved_nodes
                    .push(Unresolved::Expression(annotation.expression()));
            }
            if let Some(expression) = param.default() {
                self.index_non_block_node(&expression, ordered, false);
            }
        }
        if let Some(return_annotation) = return_annotation {
            // This is the -> annotation that needs to be resolved at the end of a module.
            self.unresolved_nodes
                .push(Unresolved::Expression(return_annotation.expression()));
        }

        let mut is_overload = false;
        let mut function_type = FunctionType::Function;
        if let Some(decorators) = decorators {
            for decorator in decorators.iter() {
                let expression = decorator.named_expression().expression();
                if let ExpressionContent::ExpressionPart(ExpressionPart::Atom(atom)) =
                    expression.unpack()
                {
                    if let AtomContent::Name(name) = atom.unpack() {
                        match name.as_str() {
                            "property" => function_type = FunctionType::Property,
                            "classmethod" => function_type = FunctionType::ClassMethod,
                            "staticmethod" => function_type = FunctionType::StaticMethod,
                            "overload" => is_overload = true,
                            _ => (),
                        }
                    }
                }
            }
        }
        is_overload = false;
        if is_overload {
            let name = name_def.name();
            self.complex_points.insert(
                self.points,
                name.index(),
                ComplexPoint::FunctionOverload(Box::new(Overload {
                    functions: Box::new([]),
                    function_type,
                    implementation_function: is_overload
                        .then(|| PointLink::new(self.file_index, func.index())),
                    is_async,
                })),
            );
            self.symbol_table.add_or_replace_symbol(name);
        } else {
            self.add_new_definition(
                name_def,
                Point::new_redirect(self.file_index, func.index(), Locality::Stmt),
                true,
            );
        }
        self.points.set(
            func.index(),
            Point::new_simple_specific(
                if is_overload || !matches!(self.type_, NameBinderType::Function) {
                    Specific::Function
                } else {
                    Specific::Closure
                },
                Locality::Stmt,
            ),
        );
    }

    pub fn index_function_body(&mut self, func: FunctionDef<'db>) {
        // Function name was indexed already.
        let (_, params, _, block) = func.unpack();

        for param in params.iter() {
            // defaults and annotations are already indexed
            self.add_point_definition(param.name_definition(), Specific::Param, true);
        }

        let latest_return_index = self.index_block(block, true, true);
        // It's kind of hard to know where to store the latest reference statement.
        self.points.set(
            func.index() + 1,
            Point::new_node_analysis_with_node_index(
                Locality::ClassOrFunction,
                latest_return_index,
            ),
        );
    }

    fn index_lambda_param_defaults(&mut self, lambda: Lambda<'db>, ordered: bool) {
        // lambda: "lambda" [lambda_parameters] ":" expression
        for param in lambda.params() {
            if let Some(default) = param.default() {
                self.index_non_block_node(&default, ordered, false);
            }
        }
    }

    fn index_lambda(&mut self, lambda: Lambda<'db>) {
        let (params, expr) = lambda.unpack();
        for param in params {
            self.add_point_definition(param.name_definition(), Specific::Param, true);
        }
        self.index_non_block_node(&expr, true, true);
    }

    #[inline]
    fn maybe_add_reference(&mut self, name: Name<'db>, ordered: bool) {
        if ordered {
            let mut n = None;
            self.add_reference(name, |name| n = Some(name));
            if let Some(n) = n {
                self.unresolved_names.push(n);
            }
        } else {
            self.unordered_references.push(name);
        }
    }

    #[inline]
    fn add_reference(&self, name: Name<'db>, mut unresolved_name_callback: impl FnMut(Name<'db>)) {
        let point = {
            if self.parent_lookup_not_finished {
                if let Some(definition) = self.symbol_table.lookup_symbol(name.as_str()) {
                    Point::new_redirect(self.file_index, definition, Locality::File)
                } else {
                    unresolved_name_callback(name);
                    return;
                }
            } else if let Some(definition) = self.lookup_name(name) {
                Point::new_redirect(self.file_index, definition, Locality::File)
            } else {
                Point::new_uncalculated()
            }
        };
        self.points.set(name.index(), point);
    }

    fn lookup_name(&self, name: Name<'db>) -> Option<NodeIndex> {
        self.symbol_table
            .lookup_symbol(name.as_str())
            // If the symbol is not defined in the symbol table, it can also be in a parent scope.
            .or_else(|| self.parent.and_then(|parent| parent.lookup_name(name)))
    }

    fn index_unordered_references(&mut self) {
        for &name in &self.unordered_references {
            let mut n = None;
            self.add_reference(name, |name| n = Some(name));
            if let Some(n) = n {
                self.unresolved_names.push(n);
            }
        }
        self.unordered_references.truncate(0);
    }
}
