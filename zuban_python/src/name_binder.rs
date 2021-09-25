use std::cell::Cell;

use crate::database::{
    ClassStorage, ComplexPoint, FileIndex, Locality, Point,
    PointType::{LanguageSpecific, MultiDefinition, Redirect},
    Specific,
};
use crate::file::ComplexValues;
use crate::utils::SymbolTable;
use parsa::{Node, NodeIndex};
use parsa_python::PyNodeType::{Keyword, Nonterminal, Terminal};
use parsa_python::{NonterminalType, PyNode, PyNodeType, PyTree, TerminalType};

pub enum NameBinderType {
    Global,
    Function,
    Class,
    Lambda,
    Comprehension,
}

pub struct NameBinder<'db, 'a> {
    tree: &'db PyTree,
    typ: NameBinderType,
    symbol_table: &'a SymbolTable,
    points: &'db [Cell<Point>],
    complex_points: &'db ComplexValues,
    unordered_references: Vec<PyNode<'db>>,
    unresolved_nodes: Vec<PyNode<'db>>,
    unresolved_names: Vec<PyNode<'db>>,
    file_index: FileIndex,
    parent_lookup_not_finished: bool,
    parent: Option<&'a NameBinder<'db, 'a>>,
}

impl<'db, 'a> NameBinder<'db, 'a> {
    fn new(
        tree: &'db PyTree,
        typ: NameBinderType,
        symbol_table: &'a SymbolTable,
        points: &'db [Cell<Point>],
        complex_points: &'db ComplexValues,
        file_index: FileIndex,
        parent: Option<&'a Self>,
    ) -> Self {
        Self {
            tree,
            typ,
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
        tree: &'db PyTree,
        symbol_table: &'a SymbolTable,
        points: &'db [Cell<Point>],
        complex_points: &'db ComplexValues,
        file_index: FileIndex,
        parent: Option<&'a Self>,
        func: impl FnOnce(&mut Self),
    ) {
        let mut binder = Self::new(
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
        typ: NameBinderType,
        symbol_table: &'_ SymbolTable,
        mut func: impl FnMut(&mut NameBinder<'db, '_>),
    ) {
        let mut name_binder = NameBinder::new(
            self.tree,
            typ,
            symbol_table,
            self.points,
            self.complex_points,
            self.file_index,
            Some(self),
        );
        func(&mut name_binder);
        name_binder.close();
        let unresolved_names = name_binder.unresolved_names;
        self.unresolved_nodes.extend(unresolved_names);
    }

    fn add_new_definition(&self, name_def: PyNode<'db>, point: Point) {
        debug_assert_eq!(
            name_def.get_type(),
            Nonterminal(NonterminalType::name_definition)
        );
        let name = name_def.get_nth_child(0);
        let replaced = self.symbol_table.add_or_replace_symbol(name);
        if let Some(replaced) = replaced {
            //dbg!("TODO multi reference {:?}", replaced);
        }
        self.points[name.index as usize].set(point);
    }

    fn add_point_definition(&mut self, name_def: PyNode<'db>, type_: Specific) {
        self.add_new_definition(
            name_def,
            Point::new_simple_language_specific(type_, Locality::Stmt),
        );
    }

    fn add_redirect_definition(&mut self, name_def: PyNode<'db>, node_index: NodeIndex) {
        self.add_new_definition(
            name_def,
            Point::new_redirect(self.file_index, node_index, Locality::Stmt),
        );
    }

    pub fn index_file(&mut self, file_node: PyNode<'db>) {
        self.index_stmts(file_node.iter_children(), true);
    }

    fn index_block(&mut self, block_node: PyNode<'db>, ordered: bool) -> NodeIndex {
        // Returns the latest return/yield index
        // Theory:
        // - while_stmt, for_stmt: ignore order (at least mostly)
        // - match_stmt, if_stmt, try_stmt (only in coresponding blocks and after)
        // - sync_for_if_clause: reversed order and only in scope
        // - lambda: only in scope
        // - function_def, class_def: ignore
        debug_assert_eq!(block_node.get_type(), Nonterminal(NonterminalType::block));
        if block_node
            .get_nth_child(0)
            .is_type(Nonterminal(NonterminalType::simple_stmts))
        {
            self.index_non_block_node(block_node, ordered)
        } else {
            self.index_stmts(block_node.iter_children().skip(2), ordered)
        }
    }

    fn index_stmts(
        &mut self,
        stmts: impl Iterator<Item = PyNode<'db>>,
        ordered: bool,
    ) -> NodeIndex {
        use NonterminalType::*;
        //debug_assert_eq!(stmts_node.get_type(), Nonterminal(stmts));
        let mut latest_return_or_yield = 0;
        for child in stmts {
            if child.is_type(Terminal(TerminalType::Endmarker))
                || child.is_type(Terminal(TerminalType::Newline))
                || child.is_type(Terminal(TerminalType::Dedent))
            {
                continue;
            }
            let child = child.get_nth_child(0);
            let return_or_yield = if child.is_type(Nonterminal(simple_stmts)) {
                self.index_non_block_node(child, ordered)
            } else if child.is_type(Nonterminal(function_def)) {
                self.index_function_name_and_param_defaults(child, ordered);
                0
            } else if child.is_type(Nonterminal(class_def)) {
                self.index_class(child);
                0
            } else if child.is_type(Nonterminal(decorated)) {
                let not_decorated = child.get_nth_child(1);
                if not_decorated.is_type(Nonterminal(function_def)) {
                    self.index_function_name_and_param_defaults(not_decorated, ordered);
                } else if not_decorated.is_type(Nonterminal(class_def)) {
                    self.add_point_definition(
                        not_decorated.get_nth_child(1),
                        Specific::LazyInferredClass,
                    );
                } else {
                    debug_assert_eq!(not_decorated.get_type(), Nonterminal(async_function_def));
                    /*
                    self.add_point_definition(
                        not_decorated.get_nth_child(0).get_nth_child(1),
                    );
                    */
                    todo!("async stmt")
                }
                0
            } else if child.is_type(Nonterminal(if_stmt)) {
                self.index_if_stmt(child, ordered)
            } else if child.is_type(Nonterminal(try_stmt)) {
                self.index_try_stmt(child, ordered)
            } else if child.is_type(Nonterminal(for_stmt)) {
                self.index_for_stmt(child, ordered)
            } else if child.is_type(Nonterminal(while_stmt)) {
                self.index_while_stmt(child, ordered)
            } else if child.is_type(Nonterminal(match_stmt)) {
                self.index_match_stmt(child, ordered)
            } else if child.is_type(Nonterminal(with_stmt)) {
                self.index_with_stmt(child, ordered)
            } else if child.is_type(Nonterminal(async_stmt)) {
                let iterator = child.iter_children();
                let mut iterator = iterator.skip(1);
                let inner = iterator.next().unwrap();
                if inner.is_type(Nonterminal(function_def)) {
                    self.index_function_name_and_param_defaults(inner, ordered);
                    0
                } else if inner.is_type(Nonterminal(for_stmt)) {
                    self.index_for_stmt(inner, ordered)
                } else if inner.is_type(Nonterminal(with_stmt)) {
                    self.index_with_stmt(child, ordered)
                } else {
                    unreachable!()
                }
            } else {
                unreachable!("But found {:?}", child.get_type());
            };
            latest_return_or_yield =
                self.merge_latest_return_or_yield(latest_return_or_yield, return_or_yield);
        }
        latest_return_or_yield
    }

    fn merge_latest_return_or_yield(&self, first: NodeIndex, mut second: NodeIndex) -> NodeIndex {
        if first != 0 && second != 0 {
            loop {
                let point = self.points[second as usize].get();
                let node_index = point.get_node_index();
                if node_index == 0 {
                    // Now that we have the first node in the chain of the second nodes, link that
                    // to the first one (like a linked list)
                    self.points[second as usize].set(Point::new_node_analysis_with_node_index(
                        Locality::File,
                        first,
                    ));
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
        use NonterminalType::*;
        self.index_unordered_references();

        self.parent_lookup_not_finished = true;
        while let Some(n) = self.unresolved_nodes.pop() {
            if n.is_type(Terminal(TerminalType::Name)) {
                self.maybe_add_reference(n, true);
            } else if n.is_type(Nonterminal(comprehension)) {
                // TODO It is not correct to index the last part of the expression here. It should
                // have been done at the point where the generator was created.
                self.index_comprehension(n, true);
            } else if n.is_type(Nonterminal(lambda)) {
                let symbol_table = SymbolTable::default();
                self.with_nested(NameBinderType::Lambda, &symbol_table, |binder| {
                    binder.index_lambda(n)
                });
            } else if n.is_type(Nonterminal(expression)) {
                // Typically annotations
                self.index_non_block_node(n, true);
            } else if n.is_type(Nonterminal(function_def)) {
                let symbol_table = SymbolTable::default();
                self.with_nested(NameBinderType::Function, &symbol_table, |binder| {
                    binder.index_function_body(n)
                });
            } else {
                unreachable!("closing scope {:?}", n);
            }
        }
        debug_assert_eq!(self.unordered_references.len(), 0);
    }

    fn index_for_stmt(&mut self, for_stmt: PyNode<'db>, ordered: bool) -> NodeIndex {
        debug_assert_eq!(for_stmt.get_type(), Nonterminal(NonterminalType::for_stmt));
        let mut latest_return_or_yield = 0;
        // "for" star_targets "in" star_expressions ":" block else_block?
        let iterator = for_stmt.iter_children();
        let mut iterator = iterator.skip(1);

        let latest = self.index_non_block_node(iterator.next().unwrap(), ordered);
        latest_return_or_yield = self.merge_latest_return_or_yield(latest_return_or_yield, latest);
        let mut iterator = iterator.skip(1);
        let latest = self.index_non_block_node(iterator.next().unwrap(), ordered);
        latest_return_or_yield = self.merge_latest_return_or_yield(latest_return_or_yield, latest);

        let mut iterator = iterator.skip(1);
        let latest = self.index_block(iterator.next().unwrap(), false);
        latest_return_or_yield = self.merge_latest_return_or_yield(latest_return_or_yield, latest);

        if ordered {
            self.index_unordered_references();
        }
        if let Some(else_) = iterator.next() {
            // "else" ":" block
            let latest = self.index_block(else_.get_nth_child(2), ordered);
            latest_return_or_yield =
                self.merge_latest_return_or_yield(latest_return_or_yield, latest);
        }
        latest_return_or_yield
    }

    fn index_while_stmt(&mut self, while_stmt: PyNode<'db>, ordered: bool) -> NodeIndex {
        debug_assert_eq!(
            while_stmt.get_type(),
            Nonterminal(NonterminalType::while_stmt)
        );
        let mut latest_return_or_yield = 0;
        // "while" named_expression ":" block else_block?
        let iterator = while_stmt.iter_children();
        let mut iterator = iterator.skip(1);

        let latest = self.index_non_block_node(iterator.next().unwrap(), ordered);
        latest_return_or_yield = self.merge_latest_return_or_yield(latest_return_or_yield, latest);
        let mut iterator = iterator.skip(1);
        let latest = self.index_non_block_node(iterator.next().unwrap(), false);
        latest_return_or_yield = self.merge_latest_return_or_yield(latest_return_or_yield, latest);
        if ordered {
            self.index_unordered_references();
        }
        if let Some(else_) = iterator.next() {
            // "else" ":" block
            let latest = self.index_block(else_.get_nth_child(2), ordered);
            latest_return_or_yield =
                self.merge_latest_return_or_yield(latest_return_or_yield, latest);
        }
        latest_return_or_yield
    }

    fn index_with_stmt(&mut self, with_stmt: PyNode<'db>, ordered: bool) -> NodeIndex {
        debug_assert_eq!(
            with_stmt.get_type(),
            Nonterminal(NonterminalType::with_stmt)
        );
        let mut latest_return_or_yield = 0;
        // with_stmt: "with" ("(" ",".with_item+ ","? ")" | ",".with_item+ )  ":" block
        for child in with_stmt.iter_children() {
            let latest = match child.get_type() {
                Nonterminal(NonterminalType::with_item) => {
                    // expression ["as" star_target]
                    let latest = self.index_non_block_node(child.get_nth_child(0), ordered);
                    latest_return_or_yield =
                        self.merge_latest_return_or_yield(latest_return_or_yield, latest);
                    self.index_non_block_node(child.get_nth_child(2), ordered)
                }
                Nonterminal(NonterminalType::block) => self.index_block(child, ordered),
                _ => 0,
            };
            latest_return_or_yield =
                self.merge_latest_return_or_yield(latest_return_or_yield, latest);
        }
        latest_return_or_yield
    }

    fn index_if_stmt(&mut self, if_stmt: PyNode<'db>, ordered: bool) -> NodeIndex {
        debug_assert_eq!(if_stmt.get_type(), Nonterminal(NonterminalType::if_stmt));
        // "if" named_expression ":" block ("elif" named_expression ":" block)* else_block?

        let mut latest_return_or_yield = 0;
        for child in if_stmt.iter_children().skip(1) {
            let latest = match child.get_type() {
                Nonterminal(NonterminalType::named_expression) => {
                    self.index_non_block_node(child, ordered)
                }
                Nonterminal(NonterminalType::block) => self.index_block(child, ordered),
                Nonterminal(NonterminalType::else_block) => {
                    self.index_block(child.get_nth_child(2), ordered)
                }
                Keyword => 0,
                _ => (unreachable!()),
            };
            latest_return_or_yield =
                self.merge_latest_return_or_yield(latest_return_or_yield, latest);
        }
        latest_return_or_yield
    }

    fn index_try_stmt(&mut self, try_stmt: PyNode<'db>, ordered: bool) -> NodeIndex {
        debug_assert_eq!(try_stmt.get_type(), Nonterminal(NonterminalType::try_stmt));
        let mut latest_return_or_yield = 0;
        // "try" ":" block (except_block+ else_block? finally_block? | finally_block)
        for child in try_stmt.iter_children() {
            let latest = match child.get_type() {
                Nonterminal(NonterminalType::block) => self.index_block(child, ordered),
                Nonterminal(NonterminalType::except_block) => {
                    // except_clause ":" block
                    let except_clause = child.get_nth_child(0);
                    // except_clause: "except" [expression ["as" name_definition]]
                    for child in except_clause.iter_children() {
                        if child.is_type(Nonterminal(NonterminalType::expression)) {
                            self.index_non_block_node(child, ordered);
                        } else if child.is_type(Nonterminal(NonterminalType::name_definition)) {
                            self.add_redirect_definition(child, except_clause.index as u32);
                        }
                    }
                    // block
                    self.index_block(child.get_nth_child(2), ordered)
                }
                Nonterminal(NonterminalType::finally_block)
                | Nonterminal(NonterminalType::else_block) => {
                    // "finally" ":" block
                    // "else" ":" block
                    self.index_block(child.get_nth_child(2), ordered)
                }
                _ => 0,
            };
            latest_return_or_yield =
                self.merge_latest_return_or_yield(latest_return_or_yield, latest);
        }
        latest_return_or_yield
    }

    fn index_class(&mut self, class: PyNode<'db>) {
        // "class" name_definition ["(" [arguments] ")"] ":" block
        debug_assert_eq!(class.get_type(), Nonterminal(NonterminalType::class_def));
        let symbol_table = SymbolTable::default();
        self.with_nested(NameBinderType::Class, &symbol_table, |binder| {
            for child in class.iter_children() {
                if child.is_type(Nonterminal(NonterminalType::arguments)) {
                    binder.index_non_block_node(child, true);
                } else if child.is_type(Nonterminal(NonterminalType::block)) {
                    binder.index_block(child, true);
                }
            }
        });
        self.index_self_vars(class, &symbol_table);
        self.complex_points.insert(
            self.points,
            class.index,
            ComplexPoint::Class(ClassStorage::new(symbol_table)),
        );
        // Need to first index the class, because the class body does not have access to
        // the class name.
        self.add_redirect_definition(class.get_nth_child(1), class.index as u32);
    }

    fn index_self_vars(&mut self, class: PyNode<'db>, symbol_table: &SymbolTable) {
        for node in class.search(&[Nonterminal(NonterminalType::t_primary)]) {
            let name_def = node.get_nth_child(2);
            if name_def.is_type(Nonterminal(NonterminalType::name_definition)) {
                let atom = node.get_nth_child(0);
                if atom.is_type(Nonterminal(NonterminalType::atom)) {
                    let self_name = atom.get_nth_child(0);
                    if self_name.is_type(Terminal(TerminalType::Name)) {
                        if self.is_self_param(self_name.index as usize) {
                            symbol_table.add_or_replace_symbol(name_def.get_nth_child(0));
                        }
                    }
                }
            }
        }
    }

    fn is_self_param(&self, name_index: usize) -> bool {
        let point = self.points[name_index].get();
        if let Redirect = point.get_type() {
            let param_index = point.get_node_index();
            let param_point = self.points[param_index as usize].get();
            if let LanguageSpecific = param_point.get_type() {
                if param_point.get_language_specific() == Specific::Param {
                    let name_node = self.tree.get_node_by_index(param_index);
                    // Parents are name_definition/param_no_default/parameters
                    let param = name_node.get_parent().unwrap().get_parent().unwrap();
                    let params = param.get_parent().unwrap();
                    // Could also be a kwarg, which is never a self
                    if params.is_type(Nonterminal(NonterminalType::parameters)) {
                        if params.index + 1 == param.index {
                            return true;
                        }
                    }
                }
            }
        }
        false
    }

    fn index_match_stmt(&mut self, match_stmt: PyNode<'db>, ordered: bool) -> NodeIndex {
        debug_assert_eq!(
            match_stmt.get_type(),
            Nonterminal(NonterminalType::match_stmt)
        );
        // "match" subject_expr ":" Newline Indent case_block+ Dedent
        todo!("match_stmt")
    }

    fn index_non_block_node(&mut self, node: PyNode<'db>, ordered: bool) -> NodeIndex {
        use NonterminalType::*;
        const SEARCH_NAMES: &[PyNodeType] = &[
            Terminal(TerminalType::Name),
            Nonterminal(lambda),
            Nonterminal(comprehension),
            Nonterminal(dict_comprehension),
            Nonterminal(yield_expr),
            Nonterminal(return_stmt),
            Nonterminal(dict_comprehension),
        ];
        let mut latest_return_or_yield = 0;
        for n in node.search(SEARCH_NAMES) {
            if n.is_type(Terminal(TerminalType::Name)) {
                let parent = n.get_parent().unwrap();
                if parent.is_type(Nonterminal(name_definition)) {
                    if !parent.get_parent().unwrap().is_type(Nonterminal(t_primary)) {
                        // The types are inferred later.
                        self.add_new_definition(parent, Point::new_uncalculated())
                    }
                } else {
                    self.index_reference(n, parent, ordered);
                }
            } else if n.is_type(Nonterminal(lambda)) {
                self.index_lambda_param_defaults(n, ordered);
                self.unresolved_nodes.push(n);
            } else if n.is_type(Nonterminal(return_stmt)) || n.is_type(Nonterminal(yield_expr)) {
                let keyword_index = n.index + 1;
                self.points[keyword_index as usize].set(Point::new_node_analysis_with_node_index(
                    Locality::File,
                    latest_return_or_yield,
                ));
                latest_return_or_yield = keyword_index
            } else {
                // Index the first expression of a comprehension, which is always executed
                // in the current scope.
                let parent = n.get_parent().unwrap();
                let bracket = parent.get_nth_child(0).get_code();
                if (bracket == "[" || bracket == "{") && parent.is_type(Nonterminal(atom)) {
                    self.index_comprehension(n, ordered);
                } else {
                    self.unresolved_nodes.push(n);
                }
            }
        }
        latest_return_or_yield
    }

    fn index_comprehension(&mut self, comp: PyNode<'db>, ordered: bool) {
        // comprehension: named_expression for_if_clauses
        // dict_comprehension: dict_key_value for_if_clauses
        let clauses = comp.get_nth_child(1);
        debug_assert_eq!(
            clauses.get_type(),
            Nonterminal(NonterminalType::for_if_clauses)
        );
        let mut iterator = clauses.iter_children();

        let first_clause = iterator.next().unwrap();
        // TODO the ordered argument is not used here currently and it should probably be used.
        self.index_comprehension_clause(&mut iterator, first_clause, comp.get_nth_child(0));
    }

    fn index_comprehension_clause(
        &mut self,
        clauses: &mut impl Iterator<Item = PyNode<'db>>,
        mut clause: PyNode<'db>,
        // Either a named_expression or a dict_key_value
        result_node: PyNode<'db>,
    ) {
        use NonterminalType::*;
        if clause.is_type(Nonterminal(async_for_if_clause)) {
            // async_for_if_clause:? ["async"] sync_for_if_clause
            clause = clause.get_nth_child(1);
        }

        // sync_for_if_clause: "for" star_targets "in" disjunction comp_if*
        debug_assert_eq!(clause.get_type(), Nonterminal(sync_for_if_clause));
        for child in clause.iter_children() {
            if child.is_type(Nonterminal(disjunction)) || child.is_type(Nonterminal(comp_if)) {
                self.index_non_block_node(child, true);
            }
        }
        // TODO this is not exactly correct for named expressions and their scopes.
        let symbol_table = SymbolTable::default();
        self.with_nested(NameBinderType::Comprehension, &symbol_table, |binder| {
            binder.index_non_block_node(clause.get_nth_child(1), true);
            if let Some(clause) = clauses.next() {
                binder.index_comprehension_clause(clauses, clause, result_node);
            } else {
                binder.index_non_block_node(result_node, true);
            }
        });
    }

    fn index_function_name_and_param_defaults(&mut self, node: PyNode<'db>, ordered: bool) {
        use NonterminalType::*;
        debug_assert_eq!(node.get_type(), Nonterminal(function_def));
        // function_def: "def" name_definition function_def_parameters return_annotation? ":" block
        if self.parent.is_some() {
            // Has to be resolved, because we otherwise have no knowledge about the symbol
            // tables in parents.
            self.unresolved_nodes.push(node);
        }

        for child in node.iter_children() {
            if child.is_type(Nonterminal(function_def_parameters)) {
                let parameters_node = child.get_nth_child(1);
                if parameters_node.is_type(Nonterminal(parameters)) {
                    for n in
                        parameters_node.search(&[Nonterminal(annotation), Nonterminal(expression)])
                    {
                        // expressions are resolved immediately while annotations are inferred at the
                        // end of a module.
                        if n.is_type(Nonterminal(annotation)) {
                            self.unresolved_nodes.push(n.get_nth_child(1));
                        } else {
                            self.index_non_block_node(n, ordered);
                        }
                    }
                }
            } else if child.is_type(Nonterminal(return_annotation)) {
                // This is the -> annotation that needs to be resolved at the end of a module.
                self.unresolved_nodes.push(child.get_nth_child(1));
            }
        }
        self.add_point_definition(
            node.get_nth_child(1),
            if matches!(self.typ, NameBinderType::Function) {
                Specific::LazyInferredClosure
            } else {
                Specific::LazyInferredFunction
            },
        );
    }

    pub fn index_function_body(&mut self, func: PyNode<'db>) {
        // "def" name_definition "(" [parameters] ")" ["->" expression] ":" block
        use NonterminalType::*;
        debug_assert_eq!(func.get_type(), Nonterminal(function_def));

        let func_index = func.index as usize;
        // Function name was indexed already.
        for child in func.iter_children() {
            if child.is_type(Nonterminal(function_def_parameters)) {
                let parameters_node = child.get_nth_child(1);
                if parameters_node.is_type(Nonterminal(parameters)) {
                    for n in child.search(&[Nonterminal(name_definition), Nonterminal(expression)])
                    {
                        if n.is_type(Nonterminal(name_definition)) {
                            self.add_point_definition(n, Specific::Param);
                        } // defaults and annotations are already indexed
                    }
                }
            } else if child.is_type(Nonterminal(block)) {
                let latest_return_index = self.index_block(child, true);
                // It's kind of hard to know where to store the latest reference statement.
                self.points[func_index + 1].set(Point::new_node_analysis_with_node_index(
                    Locality::ClassOrFunction,
                    latest_return_index,
                ));
            }
        }
        let parent = func.get_parent().unwrap();
        if !parent.is_type(Nonterminal(stmt)) && !parent.is_type(Nonterminal(decorated)) {
            todo!("{:?}", parent);
        }
        self.points[func_index].set(Point::new_simple_language_specific(
            if matches!(self.parent.unwrap().typ, NameBinderType::Function) {
                Specific::Closure
            } else {
                Specific::Function
            },
            Locality::Stmt,
        ));

        // Avoid overwriting multi definitions
        let mut name_index = func.index as usize + 3;
        if self.points[name_index].get().get_type() == MultiDefinition {
            name_index -= 1;
        }
        self.points[name_index].set(Point::new_redirect(
            self.file_index,
            func.index,
            Locality::Stmt,
        ));
    }

    fn index_lambda_param_defaults(&mut self, node: PyNode<'db>, ordered: bool) {
        use NonterminalType::*;
        // lambda: "lambda" [lambda_parameters] ":" expression
        let params = node.get_nth_child(1);
        if params.is_type(Nonterminal(lambda_parameters)) {
            for n in params.search(&[Nonterminal(expression)]) {
                self.index_non_block_node(n, ordered);
            }
        }
    }

    fn index_lambda(&mut self, node: PyNode<'db>) {
        use NonterminalType::*;
        debug_assert_eq!(node.get_type(), Nonterminal(lambda));
        for child in node.iter_children() {
            if child.is_type(Nonterminal(lambda_parameters)) {
                for n in child.search(&[Nonterminal(name_definition), Nonterminal(expression)]) {
                    if n.is_type(Nonterminal(name_definition)) {
                        self.add_point_definition(n, Specific::Param);
                    } // defaults are already indexed
                }
            }
            if child.is_type(Nonterminal(expression)) {
                self.index_non_block_node(child, true);
            }
        }
    }

    fn index_reference(&mut self, name: PyNode<'db>, parent: PyNode<'db>, ordered: bool) {
        use NonterminalType::*;
        debug_assert_eq!(name.get_type(), Terminal(TerminalType::Name));
        if parent.is_type(Nonterminal(atom)) {
            self.maybe_add_reference(name, ordered);
        } else if parent.is_type(Nonterminal(global_stmt)) {
            //self.maybe_add_reference(name, ordered);
            dbg!("TODO unhandled global");
        } else if parent.is_type(Nonterminal(nonlocal_stmt)) {
            // TODO nonlocal
        }
        // All other names are not references or part of imports and should be resolved later.
    }

    #[inline]
    fn maybe_add_reference(&mut self, name: PyNode<'db>, ordered: bool) {
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
    fn add_reference(
        &self,
        name: PyNode<'db>,
        mut unresolved_name_callback: impl FnMut(PyNode<'db>),
    ) {
        let point = {
            if self.parent_lookup_not_finished {
                if let Some(definition) = self.symbol_table.lookup_symbol(name.get_code()) {
                    Point::new_redirect(self.file_index, definition, Locality::File)
                } else {
                    unresolved_name_callback(name);
                    return;
                }
            } else if let Some(definition) = self.lookup_name(name) {
                Point::new_redirect(self.file_index, definition, Locality::File)
            } else {
                Point::new_missing_or_unknown(self.file_index, Locality::File)
            }
        };
        self.points[name.index as usize].set(point);
    }

    fn lookup_name(&self, name: PyNode<'db>) -> Option<NodeIndex> {
        self.symbol_table
            .lookup_symbol(name.get_code())
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
