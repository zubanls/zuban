use std::cell::Cell;

use parsa_python::{PyNode, PyNodeType, NonterminalType, TerminalType};
use parsa_python::PyNodeType::{Nonterminal, Terminal, Keyword};
use parsa::{Node, NodeIndex};
use crate::utils::SymbolTable;
use crate::database::{ValueOrReference, ValueEnum, Locality, FileIndex, ClassStorage,
                      ValueOrReferenceType::MultiDefinition, ComplexValue};
use crate::file::ComplexValues;

pub struct NameBinder<'a, 'b> {
    symbol_table: &'b SymbolTable,
    values_or_references: &'a [Cell<ValueOrReference>],
    complex_values: &'a ComplexValues,
    unordered_references: Vec<PyNode<'a>>,
    unresolved_nodes: Vec<PyNode<'a>>,
    unresolved_names: Vec<PyNode<'a>>,
    file_index: FileIndex,
    parent_lookup_not_finished: bool,
    parent: Option<&'b NameBinder<'a, 'b>>,
}

impl<'a, 'b> NameBinder<'a, 'b> {
    fn new(
        symbol_table: &'b SymbolTable,
        values_or_references: &'a [Cell<ValueOrReference>],
        complex_values: &'a ComplexValues,
        file_index: FileIndex,
        parent: Option<&'b Self>,
    ) -> Self {
        Self {
            symbol_table,
            values_or_references,
            complex_values,
            unordered_references: vec![],
            unresolved_nodes: vec![],
            unresolved_names: vec![],
            file_index,
            parent_lookup_not_finished: false,
            parent,
        }
    }

    pub fn with_global_binder(
        symbol_table: &'b SymbolTable,
        values_or_references: &'a [Cell<ValueOrReference>],
        complex_values: &'a ComplexValues,
        file_index: FileIndex,
        parent: Option<&'b Self>,
        func: impl FnOnce(&mut Self),
    ) {
        let mut binder = Self::new(symbol_table, values_or_references, complex_values, file_index, None);
        func(&mut binder);
        binder.close();
    }

    pub fn with_nested(&mut self, symbol_table: &'_ SymbolTable, mut func: impl FnMut(&mut NameBinder<'a, '_>)) {
        let mut name_binder = NameBinder::new(
            symbol_table, self.values_or_references, self.complex_values,
            self.file_index, Some(self));
        func(&mut name_binder);
        name_binder.close();
        let unresolved_names = name_binder.unresolved_names;
        self.unresolved_nodes.extend(unresolved_names);
    }

    fn add_new_definition(&self, name_def: PyNode<'a>, value: ValueOrReference) {
        debug_assert!(name_def.is_type(Nonterminal(NonterminalType::name_definition)));
        let name = name_def.get_nth_child(0);
        let replaced = self.symbol_table.add_or_replace_symbol(name);
        if let Some(replaced) = replaced {
            //dbg!("TODO multi reference {:?}", replaced);
        }
        self.values_or_references[name.index as usize].set(value);
    }

    fn add_value_definition(&mut self, name_def: PyNode<'a>, type_: ValueEnum) {
        self.add_new_definition(
            name_def,
            ValueOrReference::new_simple_language_specific(type_, Locality::Stmt)
        );
    }

    fn set_complex_value(&mut self, node: PyNode<'a>, complex: ComplexValue) {
        let complex_index = self.complex_values.len() as u32;
        self.complex_values.push(Box::pin(complex));
        self.values_or_references[node.index as usize].set(
            ValueOrReference::new_complex_value(complex_index, Locality::Stmt));
    }

    fn add_redirect_definition(&mut self, name_def: PyNode<'a>, node_index: NodeIndex) {
        self.add_new_definition(
            name_def,
            ValueOrReference::new_redirect(
                self.file_index,
                node_index,
                Locality::Stmt,
            )
        );
    }

    pub fn index_file(&mut self, file_node: PyNode<'a>) {
        self.index_stmts(file_node.iter_children(), true);
    }

    fn index_block(&mut self, block_node: PyNode<'a>, ordered: bool) {
        // Theory:
        // - while_stmt, for_stmt: ignore order (at least mostly)
        // - match_stmt, if_stmt, try_stmt (only in coresponding blocks and after)
        // - sync_for_if_clause: reversed order and only in scope
        // - lambda: only in scope
        // - function_def, class_def: ignore
        debug_assert_eq!(block_node.get_type(), Nonterminal(NonterminalType::block));
        if block_node.get_nth_child(0).is_type(Nonterminal(NonterminalType::simple_stmts)) {
            self.index_non_block_node(block_node, ordered);
        } else {
            self.index_stmts(block_node.iter_children().skip(2), ordered);
        }
    }

    fn index_stmts(&mut self, stmts: impl Iterator<Item=PyNode<'a>>, ordered: bool) {
        use NonterminalType::*;
        //debug_assert_eq!(stmts_node.get_type(), Nonterminal(stmts));
        for child in stmts {
            if child.is_type(Terminal(TerminalType::Endmarker))
                || child.is_type(Terminal(TerminalType::Newline))
                || child.is_type(Terminal(TerminalType::Dedent))
            {
                continue
            }
            let child = child.get_nth_child(0);
            if child.is_type(Nonterminal(simple_stmts)) {
                self.index_non_block_node(child, ordered);
            } else if child.is_type(Nonterminal(function_def)) {
                if self.parent.is_some() {
                    // Has to be resolved, because we otherwise have no knowledge about the symbol
                    // tables in parents.
                    self.unresolved_nodes.push(child);
                }
                self.index_function_name_and_param_defaults(child, ordered);
            } else if child.is_type(Nonterminal(class_def)) {
                self.index_class(child);
            } else if child.is_type(Nonterminal(decorated)) {
                let not_decorated = child.get_nth_child(1);
                if not_decorated.is_type(Nonterminal(function_def)) {
                    self.add_value_definition(
                        not_decorated.get_nth_child(1),
                        ValueEnum::LazyInferredFunction,
                    );
                } else if not_decorated.is_type(Nonterminal(class_def)) {
                    self.add_value_definition(
                        not_decorated.get_nth_child(1),
                        ValueEnum::LazyInferredClass,
                    );
                } else {
                    debug_assert!(not_decorated.is_type(Nonterminal(async_function_def)));
                    self.add_value_definition(
                        not_decorated.get_nth_child(0).get_nth_child(1),
                        ValueEnum::LazyInferredClass,
                    );
                }
            } else if child.is_type(Nonterminal(if_stmt)){
                self.index_if_stmt(child, ordered);
            } else if child.is_type(Nonterminal(try_stmt)){
                self.index_try_stmt(child, ordered);
            } else if child.is_type(Nonterminal(for_stmt)){
                self.index_for_stmt(child, ordered);
            } else if child.is_type(Nonterminal(while_stmt)) {
                self.index_while_stmt(child, ordered);
            } else if child.is_type(Nonterminal(match_stmt)) {
                self.index_match_stmt(child, ordered);
            } else if child.is_type(Nonterminal(with_stmt)){
                self.index_with_stmt(child, ordered);
            } else if child.is_type(Nonterminal(async_stmt)) {
                let iterator = child.iter_children();
                let mut iterator = iterator.skip(1);
                let inner = iterator.next().unwrap();
                if inner.is_type(Nonterminal(function_def)) {
                    self.add_value_definition(
                        inner.get_nth_child(1),
                        ValueEnum::LazyInferredFunction,
                    );
                } else if inner.is_type(Nonterminal(for_stmt)) {
                    self.index_for_stmt(inner, ordered);
                } else if inner.is_type(Nonterminal(with_stmt)) {
                    self.index_with_stmt(child, ordered);
                }
            } else {
                unreachable!("But found {:?}", child.get_type());
            }
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
                self.with_nested(&symbol_table, |binder| binder.index_lambda(n));
            } else if n.is_type(Nonterminal(expression)) {
                // Typically annotations
                self.index_non_block_node(n, true);
            } else if n.is_type(Nonterminal(function_def)) {
                let symbol_table = SymbolTable::default();
                self.with_nested(&symbol_table, |binder| binder.index_function_body(n));
            } else {
                unreachable!("closing scope {:?}", n);
            }
        }
        debug_assert_eq!(self.unordered_references.len(), 0);
    }

    fn index_for_stmt(&mut self, for_stmt: PyNode<'a>, ordered: bool) {
        debug_assert_eq!(for_stmt.get_type(), Nonterminal(NonterminalType::for_stmt));
        // "for" star_targets "in" star_expressions ":" block else_block?
        let iterator = for_stmt.iter_children();
        let mut iterator = iterator.skip(1);

        self.index_non_block_node(iterator.next().unwrap(), ordered);
        let mut iterator = iterator.skip(1);
        self.index_non_block_node(iterator.next().unwrap(), ordered);

        let mut iterator = iterator.skip(1);
        self.index_block(iterator.next().unwrap(), false);

        if ordered {
            self.index_unordered_references();
        }
        if let Some(else_) = iterator.next() {
            // "else" ":" block
            self.index_block(else_.get_nth_child(2), ordered);
        }
    }

    fn index_while_stmt(&mut self, while_stmt: PyNode<'a>, ordered: bool) {
        debug_assert_eq!(while_stmt.get_type(), Nonterminal(NonterminalType::while_stmt));
        // "while" named_expression ":" block else_block?
        let iterator = while_stmt.iter_children();
        let mut iterator = iterator.skip(1);

        self.index_non_block_node(iterator.next().unwrap(), ordered);
        let mut iterator = iterator.skip(1);
        self.index_non_block_node(iterator.next().unwrap(), false);
        if ordered {
            self.index_unordered_references();
        }
        if let Some(else_) = iterator.next() {
            // "else" ":" block
            self.index_block(else_.get_nth_child(2), ordered);
        }
    }

    fn index_with_stmt(&mut self, with_stmt: PyNode<'a>, ordered: bool) {
        debug_assert_eq!(with_stmt.get_type(), Nonterminal(NonterminalType::with_stmt));
        // with_stmt: "with" ("(" ",".with_item+ ","? ")" | ",".with_item+ )  ":" block
        for child in with_stmt.iter_children() {
            match child.get_type() {
                Nonterminal(NonterminalType::with_item) => {
                    // expression ["as" star_target]
                    self.index_non_block_node(child.get_nth_child(0), ordered);
                    self.index_non_block_node(child.get_nth_child(2), ordered);
                }
                Nonterminal(NonterminalType::block) => self.index_block(child, ordered),
                _ => (),
            }
        }
    }

    fn index_if_stmt(&mut self, if_stmt: PyNode<'a>, ordered: bool) {
        debug_assert_eq!(if_stmt.get_type(), Nonterminal(NonterminalType::if_stmt));
        // "if" named_expression ":" block ("elif" named_expression ":" block)* else_block?

        for child in if_stmt.iter_children().skip(1) {
            match child.get_type() {
                Nonterminal(NonterminalType::named_expression) =>
                    self.index_non_block_node(child, ordered),
                Nonterminal(NonterminalType::block) =>
                    self.index_block(child, ordered),
                Nonterminal(NonterminalType::else_block) =>
                    self.index_block(child.get_nth_child(2), ordered),
                Keyword => (),
                _ => (unreachable!()),
            }
        }
    }

    fn index_try_stmt(&mut self, try_stmt: PyNode<'a>, ordered: bool) {
        debug_assert_eq!(try_stmt.get_type(), Nonterminal(NonterminalType::try_stmt));
        // "try" ":" block (except_block+ else_block? finally_block? | finally_block)
        for child in try_stmt.iter_children() {
            match child.get_type() {
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
                _ => (),
            }
        }
    }

    fn index_class(&mut self, class: PyNode<'a>) {
        // "class" name_definition ["(" [arguments] ")"] ":" block
        debug_assert_eq!(class.get_type(), Nonterminal(NonterminalType::class_def));
        let symbol_table = SymbolTable::default();
        self.with_nested(&symbol_table, |binder| {
            for child in class.iter_children() {
                if child.is_type(Nonterminal(NonterminalType::arguments)) {
                    binder.index_non_block_node(child, true);
                } else if child.is_type(Nonterminal(NonterminalType::block)) {
                    binder.index_block(child, true);
                }
            }
        });
        self.set_complex_value(class, ComplexValue::Class(ClassStorage::new(symbol_table)));
        // Need to first index the class, because the class body does not have access to
        // the class name.
        self.add_redirect_definition(
            class.get_nth_child(1),
            class.index as u32,
        );
    }

    fn index_match_stmt(&mut self, match_stmt: PyNode<'a>, ordered: bool) {
        debug_assert_eq!(match_stmt.get_type(), Nonterminal(NonterminalType::match_stmt));
        // "match" subject_expr ":" Newline Indent case_block+ Dedent
        todo!("match_stmt")
    }

    fn index_non_block_node(&mut self, node: PyNode<'a>, ordered: bool) {
        use NonterminalType::*;
        const SEARCH_NAMES: &[PyNodeType] = &[
            Terminal(TerminalType::Name),
            Nonterminal(lambda),
            Nonterminal(comprehension),
            Nonterminal(dict_comprehension),
        ];
        for n in node.search(SEARCH_NAMES) {
            if n.is_type(Terminal(TerminalType::Name)) {
                let parent = n.get_parent().unwrap();
                if parent.is_type(Nonterminal(name_definition)) {
                    // The types are inferred later.
                    self.add_new_definition(
                        parent,
                        ValueOrReference::new_uncalculated(),
                    )
                } else {
                    self.index_reference(n, parent, ordered);
                }
            } else if n.is_type(Nonterminal(lambda)) {
                self.index_lambda_param_defaults(n, ordered);
                self.unresolved_nodes.push(n);
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
    }

    fn index_comprehension(&mut self, comp: PyNode<'a>, ordered: bool) {
        // comprehension: named_expression for_if_clauses
        // dict_comprehension: dict_key_value for_if_clauses
        let clauses = comp.get_nth_child(1);
        debug_assert_eq!(clauses.get_type(), Nonterminal(NonterminalType::for_if_clauses));
        let mut iterator = clauses.iter_children();

        let first_clause = iterator.next().unwrap();
        // TODO the ordered argument is not used here currently and it should probably be used.
        self.index_comprehension_clause(&mut iterator, first_clause, comp.get_nth_child(0));
    }

    fn index_comprehension_clause(
        &mut self,
        clauses: &mut impl Iterator<Item=PyNode<'a>>,
        mut clause: PyNode<'a>,
        // Either a named_expression or a dict_key_value
        result_node: PyNode<'a>,
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
        self.with_nested(&symbol_table, |binder| {
            binder.index_non_block_node(clause.get_nth_child(1), true);
            if let Some(clause) = clauses.next() {
                binder.index_comprehension_clause(clauses, clause, result_node);
            } else {
                binder.index_non_block_node(result_node, true);
            }
        });
    }

    fn index_function_name_and_param_defaults(&mut self, node: PyNode<'a>, ordered: bool) {
        use NonterminalType::*;
        // function_def: "def" name_definition function_def_parameters return_annotation? ":" block
        for child in node.iter_children() {
            if child.is_type(Nonterminal(parameters)) {
                for n in child.search(&[Nonterminal(annotation), Nonterminal(expression)]) {
                    // expressions are resolved immediately while annotations are inferred at the
                    // end of a module.
                    if n.is_type(Nonterminal(annotation)) {
                        self.unresolved_nodes.push(n.get_nth_child(1));
                    } else {
                        self.index_non_block_node(n, ordered);
                    }
                }
            } else if child.is_type(Nonterminal(return_annotation)) {
                // This is the -> annotation that needs to be resolved at the end of a module.
                self.unresolved_nodes.push(child.get_nth_child(1));
            }
        }
        self.add_value_definition(
            node.get_nth_child(1),
            ValueEnum::LazyInferredFunction,
        );
    }

    pub fn index_function_body(&mut self, func: PyNode<'a>) {
        // "def" name_definition "(" [parameters] ")" ["->" expression] ":" block
        use NonterminalType::*;
        debug_assert_eq!(func.get_type(), Nonterminal(function_def));

        // Function name was indexed already.
        for child in func.iter_children() {
            if child.is_type(Nonterminal(parameters)) {
                for n in child.search(&[Nonterminal(name_definition), Nonterminal(expression)]) {
                    if n.is_type(Nonterminal(name_definition)) {
                        self.add_value_definition(n, ValueEnum::Param);
                    } // defaults and annotations are already indexed
                }
            }
            if child.is_type(Nonterminal(block)) {
               self.index_block(child, true);
            }
        }
        let parent = func.get_parent().unwrap();
        if !parent.is_type(Nonterminal(stmt)) {
            todo!("{:?}", stmt);
        }
        let func_index = func.index as usize;
        self.values_or_references[func_index].set(
            ValueOrReference::new_simple_language_specific(ValueEnum::Function, Locality::Stmt));

        // Avoid overwriting multi definitions
        let mut name_index = func.index as usize + 3;
        if self.values_or_references[name_index].get().get_type() == MultiDefinition {
            name_index -= 1;
        }
        self.values_or_references[name_index].set(
            ValueOrReference::new_redirect(self.file_index, func.index, Locality::Stmt));
    }

    fn index_lambda_param_defaults(&mut self, node: PyNode<'a>, ordered: bool) {
        use NonterminalType::*;
        // lambda: "lambda" [lambda_parameters] ":" expression
        let params = node.get_nth_child(1);
        if params.is_type(Nonterminal(lambda_parameters)) {
            for n in params.search(&[Nonterminal(expression)]) {
                self.index_non_block_node(n, ordered);
            }
        }
    }

    fn index_lambda(&mut self, node: PyNode<'a>) {
        use NonterminalType::*;
        debug_assert_eq!(node.get_type(), Nonterminal(lambda));
        for child in node.iter_children() {
            if child.is_type(Nonterminal(lambda_parameters)) {
                for n in child.search(&[Nonterminal(name_definition), Nonterminal(expression)]) {
                    if n.is_type(Nonterminal(name_definition)) {
                        self.add_value_definition(n, ValueEnum::Param);
                    } // defaults are already indexed
                }
            }
            if child.is_type(Nonterminal(expression)) {
               self.index_non_block_node(child, true);
            }
        }
    }

    fn index_reference(&mut self, name: PyNode<'a>, parent: PyNode<'a>, ordered: bool) {
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
    fn maybe_add_reference(&mut self, name: PyNode<'a>, ordered: bool) {
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
    fn add_reference(&self, name: PyNode<'a>, mut unresolved_name_callback: impl FnMut(PyNode<'a>)) {
        let value = {
            if self.parent_lookup_not_finished {
                if let Some(definition) = self.symbol_table.lookup_symbol(name.get_code()) {
                    ValueOrReference::new_redirect(
                        self.file_index,
                        definition,
                        Locality::File,
                    )
                } else {
                    unresolved_name_callback(name);
                    return
                }
            } else if let Some(definition) = self.lookup_name(name) {
                ValueOrReference::new_redirect(
                    self.file_index,
                    definition,
                    Locality::File,
                )
            } else {
                ValueOrReference::new_missing_or_unknown(
                    self.file_index,
                    Locality::File,
                )
            }
        };
        self.values_or_references[name.index as usize].set(value);
    }

    fn lookup_name(&self, name: PyNode<'a>) -> Option<NodeIndex> {
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
