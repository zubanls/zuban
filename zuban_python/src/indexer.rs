use parsa_python::{PythonNode, PythonNodeType, PythonNonterminalType, PythonTerminalType};
use parsa_python::PythonNodeType::{Nonterminal, Terminal};
use parsa::{Node, NodeIndex};
use crate::file::ValuesOrReferences;
use crate::utils::DefinitionNames;
use crate::database::{InternalValueOrReference, PythonValueEnum, Locality, FileIndex};

pub struct IndexerState<'a, 'b> {
    definition_names: &'a DefinitionNames,
    scope_definition_names: DefinitionNames,
    values_or_references: &'a ValuesOrReferences,
    unordered_references: Vec<PythonNode<'a>>,
    unresolved_nodes: Vec<PythonNode<'a>>,
    file_index: FileIndex,
    is_global_scope: bool,
    parent: Option<&'b IndexerState<'a, 'b>>,
}

impl<'a, 'b> IndexerState<'a, 'b> {
    pub fn new(
        definition_names: &'a DefinitionNames,
        values_or_references: &'a ValuesOrReferences,
        file_index: FileIndex,
        is_global_scope: bool,
        parent: Option<&'b IndexerState<'a, 'b>>,
    ) -> Self {
        IndexerState {
            definition_names: definition_names,
            scope_definition_names: Default::default(),
            values_or_references: values_or_references,
            unordered_references: vec![],
            unresolved_nodes: vec![],
            file_index,
            is_global_scope,
            parent,
        }
    }

    fn new_nested(&self) -> IndexerState<'a, '_> {
        IndexerState::new(
            self.definition_names, self.values_or_references,
            self.file_index, false, Some(self))
    }

    fn add_new_definition(&self, name_def: PythonNode<'a>, value: InternalValueOrReference) {
        debug_assert!(name_def.is_type(Nonterminal(PythonNonterminalType::name_definition)));
        let name = name_def.get_nth_child(0);
        self.definition_names.add_definition(name);
        self.values_or_references[name.index].set(value);
    }

    fn add_value_definition(&mut self, name_def: PythonNode<'a>, type_: PythonValueEnum) {
        self.add_new_definition(
            name_def,
            InternalValueOrReference::new_simple_language_specific(
                type_,
                Locality::Stmt,
                false,
                self.is_global_scope,
            )
        );
    }

    fn add_redirect_definition(&mut self, name_def: PythonNode<'a>, node_index: NodeIndex) {
        self.add_new_definition(
            name_def,
            InternalValueOrReference::new_redirect(
                self.file_index,
                node_index,
                Locality::Stmt,
                false,
                self.is_global_scope,
            )
        );
    }

    pub fn index_block(&mut self, block_node: PythonNode<'a>, ordered: bool) {
        // Theory:
        // - while_stmt, for_stmt: ignore order (at least mostly)
        // - match_stmt, if_stmt, try_stmt (only in coresponding blocks and after)
        // - sync_for_if_clause: reversed order and only in scope
        // - lambda: only in scope
        // - function_def, class_def: ignore
        use PythonNonterminalType::*;
        for child in block_node.iter_children() {
            if child.is_type(Nonterminal(simple_stmts)) {
                self.index_non_block_node(child, ordered);
            } else if child.is_type(Nonterminal(function_def)) {
                if !self.is_global_scope {
                    // Has to be resolved, because we otherwise have no knowledge about globals
                    self.unresolved_nodes.push(child);
                }
                self.index_function_name_and_param_defaults(child, ordered);
            } else if child.is_type(Nonterminal(class_def)) {
                self.new_nested().index_class(child);
            } else if child.is_type(Nonterminal(decorated)) {
                let not_decorated = child.get_nth_child(1);
                if not_decorated.is_type(Nonterminal(function_def)) {
                    self.add_value_definition(
                        not_decorated.get_nth_child(1),
                        PythonValueEnum::LazyInferredFunction,
                    );
                } else if not_decorated.is_type(Nonterminal(class_def)) {
                    self.add_value_definition(
                        not_decorated.get_nth_child(1),
                        PythonValueEnum::LazyInferredClass,
                    );
                } else {
                    debug_assert!(not_decorated.is_type(Nonterminal(async_function_def)));
                    self.add_value_definition(
                        not_decorated.get_nth_child(0).get_nth_child(1),
                        PythonValueEnum::LazyInferredClass,
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
                        PythonValueEnum::LazyInferredFunction,
                    );
                } else if inner.is_type(Nonterminal(for_stmt)) {
                    self.index_for_stmt(inner, ordered);
                } else if inner.is_type(Nonterminal(with_stmt)) {
                    self.index_with_stmt(child, ordered);
                }
            } else {
                assert_eq!(child.get_type(), Terminal(PythonTerminalType::Newline));
            }
        }

        self.index_unordered_references();

        while let Some(n) = self.unresolved_nodes.pop() {
            if n.is_type(Nonterminal(comprehension)) {
                todo!("generator comprehension");
            } else if n.is_type(Nonterminal(lambda)) {
                self.new_nested().index_lambda(n);
            } else if n.is_type(Nonterminal(expression)) {
                // Typically annotations
                self.index_non_block_node(n, true);
            } else if n.is_type(Nonterminal(function_def)) {
                self.new_nested().index_function(n);
            } else {
                unreachable!();
            }
        }
    }

    fn index_for_stmt(&mut self, for_stmt: PythonNode<'a>, ordered: bool) {
        debug_assert_eq!(for_stmt.get_type(), Nonterminal(PythonNonterminalType::for_stmt));
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

    fn index_while_stmt(&mut self, while_stmt: PythonNode<'a>, ordered: bool) {
        debug_assert_eq!(while_stmt.get_type(), Nonterminal(PythonNonterminalType::while_stmt));
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

    fn index_with_stmt(&mut self, with_stmt: PythonNode<'a>, ordered: bool) {
        debug_assert_eq!(with_stmt.get_type(), Nonterminal(PythonNonterminalType::with_stmt));
        // with_stmt: "with" ("(" ",".with_item+ ","? ")" | ",".with_item+ )  ":" block
        for child in with_stmt.iter_children() {
            match child.get_type() {
                Nonterminal(PythonNonterminalType::with_item) => {
                    // expression ["as" star_target]
                    self.index_non_block_node(child.get_nth_child(0), ordered);
                    self.index_non_block_node(child.get_nth_child(2), ordered);
                }
                Nonterminal(PythonNonterminalType::block) => self.index_block(child, ordered),
                _ => (),
            }
        }
    }

    fn index_if_stmt(&mut self, if_stmt: PythonNode<'a>, ordered: bool) {
        debug_assert_eq!(if_stmt.get_type(), Nonterminal(PythonNonterminalType::if_stmt));
        // "if" named_expression ":" block ("elif" named_expression ":" block)* else_block?
    }

    fn index_try_stmt(&mut self, try_stmt: PythonNode<'a>, ordered: bool) {
        debug_assert_eq!(try_stmt.get_type(), Nonterminal(PythonNonterminalType::try_stmt));
        // "try" ":" block (except_block+ else_block? finally_block? | finally_block)
        for child in try_stmt.iter_children() {
            match child.get_type() {
                Nonterminal(PythonNonterminalType::block) => self.index_block(child, ordered),
                Nonterminal(PythonNonterminalType::except_block) => {
                    // except_clause ":" block
                    let except_clause = child.get_nth_child(0);
                    // except_clause: "except" [expression ["as" name_definition]]
                    for child in except_clause.iter_children() {
                        if child.is_type(Nonterminal(PythonNonterminalType::expression)) {
                            self.index_non_block_node(child, ordered);
                        } else if child.is_type(Nonterminal(PythonNonterminalType::name_definition)) {
                            self.add_redirect_definition(child, except_clause.index as u32);
                        }
                    }
                    // block
                    self.index_block(child.get_nth_child(2), ordered)
                }
                Nonterminal(PythonNonterminalType::finally_block)
                | Nonterminal(PythonNonterminalType::else_block) => {
                    // "finally" ":" block
                    // "else" ":" block
                    self.index_block(child.get_nth_child(2), ordered)
                }
                _ => (),
            }
        }
    }

    fn index_class(&mut self, class: PythonNode<'a>) {
        // "class" name_definition ["(" [arguments] ")"] ":" block
        debug_assert_eq!(class.get_type(), Nonterminal(PythonNonterminalType::class_def));
        for child in class.iter_children() {
            if child.is_type(Nonterminal(PythonNonterminalType::arguments)) {
                self.index_non_block_node(child, true);
            } else if child.is_type(Nonterminal(PythonNonterminalType::block)) {
                self.new_nested().index_block(child, true);
            }
        }
        // Need to first index the class, because the class body does not have access to
        // the class name.
        self.add_value_definition(
            class.get_nth_child(1),
            PythonValueEnum::LazyInferredClass,
        );
    }

    fn index_match_stmt(&mut self, match_stmt: PythonNode<'a>, ordered: bool) {
        debug_assert_eq!(match_stmt.get_type(), Nonterminal(PythonNonterminalType::match_stmt));
        // "match" subject_expr ":" Newline Indent case_block+ Dedent
        todo!("match_stmt")
    }

    fn index_non_block_node(&mut self, node: PythonNode<'a>, ordered: bool) {
        use PythonNonterminalType::*;
        const SEARCH_NAMES: &'static [PythonNodeType] = &[
            Terminal(PythonTerminalType::Name),
            Nonterminal(lambda),
            Nonterminal(comprehension),
            Nonterminal(dict_comprehension),
        ];
        for n in node.search(SEARCH_NAMES) {
            if n.is_type(Terminal(PythonTerminalType::Name)) {
                let parent = n.get_parent().unwrap();
                // name_definitions are resolved later.
                if !parent.is_type(Nonterminal(name_definition)) {
                    self.index_reference(n, parent, ordered);
                }
            } else {
                if n.is_type(Nonterminal(lambda)) {
                    self.index_lambda_param_defaults(n, ordered);
                    self.unresolved_nodes.push(n);
                } else {
                    // Index the first expression of a comprehension, which is always executed
                    // in the current scope.
                    // comprehension: named_expression for_if_clauses
                    // dict_comprehension: dict_key_value for_if_clauses
                    let clauses = n.get_nth_child(1);
                    debug_assert_eq!(clauses.get_type(), Nonterminal(for_if_clauses));

                    // for_if_clauses: async_for_if_clause+
                    let mut for_if_clause = clauses.get_nth_child(0);
                    if for_if_clause.is_type(Nonterminal(async_for_if_clause)) {
                        // async_for_if_clause:? ["async"] sync_for_if_clause
                        for_if_clause = for_if_clause.get_nth_child(1);
                    }

                    if clauses.iter_children().count() > 1 {
                        todo!("comprehensions not handled yet");
                    }

                    // sync_for_if_clause: "for" star_targets "in" disjunction comp_if*
                    debug_assert_eq!(for_if_clause.get_type(), Nonterminal(sync_for_if_clause));
                    self.index_non_block_node(for_if_clause.get_nth_child(3), ordered);

                    todo!("we need to add GENERATOR comprehensions here");
                }
            }
        }
    }

    fn index_function_name_and_param_defaults(&mut self, node: PythonNode<'a>, ordered: bool) {
        use PythonNonterminalType::*;
        // function_def: "def" name_definition "(" [parameters] ")" ["->" expression] ":" block
        for child in node.iter_children() {
            if child.is_type(Nonterminal(parameters)) {
                for n in child.search(&[Nonterminal(annotation), Nonterminal(expression)]) {
                    // expressions are resolved immediately while annotations are inferred at the
                    // end of a module.
                    if n.is_type(Nonterminal(annotation)) {
                        self.unresolved_nodes.push(n);
                    } else {
                        self.index_non_block_node(n, ordered);
                    }
                }
            } else if child.is_type(Nonterminal(expression)) {
                // This is the -> annotation that needs to be resolved at the end of a module.
                self.unresolved_nodes.push(child);
            }
        }
        self.add_value_definition(
            node.get_nth_child(1),
            PythonValueEnum::LazyInferredFunction,
        );
    }

    pub fn index_function(&mut self, func: PythonNode<'a>) {
        // "def" name_definition "(" [parameters] ")" ["->" expression] ":" block
        use PythonNonterminalType::*;
        debug_assert_eq!(func.get_type(), Nonterminal(function_def));

        // Function name was indexed already.
        for child in func.iter_children() {
            if child.is_type(Nonterminal(parameters)) {
                for n in child.search(&[Nonterminal(name_definition), Nonterminal(expression)]) {
                    if n.is_type(Nonterminal(name_definition)) {
                        self.add_value_definition(n, PythonValueEnum::Param);
                    } // defaults and annotations are already indexed
                }
            }
            if child.is_type(Nonterminal(block)) {
               self.index_block(child, true);
            }
        }
    }

    fn index_lambda_param_defaults(&mut self, node: PythonNode<'a>, ordered: bool) {
        use PythonNonterminalType::*;
        // lambda: "lambda" [lambda_parameters] ":" expression
        let params = node.get_nth_child(1);
        if params.is_type(Nonterminal(lambda_parameters)) {
            for n in params.search(&[Nonterminal(expression)]) {
                self.index_non_block_node(n, ordered);
            }
        }
    }

    fn index_lambda(&mut self, node: PythonNode<'a>) {
        use PythonNonterminalType::*;
        debug_assert_eq!(node.get_type(), Nonterminal(lambda));
        for child in node.iter_children() {
            if child.is_type(Nonterminal(lambda_parameters)) {
                for n in child.search(&[Nonterminal(name_definition), Nonterminal(expression)]) {
                    if n.is_type(Nonterminal(name_definition)) {
                        self.add_value_definition(n, PythonValueEnum::Param);
                    } // defaults are already indexed
                }
            }
            if child.is_type(Nonterminal(expression)) {
               self.index_non_block_node(child, true);
            }
        }
    }

    fn index_reference(&mut self, name: PythonNode<'a>, parent: PythonNode<'a>, ordered: bool) {
        use PythonNonterminalType::*;
        debug_assert_eq!(name.get_type(), Terminal(PythonTerminalType::Name));
        if parent.is_type(Nonterminal(atom)) {
            self.maybe_add_reference(name, ordered);
        } else if parent.is_type(Nonterminal(global_stmt)) {
            //self.maybe_add_reference(name, ordered);
            // TODO global
        } else if parent.is_type(Nonterminal(nonlocal_stmt)) {
            // TODO nonlocal
        }
        // All other names are not references or part of imports and should be resolved later.
    }

    #[inline]
    fn maybe_add_reference(&mut self, name: PythonNode<'a>, ordered: bool) {
        if ordered {
            self.add_reference(name);
        } else {
            self.unordered_references.push(name);
        }
    }

    #[inline]
    fn add_reference(&self, name: PythonNode<'a>) {
        let value = {
            if let Some(definition) = self.lookup_name(name) {
                InternalValueOrReference::new_redirect(
                    self.file_index,
                    definition,
                    Locality::File,
                    false,
                    self.is_global_scope,
                )
            } else {
                InternalValueOrReference::new_missing_or_unknown(
                    self.file_index,
                    Locality::File,
                )
            }
        };
        self.values_or_references[name.index].set(value);
    }

    fn lookup_name(&self, name: PythonNode<'a>) -> Option<NodeIndex> {
        if self.is_global_scope {
            self.definition_names.lookup_global_definition(
                self.values_or_references,
                name.get_code(),
            )
        } else {
            self.definition_names
                .lookup_definition(name.get_code())
                .or_else(|| self.parent.and_then(|parent| parent.lookup_name(name)))
        }
    }

    fn index_unordered_references(&mut self) {
        for &name in &self.unordered_references {
            self.add_reference(name);
        }
        self.unordered_references.truncate(0);
    }

}
