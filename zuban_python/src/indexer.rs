use parsa_python::{PythonNode, PythonNonterminalType, PythonTerminalType};
use parsa_python::PythonNodeType::{Nonterminal, Terminal};
use parsa::Node;
use crate::file::{DefinitionNames, ValuesOrReferences};
use crate::utils::HashableRawStr;
use crate::database::{InternalValueOrReference, PythonValueEnum, Locality};

pub struct IndexerState<'a> {
    definition_names: &'a DefinitionNames,
    values_or_references: &'a ValuesOrReferences,
    unresolved_references: Vec<PythonNode<'a>>,
    unresolved_nodes: Vec<PythonNode<'a>>,
    is_global_scope: bool,
}

impl<'a> IndexerState<'a> {
    pub fn new(definition_names: &'a DefinitionNames, values_or_references: &'a ValuesOrReferences, is_global_scope: bool) -> Self {
        IndexerState {
            definition_names: definition_names,
            values_or_references: values_or_references,
            unresolved_references: vec![],
            unresolved_nodes: vec![],
            is_global_scope: true,
        }
    }

    fn add_new_definition(&self, name_def: PythonNode, type_: PythonValueEnum, is_global_scope: bool) {
        debug_assert!(name_def.is_type(Nonterminal(PythonNonterminalType::name_definition)));
        let name = name_def.get_nth_child(0);
        self.definition_names.push_to_vec(HashableRawStr::new(name.get_code()), name.index as u32);
        self.values_or_references[name.index].set(
            InternalValueOrReference::new_simple_language_specific(
                type_,
                Locality::Stmt,
                false,
                is_global_scope,
            )
        );
    }

    pub fn index_block(&self, block_node: PythonNode, ordered: bool) {
        // Theory:
        // - while_stmt, for_stmt: ignore order (at least mostly)
        // - match_stmt, if_stmt, try_stmt (only in coresponding blocks and after)
        // - sync_for_if_clause: reversed order and only in scope
        // - lambda: only in scope
        // - function_def, class_def: ignore
        use PythonNonterminalType::*;
        for child in block_node.iter_children() {
            if child.is_type(Nonterminal(simple_stmts)) {
            } else if child.is_type(Nonterminal(function_def)) {
                self.add_new_definition(
                    child.get_nth_child(1),
                    PythonValueEnum::LazyInferredFunction,
                    self.is_global_scope,
                );
            } else if child.is_type(Nonterminal(class_def)) {
                self.add_new_definition(
                    child.get_nth_child(1),
                    PythonValueEnum::LazyInferredClass,
                    self.is_global_scope,
                );
            } else if child.is_type(Nonterminal(decorated)) {
                let not_decorated = child.get_nth_child(1);
                if not_decorated.is_type(Nonterminal(function_def)) {
                    self.add_new_definition(
                        not_decorated.get_nth_child(1),
                        PythonValueEnum::LazyInferredFunction,
                        self.is_global_scope,
                    );
                } else if not_decorated.is_type(Nonterminal(class_def)) {
                    self.add_new_definition(
                        not_decorated.get_nth_child(1),
                        PythonValueEnum::LazyInferredClass,
                        self.is_global_scope,
                    );
                } else {
                    debug_assert!(not_decorated.is_type(Nonterminal(async_function_def)));
                    self.add_new_definition(
                        not_decorated.get_nth_child(0).get_nth_child(1),
                        PythonValueEnum::LazyInferredClass,
                        self.is_global_scope,
                    );
                }
            } else if child.is_type(Nonterminal(while_stmt)) {
                self.index_while_stmt(child, ordered);
            } else if child.is_type(Nonterminal(for_stmt)){
                self.index_for_stmt(child, ordered);
            } else if child.is_type(Nonterminal(with_stmt)){
                self.index_with_stmt(child, ordered);
            } else if child.is_type(Nonterminal(async_stmt)) {
                let iterator = child.iter_children();
                let mut iterator = iterator.skip(1);
                let inner = iterator.next().unwrap();
                if inner.is_type(Nonterminal(function_def)) {
                    self.add_new_definition(
                        inner.get_nth_child(1),
                        PythonValueEnum::LazyInferredFunction,
                        self.is_global_scope,
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
    }

    fn index_for_stmt(&self, for_stmt: PythonNode, ordered: bool) {
        debug_assert_eq!(for_stmt.get_type(), Nonterminal(PythonNonterminalType::for_stmt));
        // "for" star_targets "in" star_expressions ":" block else_block?
        let iterator = for_stmt.iter_children();
        let mut iterator = iterator.skip(1);

        self.index_star_targets(iterator.next().unwrap(), ordered);
        let mut iterator = iterator.skip(1);
        self.index_non_block_node(iterator.next().unwrap(), ordered);
        let mut iterator = iterator.skip(1);
        self.index_block(iterator.next().unwrap(), ordered);
        if let Some(else_) = iterator.next() {
            // "else" ":" block
            self.index_block(else_.get_nth_child(2), ordered);
        }
    }

    fn index_while_stmt(&self, while_stmt: PythonNode, ordered: bool) {
        debug_assert_eq!(while_stmt.get_type(), Nonterminal(PythonNonterminalType::while_stmt));
        // "while" named_expression ":" block else_block?
        let iterator = for_stmt.iter_children();
        let mut iterator = iterator.skip(1);

        self.index_non_block_node(iterator.next().unwrap(), ordered);
        let mut iterator = iterator.skip(1);
        self.index_non_block_node(iterator.next().unwrap(), true);
        if let Some(else_) = iterator.next() {
            // "else" ":" block
            self.index_block(else_.get_nth_child(2), ordered);
        }
    }

    fn index_with_stmt(&self, with_stmt: PythonNode, ordered: bool) {
        debug_assert_eq!(with_stmt.get_type(), Nonterminal(PythonNonterminalType::with_stmt));
        // with_stmt: "with" ("(" ",".with_item+ ","? ")" | ",".with_item+ )  ":" block
        for child in with_stmt.iter_children() {
            match child.get_type() {
                Nonterminal(PythonNonterminalType::with_item) => {
                    // expression ["as" star_target]
                    self.index_non_block_node(child.get_nth_child(0), ordered);
                    self.index_star_targets(child.get_nth_child(2), ordered);
                }
                Nonterminal(PythonNonterminalType::block) => self.index_block(child, ordered),
                _ => (),
            }
        }
    }

    fn index_star_targets(&self, node: PythonNode, ordered: bool) {
    }

    fn index_non_block_node(&self, node: PythonNode, ordered: bool) {
    }
}
