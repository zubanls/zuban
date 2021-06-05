use parsa_python::{PythonNode, PythonNodeType, PythonNonterminalType, PythonTerminalType};
use parsa_python::PythonNodeType::{Nonterminal, Terminal};
use parsa::{Node, NodeIndex};
use crate::file::{DefinitionNames, ValuesOrReferences};
use crate::utils::HashableRawStr;
use crate::database::{InternalValueOrReference, PythonValueEnum, Locality, FileIndex};

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
            is_global_scope,
        }
    }

    fn add_new_definition(&self, name_def: PythonNode, value: InternalValueOrReference) {
        debug_assert!(name_def.is_type(Nonterminal(PythonNonterminalType::name_definition)));
        let name = name_def.get_nth_child(0);
        self.definition_names.push_to_vec(HashableRawStr::new(name.get_code()), name.index as u32);
        self.values_or_references[name.index].set(value);
    }

    fn add_value_definition(&self, name_def: PythonNode, type_: PythonValueEnum) {
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

    fn add_redirect_definition(&self, name_def: PythonNode, node_index: NodeIndex) {
        self.add_new_definition(
            name_def,
            InternalValueOrReference::new_redirect(
                FileIndex(0), // TODO
                node_index,
                Locality::Stmt,
                false,
                self.is_global_scope,
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
                self.index_non_block_node(child, ordered);
            } else if child.is_type(Nonterminal(function_def)) {
                self.add_value_definition(
                    child.get_nth_child(1),
                    PythonValueEnum::LazyInferredFunction,
                );
            } else if child.is_type(Nonterminal(class_def)) {
                self.add_value_definition(
                    child.get_nth_child(1),
                    PythonValueEnum::LazyInferredClass,
                );
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
        let iterator = while_stmt.iter_children();
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

    fn index_if_stmt(&self, if_stmt: PythonNode, ordered: bool) {
        debug_assert_eq!(if_stmt.get_type(), Nonterminal(PythonNonterminalType::if_stmt));
        // "if" named_expression ":" block ("elif" named_expression ":" block)* else_block?
    }

    fn index_try_stmt(&self, try_stmt: PythonNode, ordered: bool) {
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

    fn index_match_stmt(&self, match_stmt: PythonNode, ordered: bool) {
        debug_assert_eq!(match_stmt.get_type(), Nonterminal(PythonNonterminalType::match_stmt));
        // "match" subject_expr ":" Newline Indent case_block+ Dedent
        todo!()
    }

    fn index_star_targets(&self, node: PythonNode, ordered: bool) {
    }

    fn index_non_block_node(&self, node: PythonNode, ordered: bool) {
        use PythonNonterminalType::*;
        const SEARCH_NAMES: &'static [PythonNodeType] = &[
            Terminal(PythonTerminalType::Name),
            Nonterminal(PythonNonterminalType::lambda),
            Nonterminal(PythonNonterminalType::comprehension),
            Nonterminal(PythonNonterminalType::dict_comprehension),
        ];
        for node in node.search(SEARCH_NAMES) {
            node.get_parent();
        }
        /*
        const SEARCH_DEFINITIONS: &'static [i32] = &[
            dotted_as_name
            import_from_as_name
            except_clause
            pattern_capture_target
            named_expression

            t_atom
            single_target
            star_atom
            t_primary
        ];
        */
    }
}
