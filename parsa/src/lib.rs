#![allow(unused)]
extern crate lazy_static;

mod automaton;
mod backtracking;
mod grammar;

#[macro_export]
pub use lazy_static::lazy_static;
pub use std::collections::HashSet;
pub use std::io::Bytes;
pub use std::marker::PhantomData;
pub use std::mem;

pub use automaton::{
    new_fast_hash_map, FastHashMap, InternalNonterminalType, InternalSquashedType,
    InternalStrToNode, InternalStrToToken, InternalTerminalType, Rule, NODE_START,
};
pub use grammar::{
    CodeIndex, CodeLength, Grammar, InternalNode, InternalTree, NodeIndex, Token, Tokenizer,
};

#[macro_export]
macro_rules! __filter_labels_and_create_node_set {
    ([$($args:tt)+], $label:ident: $($rule:tt)+) => {
        $crate::__filter_labels_and_create_node_set!([$($args)+, $label], $($rule)+);
    };
    ($args:tt, $not_label:tt $($rule:tt)*) => {
        //compile_error!(stringify!($($rule:tt)*));
        $crate::__filter_labels_and_create_node_set!($args, $($rule)*);
    };
    ([$($args:tt)+],) => {
        $crate::__create_type_set!($($args)+);
    };
}

#[macro_export]
macro_rules! __create_type_set {
    (enum $EnumName:ident, $Map:path, $Type:path, $start:expr, rules_to_nodes=$($rule:tt)*) => {
        $crate::__filter_labels_and_create_node_set!([enum $EnumName, $Map, $Type, $start], $($rule)*);
    };
    (enum $EnumName:ident, $Map:path, $Type:path, $start:expr,
     $first_entry:ident, $($entry:ident),*) => {
        #[allow(non_camel_case_types)]
        #[derive(Copy, Clone, Debug, Eq, PartialEq)]
        #[repr(u16)]
        pub enum $EnumName {
            $first_entry = $start,
            $($entry),*
        }

        impl $EnumName {
            pub fn map() -> &'static $Map {
                #[macro_use]
                $crate::lazy_static! {
                    static ref HASHMAP: $Map = {
                        let mut m = $crate::new_fast_hash_map();
                        m.insert(
                            stringify!($first_entry),
                            $Type($EnumName::$first_entry as u16)
                        );
                        $(m.insert(
                              stringify!($entry),
                              $Type($EnumName::$entry as u16)
                          );
                        )*
                        m
                    };
                }
                &*HASHMAP
            }

            pub fn as_str(x: $EnumName) -> &'static str {
                #[macro_use]
                $crate::lazy_static! {
                    static ref HASHMAP: $crate::FastHashMap<u16, &'static str> = {
                        let mut m = $crate::new_fast_hash_map();
                        m.insert($EnumName::$first_entry as u16, stringify!($first_entry));
                        $(m.insert($EnumName::$entry as u16, stringify!($entry));)*;
                        m
                    };
                }
                HASHMAP[&(x as u16)]
            }
        }
    }
}

#[macro_export]
macro_rules! create_terminals {
    (struct $Token:ident, enum $TerminalType:ident, [$($entry:ident),*]) => {
        $crate::__create_type_set!(enum $TerminalType, $crate::InternalStrToToken,
                                   $crate::InternalTerminalType, 0, $($entry),*);

        #[derive(Debug, Copy, Clone)]
        pub struct $Token {
            start_index: $crate::CodeIndex,
            length: $crate::CodeLength,
            type_: $TerminalType,
            can_contain_syntax: bool,
        }

        impl $crate::Token for $Token {
            fn start_index(&self) -> u32 {
                self.start_index
            }

            fn length(&self) -> u32 {
                self.length
            }

            fn type_(&self) -> $crate::InternalTerminalType {
                $crate::InternalTerminalType(self.type_ as u16)
            }

            fn can_contain_syntax(&self) -> bool{
                self.can_contain_syntax
            }
        }
    }
}

#[macro_export]
macro_rules! __create_node {
    ($Tree:ident, struct $Node:ident, enum $NodeType:ident, enum $NonterminalType:ident,
            $TerminalType:ident, [$($entry:tt)*]) => {
        $crate::__create_type_set!(enum $NonterminalType, $crate::InternalStrToNode,
                                   $crate::InternalNonterminalType, $crate::NODE_START, $($entry)*);

        #[derive(Debug, PartialEq, Eq, Copy, Clone)]
        pub enum $NodeType{
            Nonterminal($NonterminalType),
            Terminal($TerminalType),
            Keyword,
            ErrorNonterminal($NonterminalType),
            ErrorTerminal($TerminalType),
            ErrorKeyword,
        }

        impl $NodeType {
            #[inline]
            fn to_internal(self) -> $crate::InternalSquashedType {
                match self {
                    Self::Nonterminal(t) =>
                        $crate::InternalSquashedType(t as u16),
                    Self::Terminal(t) =>
                        $crate::InternalSquashedType(t as u16),
                    Self::ErrorNonterminal(t) =>
                        $crate::InternalSquashedType(t as u16).set_error_recovery_bit(),
                    Self::ErrorTerminal(t) =>
                        $crate::InternalSquashedType(t as u16).set_error_recovery_bit(),
                    Self::Keyword | Self::ErrorKeyword =>
                        panic!("It's not possible to reverse keyword types"),
                }
            }
        }

        #[derive(Clone, Copy)]
        pub struct $Node<'a> {
            internal_tree: &'a $crate::InternalTree,
            pub index: $crate::NodeIndex,
            internal_node: &'a $crate::InternalNode,
        }

        impl<'a> $Node<'a> {
            fn new(
                internal_tree: &'a $crate::InternalTree,
                index: $crate::NodeIndex,
                internal_node: &'a $crate::InternalNode
            ) -> Self {
                Self {internal_tree, index, internal_node}
            }

            pub fn as_code(&self) -> &'a str {
                self.code_slice(self.internal_node.start_index, self.internal_node.length)
            }

            pub fn prefix(&self) -> &'a str {
                let start;
                if self.index == 0 {
                    start = 0;
                } else {
                    start = self.internal_tree.nodes[self.index as usize - 1].start_index;
                }
                let string = self.code_slice(start, self.internal_node.start_index);
                string
            }

            pub fn suffix(&self) -> &'a str {
                for node in &self.internal_tree.nodes[self.index as usize..] {
                    if node.start_index >= self.internal_node.start_index + self.internal_node.length {
                        let start = self.internal_node.start_index + self.internal_node.length;
                        return self.code_slice(
                            start,
                            node.start_index - start,
                        );
                    }
                }
                return ""
            }

            pub fn start(&self) -> u32 {
                self.internal_node.start_index
            }

            pub fn end(&self) -> u32 {
                self.start() + self.length()
            }

            pub fn length(&self) -> u32 {
                self.internal_node.length
            }

            pub fn is_leaf(&self) -> bool {
                self.internal_node.type_.is_leaf()
            }

            fn code_slice(&self, index: $crate::CodeIndex, length: $crate::CodeLength) -> &'a str {
                use std::str;
                // Can be unsafe, because the input of the parse function is a
                // String that is copied to the internal tree.
                unsafe {str::from_utf8_unchecked(&self.internal_tree.code.as_bytes()[
                    index as usize..index as usize + length as usize
                ])}
            }

            pub fn iter_children(&self) -> SiblingIterator<'a> {
                let next_index;
                let ended = self.is_leaf();
                if ended {
                    next_index = 0;
                } else {
                    next_index = self.index + 1;
                }
                SiblingIterator {
                    internal_tree: self.internal_tree,
                    next_index,
                    ended,
                }
            }

            pub fn nth_child(&self, index: usize) -> $Node<'a> {
                debug_assert!(!self.is_leaf(), "Unexpected Leaf: {:?}", self.type_());
                self.iter_children().skip(index).next().expect("There is no child")
            }

            pub fn next_sibling(&self) -> Option<$Node<'a>> {
                (self.internal_node.next_node_offset != 0).then(|| {
                    let index = self.index + self.internal_node.next_node_offset;
                    let n = &self.internal_tree.nodes[index as usize];
                    Self {
                        internal_tree: self.internal_tree,
                        index,
                        internal_node: n
                    }
                })
            }

            pub fn previous_sibling(&self) -> Option<$Node<'a>> {
                for (i, n) in self.internal_tree.nodes[..self.index as usize].iter().rev().enumerate() {
                    let i = i as $crate::NodeIndex + 1;
                    let offset = n.next_node_offset;
                    if offset == i {
                        return Some(Self {
                            internal_tree: self.internal_tree,
                            index: self.index - i,
                            internal_node: n
                        });
                    } else if (offset > i) {
                        debug_assert!(!n.type_.is_leaf());
                        return None
                    }
                }
                None
            }

            pub fn is_error_recovery_node(&self) -> bool {
                self.internal_node.type_.is_error_recovery()
            }

            pub fn parent(&self) -> Option<$Node<'a>> {
                let mut sibling_i = 0;  // Note that i and sibling_i are reversed.
                for (i, n) in self.internal_tree.nodes[..self.index as usize].iter().rev().enumerate() {
                    let i = i as $crate::NodeIndex + 1;
                    let offset = n.next_node_offset;
                    if (offset > i || offset == 0 && i == sibling_i + 1) && !n.type_.is_leaf() {
                        return Some(Self {
                            internal_tree: self.internal_tree,
                            index: self.index - i,
                            internal_node: n
                        });
                    }
                    if sibling_i + offset == i {
                        sibling_i = i;
                    }
                }
                None
            }

            #[inline]
            pub fn parent_until(&self, types: &'static [$NodeType]) -> Option<$Node<'a>> {
                let mut node = self.parent();
                while let Some(n) = node {
                    for &t in types {
                        if n.is_type(t) {
                            return node
                        }
                    }
                    node = n.parent();
                }
                None
            }

            pub fn search(&self, types: &'static [$NodeType]) -> SearchIterator<'a> {
                assert!(!self.is_leaf(), "Unexpected Leaf: {:?}", self.type_());
                SearchIterator {
                    internal_tree: self.internal_tree,
                    next_index: self.index,
                    end_code_index: self.end(),
                    search_types: types,
                }
            }

            pub fn previous_leaf(&self) -> Option<$Node<'a>> {
                for (index, node) in self.internal_tree.nodes[..self.index as usize].iter().enumerate().rev() {
                    if node.type_.is_leaf() {
                        return Some($Node {
                            internal_tree: &self.internal_tree,
                            internal_node: node,
                            index: index as $crate::NodeIndex,
                        });
                    }
                }
                return None
            }

            pub fn next_leaf(&self) -> Option<$Node<'a>> {
                if let Some(slice) = self.internal_tree.nodes.get(self.index as usize + 1..) {
                    for (index, node) in slice.iter().enumerate() {
                        if node.type_.is_leaf() {
                            return Some($Node {
                                internal_tree: &self.internal_tree,
                                internal_node: node,
                                index: index as $crate::NodeIndex,
                            });
                        }
                    }
                }
                return None
            }

            pub fn type_(&self) -> $NodeType {
                let f = |type_: $crate::InternalSquashedType| unsafe {$crate::mem::transmute(type_)};
                let g = |type_: $crate::InternalSquashedType| unsafe {$crate::mem::transmute(type_)};
                if self.is_error_recovery_node() {
                    if self.is_leaf() {
                        let t = self.internal_node.type_.remove_error_recovery_bit();
                        if t.0 as usize >= $TerminalType::map().len() {
                            $NodeType::ErrorKeyword
                        } else {
                            $NodeType::ErrorTerminal(f(t))
                        }
                    } else {
                        $NodeType::ErrorNonterminal(g(self.internal_node.type_.remove_error_recovery_bit()))
                    }
                } else {
                    if self.is_leaf() {
                        // TODO this should probably be something like is keyword
                        if self.internal_node.type_.0 as usize >= $TerminalType::map().len() {
                            $NodeType::Keyword
                        } else {
                            $NodeType::Terminal(f(self.internal_node.type_))
                        }
                    } else {
                        $NodeType::Nonterminal(g(self.internal_node.type_))
                    }
                }
            }

            pub fn is_type(&self, type_: $NodeType) -> bool {
                self.internal_node.type_ == type_.to_internal()
            }

            pub fn type_str(&self) -> String {
                // Not a fast API, should probably only be used for tests.
                match self.type_() {
                    $NodeType::Nonterminal(t) => $NonterminalType::as_str(t).to_owned(),
                    $NodeType::Terminal(t) => $TerminalType::as_str(t).to_owned(),
                    $NodeType::Keyword => "Keyword".to_owned(),
                    $NodeType::ErrorNonterminal(t) => format!("Error({})", $NonterminalType::as_str(t)),
                    $NodeType::ErrorTerminal(t) => format!("Error({})", $TerminalType::as_str(t)),
                    $NodeType::ErrorKeyword => "Error(Keyword)".to_owned(),
                }
            }
        }

        impl std::fmt::Debug for $Node<'_> {
            fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
                let mut code = self.as_code();
                let x;
                if code.len() > 40 {
                    x = code[..40].to_owned() + "...";
                    code = &x;
                }
                let until_code = &self.internal_tree.code.as_ref()[..self.start() as usize];
                // This is pretty slow, but should be fine, because this is only the Debug
                // implementation.
                let line = until_code.chars().filter(|&c| c == '\n').count() + 1;
                let column = until_code.chars().rev().take_while(|&c| c != '\n').count() + 1;
                f.debug_struct(stringify!($Node))
                 .field("node_index", &self.index)
                 .field("type", &self.type_str())
                 .field("content", &code)
                 .field("internal_node", &self.internal_node)
                 .field("line", &line)
                 .field("column", &column)
                 .finish()
            }
        }

        #[derive(Clone, Copy)]
        pub struct SiblingIterator<'a> {
            internal_tree: &'a $crate::InternalTree,
            next_index: $crate::NodeIndex,
            ended: bool,
        }

        impl<'a> SiblingIterator<'a> {
            pub fn new_empty(any_node: &$Node<'a>) -> Self {
                Self {
                    internal_tree: &any_node.internal_tree,
                    next_index: 0,
                    ended: true,
                }
            }
        }

        impl<'a> Iterator for SiblingIterator<'a> {
            type Item = $Node<'a>;

            fn next(&mut self) -> Option<Self::Item> {
                if self.ended {
                    return None;
                }
                let current_node = &self.internal_tree.nodes[self.next_index as usize];
                if current_node.next_node_offset == 0 {
                    self.ended = true;
                }
                let current = Self::Item {
                    internal_tree: self.internal_tree,
                    index: self.next_index,
                    internal_node: current_node,
                };
                self.next_index += current_node.next_node_offset;
                Some(current)
            }
        }

        impl std::fmt::Debug for SiblingIterator<'_> {
            fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
                f.debug_struct("SiblingIterator")
                 .field("internal_tree", &format!("node count: #{}", self.internal_tree.nodes.len()))
                 .field("next_index", &self.next_index)
                 .field("ended", &self.ended)
                 .finish()
            }
        }

        pub struct SearchIterator<'a> {
            internal_tree: &'a $crate::InternalTree,
            next_index: $crate::NodeIndex,
            end_code_index: $crate::CodeIndex,
            search_types: &'static [$NodeType],
        }

        impl<'a> Iterator for SearchIterator<'a> {
            type Item = $Node<'a>;

            fn next(&mut self) -> Option<Self::Item> {
                for (i, n) in self.internal_tree.nodes[self.next_index as usize..].iter().enumerate() {
                    let i = i as $crate::NodeIndex;
                    if n.start_index >= self.end_code_index {
                        // TODO this might be an issue with zero length nodes
                        return None;
                    }
                    for t in self.search_types {
                        if t.to_internal() == n.type_ {
                            let node = $Node::new(self.internal_tree, self.next_index + i, n);
                            self.next_index += i + 1;
                            return Some(node)
                        }
                    }
                }
                unreachable!();
            }
        }
    }
}

#[macro_export]
macro_rules! __parse_next_identifier {
    // The ~ operator
    ($input:expr, ~ $($rule:tt)+) => (
        $crate::Rule::Cut(&$input, &$crate::__parse_identifier!($($rule)+))
    );

    // An identifier again
    ($input:expr, $($rule:tt)+) => (
        $crate::Rule::Next(&$input, &$crate::__parse_identifier!($($rule)+))
    );
    ($input:expr,) => ($input);
}

#[macro_export]
macro_rules! __parse_operators {
    ($input:expr, + $($rule:tt)*) => (
        $crate::__parse_next_identifier!($crate::Rule::Multiple(&$input), $($rule)*)
    );
    ($input:expr, * $($rule:tt)*) => (
        $crate::__parse_next_identifier!($crate::Rule::Maybe(&$crate::Rule::Multiple(&$input)), $($rule)*)
    );
    ($input:expr, ? $($rule:tt)*) => (
        $crate::__parse_next_identifier!($crate::Rule::Maybe(&$input), $($rule)*)
    );
    ($separator:expr, . $label:tt + $($rule:tt)*) => ({
        // Basically turns s.e+ to (e (s e)*)
        $crate::__parse_next_identifier!(
            $crate::Rule::Next(
                &$crate::__parse_identifier!($label),
                &$crate::Rule::Maybe(&$crate::Rule::Multiple(&$crate::Rule::Next(
                    &$separator,
                    &$crate::__parse_identifier!($label)
                )))
            ),
            $($rule)*
        )
    });

    // All the other cases can only be simple operators
    ($input:expr, $($rule:tt)*) => ($crate::__parse_next_identifier!($input, $($rule)*));
}

#[macro_export]
macro_rules! __parse_identifier {
    // Negative Lookahead
    (! $lookahead:tt $($rule:tt)*) => (
        $crate::__parse_next_identifier!(
            $crate::Rule::NegativeLookahead(&$crate::__parse_identifier!($lookahead)), $($rule)*)
    );
    // Positive Lookahead
    (& $lookahead:tt $($rule:tt)*) => (
        $crate::__parse_next_identifier!(
            $crate::Rule::PositiveLookahead(&$crate::__parse_identifier!($lookahead)), $($rule)*)
    );

    // Terminal/Nonterminal
    ($name:ident $($rule:tt)*) => (
        $crate::__parse_operators!($crate::Rule::Identifier(stringify!($name)), $($rule)*)
    );
    // Keyword
    ($string:literal $($rule:tt)*) => (
        $crate::__parse_operators!($crate::Rule::Keyword($string), $($rule)*)
    );

    // Group parentheses
    (($($inner:tt)+) $($rule:tt)*) => (
        $crate::__parse_operators!(
            $crate::__parse_or!([] $($inner)*),
            $($rule)*
        )
    );

    // Optional brackets
    ([$($inner:tt)+] $($rule:tt)*) => (
        $crate::__parse_operators!(
            $crate::Rule::Maybe(&$crate::__parse_or!([] $($inner)*)),
            $($rule)*
        )
    );
}

#[macro_export]
macro_rules! __parse_or {
    // First we need to split up the rule for or, because it has the highest precedence.

    ([$($saved:tt)*] | $($rule:tt)+) => {
        $crate::Rule::Or(
            // Finish parsing the rule
            &$crate::__parse_identifier!($($saved)+),
            // Parse the next rule
            &$crate::__parse_or!([] $($rule)+),
        )
    };

    ([$($saved:tt)*] $next:tt $($rule:tt)*) => {
        $crate::__parse_or!([$($saved)* $next] $($rule)*)
    };

    ([$($saved:tt)+]) => {
        $crate::__parse_identifier!($($saved)+)
    };
}

#[macro_export]
macro_rules! __parse_at {
    // Parses the @error_recovery in `foo: @error_recovery bar | baz
    (@error_recovery $($rule:tt)*) => {
        $crate::Rule::DoesErrorRecovery(&$crate::__parse_or!([] $($rule)*))
    };

    ($($rule:tt)*) => {
        $crate::__parse_or!([] $($rule)*)
    };
}

#[macro_export]
macro_rules! __parse_reduce {
    // Parses the question mark in `foo:? bar | baz
    (? $($rule:tt)*) => {
        $crate::Rule::NodeMayBeOmitted(&$crate::__parse_at!($($rule)*))
    };

    ($($rule:tt)*) => {
        $crate::__parse_at!($($rule)*)
    };
}

#[macro_export]
macro_rules! __parse_rules {
    ($NonterminalType:ident, $rules:ident, $label:ident: | $($rule:tt)+) => {
        $crate::__parse_rule!($NonterminalType, $rules, [$label] $($rule)+)
    };
    ($NonterminalType:ident, $rules:ident, $label:ident : $($rule:tt)+) => {
        $crate::__parse_rule!($NonterminalType, $rules, [$label] $($rule)+)
    };
}

#[macro_export]
macro_rules! __parse_rule {
    ($NonterminalType:ident, $rules:ident, [$($saved:tt)+] $next:ident : $($rule:tt)+) => {
        // Finish parsing the rule
        $crate::__parse_rule!($NonterminalType, $rules, [$($saved)+]);
        // Keep parsing the rest
        $crate::__parse_rules!($NonterminalType, $rules, $next : $($rule)+);
    };

    ($NonterminalType:ident, $rules:ident, [$($saved:tt)+] $next:tt $($rule:tt)*) => {
        $crate::__parse_rule!($NonterminalType, $rules, [$($saved)+ $next] $($rule)*);
    };

    ($NonterminalType:ident, $rules:ident, [$label:ident $($saved:tt)+]) => {
        let key = $crate::InternalNonterminalType($NonterminalType::$label as u16);
        if $rules.contains_key(&key) {
            panic!("Key exists twice: {}", stringify!($label));
        }

        $rules.insert(key, (stringify!($label), $crate::__parse_reduce!($($saved)+)));
    };
}

#[macro_export]
macro_rules! __parse_soft_keywords {
    ($TerminalType:ident, $($terminal:ident : $($string:literal)|+)*) => {{
        let mut soft_keywords = $crate::new_fast_hash_map();
        $(
            let mut tokens = $crate::HashSet::new();
            $(tokens.insert($string);)+
            soft_keywords.insert(
                $crate::InternalTerminalType($TerminalType::$terminal as u16),
                tokens);
        )*;
        soft_keywords
    }};
}

#[macro_export]
macro_rules! create_grammar {
    (static $grammar:ident, struct $Grammar:ident, struct $Tree:ident,
     struct $Node:ident, enum $NodeType:ident, enum $NonterminalType:ident,
     $Tokenizer:ident, $Token:ident, $TerminalType:ident,
     soft_keywords=[$($soft_keywords:tt)*]
     $first_node:ident $($rule:tt)+) => {

        $crate::__create_node!($Tree, struct $Node, enum $NodeType, enum $NonterminalType, $TerminalType,
                               [rules_to_nodes=$first_node $($rule)+]);

        pub struct $Grammar {
            internal_grammar: Grammar<$Token>,
        }

        impl $Grammar {
            fn new() -> Self {
                let mut rules = $crate::new_fast_hash_map();
                $crate::__parse_rules!($NonterminalType, rules, $first_node $($rule)+);
                let soft_keywords = $crate::__parse_soft_keywords!($TerminalType, $($soft_keywords)*);
                Self {internal_grammar: Grammar::new(
                    &rules, $NonterminalType::map(), $TerminalType::map(),
                    soft_keywords
                )}
            }

            pub fn parse(&self, code: Box<str>) -> $Tree {
                use $crate::Tokenizer;
                // TODO shouldn't be dynamic
                let start = $NonterminalType::map()[stringify!($first_node)];
                let nodes = self.internal_grammar.parse(&code, $Tokenizer::new(&code), start);
                $Tree {
                    internal_tree: $crate::InternalTree::new(code, nodes)
                }
            }
        }

        pub struct $Tree {
            internal_tree: $crate::InternalTree
        }

        impl $Tree {
            pub fn as_code(&self) -> &str {
                &self.internal_tree.code
            }

            pub fn root_node(&self) -> $Node {
                self.node(0, &self.internal_tree.nodes[0])
            }

            #[inline]
            fn node<'a>(&'a self, index: $crate::NodeIndex, internal_node: &'a $crate::InternalNode) -> $Node {
                $Node {
                    internal_tree: &self.internal_tree,
                    internal_node,
                    index,
                }
            }

            pub fn length(&self) -> usize {
                self.internal_tree.nodes.len()
            }

            pub fn nodes(&self) -> Vec<$Node> {
                self.internal_tree.nodes.iter().enumerate().map(
                    |(index, internal_node)| self.node(index as $crate::NodeIndex, internal_node)
                ).collect()
            }

            pub fn node_by_index(&self, index: $crate::NodeIndex) -> $Node {
                self.node(index, &self.internal_tree.nodes[index as usize])
            }

            pub fn leaf_by_position(&self, position: $crate::CodeIndex) -> $Node {
                // Returns the leaf under the cursor. Start positions are higher prioritized than
                // end positions. Also if the position is on the prefix, the leaf is returned.
                let index = self.internal_tree.nodes.partition_point(
                    // Means return first start_index > position
                    |node| node.start_index <= position
                );
                for (i, node) in self.internal_tree.nodes[..index].iter().enumerate().rev() {
                    if node.type_.is_leaf() {
                        return self.node(i as $crate::NodeIndex, node)
                    }
                }
                unreachable!();
            }
        }

        impl std::fmt::Debug for $Tree {
            fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
                f.debug_struct("Tree").field("nodes", &self.nodes()).finish()
            }
        }

        $crate::lazy_static! {
            static ref $grammar: $Grammar = {$Grammar::new()};
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    create_terminals!(struct TestTerminal, enum TestTerminalType, [Foo, Bar]);

    struct TestTokenizer {}
    impl Tokenizer<'_, TestTerminal> for TestTokenizer {
        fn new(code: &str) -> Self {
            Self {}
        }
    }

    impl Iterator for TestTokenizer {
        type Item = TestTerminal;

        fn next(&mut self) -> Option<Self::Item> {
            None
        }
    }
    #[test]
    #[should_panic(expected = "The rule \"rule2\" must not have an empty production")]
    fn empty_rule() {
        create_grammar!(
            static GRAMMAR, struct TestGrammar, struct TestTree, struct TestNode,
            enum TestNodeType, enum TestNonterminalType, TestTokenizer, TestTerminal, TestTerminalType,
            soft_keywords=[]

            rule1: rule2 | Foo
            rule2: Bar?
        );

        #[allow(clippy::no_effect)]
        &*GRAMMAR;
    }
    #[test]
    #[should_panic(expected = "Indirect left recursion")]
    fn indirect_left_recursion() {
        create_grammar!(
            static GRAMMAR, struct TestGrammar, struct TestTree, struct TestNode,
            enum TestNodeType, enum TestNonterminalType, TestTokenizer, TestTerminal, TestTerminalType,
            soft_keywords=[]

            rule1: rule2 | Foo
            rule2: rule3
            rule3: rule1
        );

        #[allow(clippy::no_effect)]
        &*GRAMMAR;
    }
    #[test]
    #[should_panic(expected = "grammar contains left recursion")]
    fn direct_left_recursion_without_alternative() {
        create_grammar!(
            static GRAMMAR, struct TestGrammar, struct TestTree, struct TestNode,
            enum TestNodeType, enum TestNonterminalType, TestTokenizer, TestTerminal, TestTerminalType,
            soft_keywords=[]

            rule1: rule1
            rule2: rule1
        );

        #[allow(clippy::no_effect)]
        &*GRAMMAR;
    }
    #[test]
    #[should_panic(expected = "Only terminal lookaheads are allowed")]
    fn left_recursion_in_lookaheads() {
        create_grammar!(
            static GRAMMAR, struct TestGrammar, struct TestTree, struct TestNode,
            enum TestNodeType, enum TestNonterminalType, TestTokenizer, TestTerminal, TestTerminalType,
            soft_keywords=[]

            rule1: &rule1 Bar | Foo
            rule2: rule1
        );

        #[allow(clippy::no_effect)]
        &*GRAMMAR;
    }
    #[test]
    fn direct_left_recursion_with_alternative() {
        create_grammar!(
            static GRAMMAR, struct TestGrammar, struct TestTree, struct TestNode,
            enum TestNodeType, enum TestNonterminalType, TestTokenizer, TestTerminal, TestTerminalType,
            soft_keywords=[]

            rule1: rule1 | Foo
            rule2: rule1
        );

        #[allow(clippy::no_effect)]
        &*GRAMMAR;
    }
}
