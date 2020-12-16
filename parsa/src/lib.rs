#![allow(unused)]
extern crate lazy_static;

mod grammar;
mod automaton;

pub use std::collections::HashMap;
pub use std::io::Bytes;
#[macro_export]
pub use lazy_static::lazy_static;
pub use std::mem;

pub use grammar::{Grammar, InternalTree, ExtraData, CodeIndex, NodeIndex,
                  CodeLength, InternalNode, Tokenizer, Token};
pub use automaton::{InternalSquashedType, InternalNodeType, InternalTokenType,
                    InternalStrToNode, InternalStrToToken, Rule, NODE_START};

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
            pub fn get_map() -> &'static $Map {
                #[macro_use]
                $crate::lazy_static! {
                    static ref HASHMAP: $Map = {
                        let mut m = $crate::HashMap::new();
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
        }
    }
}

#[macro_export]
macro_rules! create_token {
    (struct $Token:ident, enum $TokenType:ident, [$($entry:ident),*]) => {
        $crate::__create_type_set!(enum $TokenType, $crate::InternalStrToToken,
                                   $crate::InternalTokenType, 0, $($entry),*);

        #[derive(Debug)]
        pub struct $Token {
            start_index: $crate::CodeIndex,
            length: $crate::CodeLength,
            type_: $TokenType,
            can_contain_syntax: bool,
        }

        impl $crate::Token for $Token {
            fn get_start_index(&self) -> u32 {
                self.start_index
            }

            fn get_length(&self) -> u32 {
                self.length
            }

            fn get_type(&self) -> $crate::InternalTokenType {
                $crate::InternalTokenType(self.type_ as u16)
            }

            fn can_contain_syntax(&self) -> bool{
                self.can_contain_syntax
            }
        }
    }
}

#[macro_export]
macro_rules! __create_node {
    (struct $Node:ident, enum $NodeType:ident, $TokenType:ident, [$($entry:tt)*]) => {
        $crate::__create_type_set!(enum $NodeType, $crate::InternalStrToNode,
                                   $crate::InternalNodeType, $crate::NODE_START, $($entry)*);

        pub struct $Node<'a> {
            internal_tree: &'a $crate::InternalTree,
            pub index: $crate::NodeIndex,
            internal_node: &'a $crate::InternalNode,
        }

        impl $Node<'_> {
            pub fn get_extra_data(&self) -> $crate::ExtraData {
                self.internal_node.extra_data
            }

            fn get_code_slice(&self, index: $crate::CodeIndex, length: $crate::CodeLength) -> &str {
                use std::str;
                // Can be unsafe, because the input of the parse function is a
                // String that is copied to the internal tree.
                unsafe {str::from_utf8_unchecked(&self.internal_tree.code[
                    index as usize..index as usize + length as usize
                ])}
            }

            pub fn get_code(&self) -> &str {
                self.get_code_slice(self.internal_node.start_index, self.internal_node.length)
            }

            pub fn get_prefix(&self) -> &str {
                let start;
                if self.index == 0 {
                    start = 0;
                } else {
                    start = self.internal_tree.nodes[self.index as usize - 1].start_index;
                }
                let string = self.get_code_slice(start, self.internal_node.start_index);
                string
            }

            pub fn get_suffix(&self) -> &str {
                let end;
                if self.index as usize == self.internal_tree.nodes.len() - 1 {
                    end = self.internal_tree.code.len() as u32
                } else {
                    end = self.internal_tree.nodes[self.index as usize + 1].start_index
                }
                let string = self.get_code_slice(
                    self.internal_node.start_index + self.internal_node.length,
                    end
                );
                string
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

            fn is_leaf(&self) -> bool {
                return self.internal_node.type_.is_leaf()
            }

            pub fn token_type(&self) -> Option<$TokenType> {
                if !self.is_leaf() {
                    return None
                }
                if self.internal_node.type_.0 as usize >= $TokenType::get_map().len() {
                    return None
                }
                // Can be unsafe, because the TokenType is created by the macro create_token.
                // TODO 
                Some(unsafe {$crate::mem::transmute(self.internal_node.type_)})
            }

            pub fn node_type(&self) -> Option<$NodeType> {
                if self.is_leaf() {
                    return None
                }
                // Can be unsafe, because the NodeType is created by this exact macro.
                Some(unsafe {$crate::mem::transmute(self.internal_node.type_)})
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
    ($input:expr, . $($rule:tt)+) => (
        // Basically turns s.e+ to (e (s e)*)
        $crate::Rule::Next(
            &$input,
            &$crate::Rule::Maybe(&$crate::Rule::Multiple(&$crate::Rule::Next(
                &$input,
                &$crate::__parse_identifier!($($rule)+)
            )))
        )
    );

    // All the other cases can only be simple operators
    ($input:expr, $($rule:tt)*) => ($crate::__parse_next_identifier!($input, $($rule)*));
}

#[macro_export]
macro_rules! __parse_identifier {
    // Negative Lookahead
    (! $($rule:tt)+) => (
        $crate::Rule::NegativeLookahead(&$crate::__parse_identifier!($($rule)+))
    );
    // Positive Lookahead
    (& $($rule:tt)+) => (
        $crate::Rule::PositiveLookahead(&$crate::__parse_identifier!($($rule)+))
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
macro_rules! __parse_rules {
    ($NodeType:ident, $rules:ident, $label:ident: | $($rule:tt)+) => {
        $crate::__parse_rule!($NodeType, $rules, [$label] $($rule)+)
    };
    ($NodeType:ident, $rules:ident, $label:ident : $($rule:tt)+) => {
        $crate::__parse_rule!($NodeType, $rules, [$label] $($rule)+)
    };
}

#[macro_export]
macro_rules! __parse_rule {
    ($NodeType:ident, $rules:ident, [$($saved:tt)+] $next:ident : $($rule:tt)+) => {
        // Finish parsing the rule
        $crate::__parse_rule!($NodeType, $rules, [$($saved)+]);
        // Keep parsing the rest
        $crate::__parse_rules!($NodeType, $rules, $next : $($rule)+);
    };

    ($NodeType:ident, $rules:ident, [$($saved:tt)+] $next:tt $($rule:tt)*) => {
        $crate::__parse_rule!($NodeType, $rules, [$($saved)+ $next] $($rule)*);
    };

    ($NodeType:ident, $rules:ident, [$label:ident $($saved:tt)+]) => {
        let key = $crate::InternalNodeType($NodeType::$label as u16);
        if $rules.contains_key(&key) {
            panic!("Key exists twice: {}", stringify!($label));
        }

        $rules.insert(key, (stringify!($label), $crate::__parse_or!([] $($saved)+)));
    };
}

#[macro_export]
macro_rules! create_grammar {
    (static $grammar:ident, struct $Grammar:ident, struct $Tree:ident,
     struct $Node:ident, enum $NodeType:ident, $Tokenizer:ident, $Token:ident, $TokenType:ident,
     $first_node:ident $($rule:tt)+) => {

        $crate::__create_node!(struct $Node, enum $NodeType, $TokenType,
                               [rules_to_nodes=$first_node $($rule)+]);

        pub struct $Grammar {
            internal_grammar: Grammar<$Token>,
        }

        impl $Grammar {
            fn new() -> Self {
                let mut rules = $crate::HashMap::new();
                $crate::__parse_rules!($NodeType, rules, $first_node $($rule)+);
                Self {internal_grammar: Grammar::new(
                    &rules, $NodeType::get_map(), $TokenType::get_map(),
                )}
            }

            pub fn parse(&self, code: &str) -> $Tree {
                use $crate::Tokenizer;
                // TODO shouldn't be dynamic
                let start = $NodeType::get_map()[stringify!($first_node)];
                $Tree {
                    internal_tree: $crate::InternalTree {
                        code: code.as_bytes().to_owned(),
                        nodes: self.internal_grammar.parse(code, $Tokenizer::new(code), start),
                        lines: None
                    }
                }
            }
        }

        #[derive(Debug)]
        pub struct $Tree {
            internal_tree: parsa::InternalTree
        }

        impl $Tree {
            pub fn get_root_node(&self) -> $Node {
                self.get_node(0, &self.internal_tree.nodes[0])
            }

            #[inline]
            fn get_node<'a>(&'a self, index: u32, internal_node: &'a $crate::InternalNode) -> $Node{
                $Node {
                    internal_tree: &self.internal_tree,
                    internal_node: internal_node,
                    index: index,
                }
            }

            pub fn get_nodes(&self) -> Vec<$Node> {
                self.internal_tree.nodes.iter().enumerate().map(
                    |(index, internal_node)| self.get_node(index as u32, internal_node)
                ).collect()
            }

            pub fn set_extra_data(&mut self, index: $crate::NodeIndex, extra_data: $crate::ExtraData) {
                self.internal_tree.nodes[0].extra_data = extra_data
            }
        }

        $crate::lazy_static! {
            pub static ref $grammar: $Grammar = {$Grammar::new()};
        }
    }
}
