#![allow(unused)]
extern crate lazy_static;

mod grammar;
mod automaton;

pub use std::collections::HashMap;
pub use std::io::Bytes;
#[macro_export]
pub use lazy_static::lazy_static;
pub use std::mem;

pub use grammar::{Grammar};
pub use automaton::{InternalSquashedType};

pub type ExtraData = u32;
pub type NodeIndex = u32;
pub type CodeIndex = u32;
pub type CodeLength = u32;
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, Default)]
pub struct InternalTokenType(pub i16);
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, Default)]
pub struct InternalNodeType(pub i16);
pub type InternalStrToToken = HashMap<&'static str, InternalTokenType>;
pub type InternalStrToNode = HashMap<&'static str, InternalNodeType>;

pub trait Token {
    fn get_start_index(&self) -> u32;
    fn get_length(&self) -> u32;
    fn get_type(&self) -> InternalTokenType;
    fn can_contain_syntax(&self) -> bool;
}

pub trait Tokenizer<'a, T: Token>: Iterator {
    fn new(code: &'a str) -> Self;
    fn yield_next(&self) -> T;
}

pub fn parse<'a, U: Token, T: Tokenizer<'a, U>>(code: &'a str) -> InternalTree {
    T::new(code).yield_next().get_type();
    InternalTree {code: code.as_bytes().to_owned(), nodes: Vec::new(), lines: None}
}

pub struct InternalTree {
    pub code: Vec<u8>,
    pub nodes: Vec<InternalNode>,
    pub lines: Option<Vec<u32>>,
}

#[derive(Copy, Clone, Debug)]
pub struct InternalNode {
    next_node_offset: NodeIndex,
    // Positive values are token types, negative values are nodes
    pub type_: InternalSquashedType,

    pub start_index: CodeIndex,
    pub length: CodeLength,
    pub extra_data: ExtraData,
}

struct CompressedNode {
    next_node_offset: u8,
    // Positive values are token types, negative values are nodes
    type_: i8,

    start_index: u16,
    length: u16,
    extra_data1: u16,
    extra_data2: u16,
}


#[cfg(test)]
mod tests {
    use std::mem::{size_of, align_of};
    use super::*;

    #[test]
    fn sizes() {
        assert_eq!(size_of::<InternalNode>(), 20);
        assert_eq!(size_of::<CompressedNode>(), 10);
        assert_eq!(align_of::<InternalNode>(), 4);
        assert_eq!(align_of::<CompressedNode>(), 2);
    }

    /*
    fn p() -> Tree {
        use std::env::current_dir;
        //let foo = &current_dir().unwrap().into_os_string().into_string().unwrap();
        let foo = "foo";
        //return parse(foo, || Token{start: 1, length: 1, type_: 1});
    }
    #[test]
    fn test_parse() {
        let tree = p();
        assert_eq!(tree.code, "foo");
    }
    */
}

#[macro_export]
macro_rules! __create_type_set {
    (enum $EnumName:ident, $Map:path, $Type:path, $($entry:ident),*) => {
        #[allow(non_camel_case_types)]
        #[derive(Copy, Clone, Debug)]
        #[repr(i16)]
        pub enum $EnumName {
            $($entry),*
        }

        impl $EnumName {
            fn get_map() -> &'static $Map {
                #[macro_use]
                $crate::lazy_static! {
                    static ref HASHMAP: $Map = {
                        let mut m = $crate::HashMap::new();
                        $(m.insert(
                              stringify!($entry),
                              $Type($EnumName::$entry as i16)
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
                                   $crate::InternalTokenType, $($entry),*);

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
                $crate::InternalTokenType(self.type_ as i16)
            }

            fn can_contain_syntax(&self) -> bool{
                self.can_contain_syntax
            }
        }
    }
}

#[macro_export]
macro_rules! create_node {
    (struct $Node:ident, enum $NodeType:ident, $TokenType:ident, [$($entry:ident),*]) => {
        $crate::__create_type_set!(enum $NodeType, $crate::InternalStrToNode,
                                   $crate::InternalNodeType, $($entry),*);

        pub struct $Node<'a> {
            internal_tree: &'a $crate::InternalTree,
            pub index: $crate::NodeIndex,
            internal_node: &'a $crate::InternalNode,
        }

        impl $Node<'_> {
            fn get_extra_data(&self) -> $crate::ExtraData {
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

            fn is_leaf(&self) -> bool {
                false // TODO
                //return self.internal_node.type_ < 0
            }

            pub fn token_type(&self) -> Option<$TokenType> {
                if self.is_leaf() {
                    return None
                }
                // Can be unsafe, because the TokenType is created by the macro create_token.
                // TODO 
                Some(unsafe {$crate::mem::transmute(self.internal_node.type_)})
            }

            pub fn node_type(&self) -> Option<$NodeType> {
                if !self.is_leaf() {
                    return None
                }
                // Can be unsafe, because the NodeType is created by this exact macro.
                Some(unsafe {$crate::mem::transmute(self.internal_node.type_)})
            }
        }
    }
}

#[derive(Debug)]
pub enum Rule {
    Identifier(&'static str),
    Keyword(&'static str),
    Or(&'static Rule, &'static Rule),
    Cut(&'static Rule, &'static Rule),
    Maybe(&'static Rule),
    Multiple(&'static Rule),
    NegativeLookahead(&'static Rule),
    PositiveLookahead(&'static Rule),
    Next(&'static Rule, &'static Rule),
}

#[macro_export]
macro_rules! __parse_or {
    // Actually an operator
    ($input:expr, | $($rule:tt)+) => (
        $crate::Rule::Or(&$input, &$crate::__parse_identifier!($($rule)+))
    );
    // TODO this should have lower prio than |
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
        $crate::__parse_or!($crate::Rule::Multiple(&$input), $($rule)*)
    );
    ($input:expr, * $($rule:tt)*) => (
        $crate::__parse_or!($crate::Rule::Maybe(&$crate::Rule::Multiple(&$input)), $($rule)*)
    );
    ($input:expr, ? $($rule:tt)*) => (
        $crate::__parse_or!($crate::Rule::Maybe(&$input), $($rule)*)
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
    ($input:expr, $($rule:tt)*) => ($crate::__parse_or!($input, $($rule)*));
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
            $crate::__parse_identifier!($($inner)*),
            $($rule)*
        )
    );

    // Optional brackets
    ([$($inner:tt)+] $($rule:tt)*) => (
        $crate::Rule::Maybe(&$crate::__parse_operators!(
            $crate::__parse_identifier!($($inner)*),
            $($rule)*
        ))
    );
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
        $crate::__parse_rule!($NodeType, $rules, [$($saved)+ $next]);
        // Keep parsing the rest
        $crate::__parse_rules!($NodeType, $rules, $next : $($rule)+);
    };

    ($NodeType:ident, $rules:ident, [$($saved:tt)+] $next:tt $($rule:tt)*) => {
        $crate::__parse_rule!($NodeType, $rules, [$($saved)+ $next] $($rule)*);
    };

    ($NodeType:ident, $rules:ident, [$label:ident $($saved:tt)+]) => {
        let key = $crate::InternalNodeType($NodeType::$label as i16);
        if $rules.contains_key(&key) {
            panic!("Key exists twice: {}", stringify!($label));
        }

        $rules.insert(key, $crate::__parse_identifier!($($saved)+));
    };
}

#[macro_export]
macro_rules! create_grammar {
    (static $grammar:ident, struct $Grammar:ident, struct $Tree:ident, $Tokenizer:ident,
     $Node:ident, $NodeType:ident, $Token:ident, $TokenType:ident,
     $first_node:ident $($rule:tt)+) => {
        struct $Grammar {
            internal_grammar: Grammar<PythonToken>,
        }

        impl $Grammar {
            fn new() -> Self {
                let mut rules = $crate::HashMap::new();
                $crate::__parse_rules!($NodeType, rules, $first_node $($rule)+);
                Self {internal_grammar: Grammar::new(
                    &rules, $NodeType::get_map(), $TokenType::get_map(),
                )}
            }

            pub fn foo(&self) {
            }

            pub fn parse(&self, code: &str) -> $crate::InternalTree {
                use $crate::Tokenizer;
                // TODO shouldn't be dynamic
                let start = $NodeType::get_map()[stringify!($first_node)];
                $crate::InternalTree {
                    code: code.as_bytes().to_owned(),
                    nodes: self.internal_grammar.parse(code, $Tokenizer::new(code), start),
                    lines: None
                }
            }
        }

        pub struct $Tree {
            internal_tree: parsa::InternalTree
        }

        impl $Tree {
            pub fn get_root_node(&self) -> $Node{
                $Node {
                    internal_tree: &self.internal_tree,
                    internal_node: &self.internal_tree.nodes[0],
                    index: 0,
                }
            }

            pub fn set_extra_data(&mut self, index: $crate::NodeIndex, extra_data: $crate::ExtraData) {
                self.internal_tree.nodes[0].extra_data = extra_data
            }
        }

        $crate::lazy_static! {
            static ref $grammar: $Grammar = {$Grammar::new()};
        }
    }
}
