#![allow(unused)]
extern crate lazy_static;
pub use std::collections::HashMap;
pub use std::io::Bytes;
#[macro_export]
pub use lazy_static::lazy_static;
pub use std::mem;

pub type ExtraData = u32;
pub type NodeIndex = u32;
pub type CodeIndex = u32;
pub type CodeLength = u32;
pub type InternalType = i16;

pub trait Token {
    fn get_start_index(&self) -> u32;
    fn get_length(&self) -> u32;
    fn get_type(&self) -> u16;
}

pub trait Tokenizer<T: Token> {
    fn new(code: &str) -> Self;
    fn yield_next(&self) -> T;
}

pub fn parse<U: Token, T: Tokenizer<U>>(code: &str) -> InternalTree {
    T::new(code).yield_next().get_type();
    InternalTree {code: code.as_bytes().to_owned(), nodes: Vec::new(), lines: None}
}

pub struct InternalTree {
    pub code: Vec<u8>,
    pub nodes: Vec<InternalNode>,
    pub lines: Option<Vec<u32>>,
}

#[derive(Copy, Clone)]
pub struct InternalNode {
    next_node_offset: NodeIndex,
    // Positive values are token types, negative values are nodes
    pub type_: InternalType,

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
macro_rules! create_parser {
    (fn $parser_name:ident, struct $Tree:ident, $Node:ident, $Token:ty, $Tokenizer:ty, $TokenType:ty, $NodeType:ty) => {
        pub fn $parser_name(code: &str) -> $Tree {
            $Tree {internal_tree: parsa::parse::<$Token, $Tokenizer>(code)}
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
    }
}

#[macro_export]
macro_rules! __create_type_set {
    (enum $EnumName:ident, $($entry:ident),*) => {
        #[allow(non_camel_case_types)]
        #[derive(Copy, Clone)]
        #[repr(i16)]
        pub enum $EnumName {
            $($entry),*
        }

        impl $EnumName {
            fn get_map() -> &'static $crate::HashMap<&'static str, i16> {
                #[macro_use]
                $crate::lazy_static! {
                    static ref HASHMAP: $crate::HashMap<&'static str, i16> = {
                        let mut m = $crate::HashMap::new();
                        $(m.insert(stringify!($entry), $EnumName::$entry as i16);)*
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
        $crate::__create_type_set!(enum $TokenType, $($entry),*);

        pub struct $Token {
            start_index: $crate::CodeIndex,
            length: $crate::CodeLength,
            type_: $TokenType,
        }

        impl $crate::Token for $Token {
            fn get_start_index(&self) -> u32 {
                self.start_index
            }

            fn get_length(&self) -> u32 {
                self.length
            }

            fn get_type(&self) -> u16 {
                self.type_ as u16
            }
        }
    }
}

#[macro_export]
macro_rules! create_node {
    (struct $Node:ident, enum $NodeType:ident, $TokenType:ident, [$($entry:ident),*]) => {
        $crate::__create_type_set!(enum $NodeType, $($entry),*);

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
                return self.internal_node.type_ < 0
            }

            pub fn token_type(&self) -> Option<$TokenType> {
                if self.is_leaf() {
                    return None
                }
                // Can be unsafe, because the TokenType is created by the macro create_token.
                Some(unsafe {$crate::mem::transmute(-self.internal_node.type_)})
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

#[macro_export]
macro_rules! create_grammar {
    (struct $Grammar:ident, $NodeType:ident, $TokenType:ident, $($label:ident: $rule:literal;)+) => {
        struct $Grammar {}
        impl $Grammar {
            fn debug() {
                $(dbg!(stringify!($label), $rule);)+
            }
        }
    }
}
