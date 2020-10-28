#![allow(unused)]
use std::mem;

pub trait Token {
    fn get_start(&self) -> u32;
    fn get_length(&self) -> u32;
    fn get_type(&self) -> u16;
}

pub trait Tokenizer<T: Token> {
    fn new(code: &str) -> Self;
    fn yield_next(&self) -> T;
}

pub fn parse<U: Token, T: Tokenizer<U>>(code: &str, tokenizer: T) -> Tree {
    T::new(code).yield_next().get_type();
    Tree {code: code.to_owned(), nodes: Vec::new(), lines: None}
}

pub struct Tree {
    code: String,
    nodes: Vec<Node>,
    lines: Option<Vec<u32>>,
}

#[derive(Copy, Clone)]
struct Node {
    next_node_offset: u32,
    // Positive values are token types, negative values are nodes
    type_: i16,

    start_index: u32,
    length: u32,
    extra_data: u32,
}

impl Node {
    pub fn get_extra_data(&self) -> u32 {
        self.extra_data
    }

    pub fn set_extra_data(&mut self, extra_data: u32) {
        self.extra_data = extra_data
    }

    pub fn is_leaf(&self) -> bool {
        return self.type_ < 0
    }

    /*
    pub fn token_type(&self) -> Option<TokenType> {
        if self.is_leaf() {
            return None
        }
        Some(unsafe {mem::transmute::<i16, TokenType>(-self.type_)})
    }

    pub fn node_type(&self) -> Option<NodeType> {
        if !self.is_leaf() {
            return None
        }
        Some(unsafe {mem::transmute::<i16, NodeType>(self.type_)})
    }
    */
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
        assert_eq!(size_of::<Node>(), 20);
        assert_eq!(size_of::<CompressedNode>(), 10);
        assert_eq!(align_of::<Node>(), 4);
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
	($parser_name:ident, $Tree:ident, $Token:ident, $Node:ident, $TokenType:ty, $NodeType:ty) => {
        pub fn $parser_name<U: parsa::Token, T: parsa::Tokenizer<U>>(code: &str, next_token: T) -> $Tree {
            $Tree {internal_tree: parsa::parse(code, next_token)}
        }

        pub struct $Tree {
            internal_tree: parsa::Tree
        }

		impl $Tree {
		}

        pub struct $Node {
        }

        impl $Node {
        }

        pub struct $Token {
            start: u32,
            length: u32,
            type_: $TokenType,
        }

        impl parsa::Token for $Token {
            fn get_start(&self) -> u32 {
                self.start
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
