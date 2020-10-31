#![allow(unused)]
extern crate lazy_static;
pub use std::collections::HashMap;
#[macro_export]
pub use lazy_static::lazy_static;
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

pub fn parse<U: Token, T: Tokenizer<U>>(code: &str) -> InternalTree {
    T::new(code).yield_next().get_type();
    InternalTree {code: code.to_owned(), nodes: Vec::new(), lines: None}
}

pub struct InternalTree {
    pub code: String,
    pub nodes: Vec<InternalNode>,
    pub lines: Option<Vec<u32>>,
}

#[derive(Copy, Clone)]
pub struct InternalNode {
    next_node_offset: u32,
    // Positive values are token types, negative values are nodes
    pub type_: i16,

    start_index: u32,
    length: u32,
    pub extra_data: u32,
}

pub mod private_parts {
    pub trait InternalNodeAccess {
        fn type_int(&self) -> i16;
    }
}

pub trait Node: private_parts::InternalNodeAccess {

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
	($parser_name:ident, $Tree:ident, $Node:ident, $Token:ty, $Tokenizer:ty, $TokenType:ty, $NodeType:ty) => {
        pub fn $parser_name(code: &str) -> $Tree {
            $Tree {internal_tree: parsa::parse::<$Token, $Tokenizer>(code)}
        }

        pub struct $Tree {
            internal_tree: parsa::InternalTree
        }

		impl $Tree {
            /*pub fn get_root_node(&self) -> $Node{
                $Node {internal_node: &self.internal_tree.nodes[0]}
            }*/
		}

        pub struct $Node {
            internal_node: parsa::InternalNode
        }



        impl $Node {
            fn get_extra_data(&self) -> u32 {
                self.internal_node.extra_data
            }

            fn set_extra_data(&mut self, extra_data: u32) {
                self.internal_node.extra_data = extra_data
            }
        }
        impl parsa::private_parts::InternalNodeAccess for $Node {
            fn type_int(&self) -> i16 {
                self.internal_node.type_
            }
        }
        impl parsa::Node for $Node {

            /*fn is_leaf(&self) -> bool {
                return self.type_int() < 0
            }*/

            /*
            pub fn token_type(&self) -> Option<TokenType> {
                if self.is_leaf() {
                    return None
                }
                Some(unsafe {mem::transmute::<i16, $TokenType>(-self.type_)})
            }

            pub fn node_type(&self) -> Option<NodeType> {
                if !self.is_leaf() {
                    return None
                }
                Some(unsafe {mem::transmute::<i16, NodeType>(self.type_)})
            }
            */
        }
    }
}

#[macro_export]
macro_rules! create_type_set {
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
	($Token:ident, enum $TokenType:ident, $($entry:ident),*) => {
        $crate::create_type_set!(enum $TokenType, $($entry),*);

        pub struct $Token {
            start: u32,
            length: u32,
            type_: $TokenType,
        }

        impl $crate::Token for $Token {
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
