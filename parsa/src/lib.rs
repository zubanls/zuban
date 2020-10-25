#![allow(unused)]

fn parse<F>(code: &str, next_token: F) -> Tree where F: Fn(&str) -> Token{
    Tree {code: code.to_owned(), nodes: Vec::new(), lines: None}
}

struct Tree {
    code: String,
    nodes: Vec<Node>,
    lines: Option<Vec<u32>>,
}

struct Token {
    start: u32,
    length: u32,
    node_type: u16,
}

#[derive(Copy, Clone)]
struct Node {
    next_node_offset: u32,
    // Positive values are token types, negative values are nodes
    node_type: i16,

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
        return self.node_type < 0
    }
}

struct CompressedNode {
    next_node_offset: u8,
    // Positive values are token types, negative values are nodes
    node_type: i8,

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

    fn p() -> Tree {
        use std::env::current_dir;
        //let foo = &current_dir().unwrap().into_os_string().into_string().unwrap();
        let foo = "foo";
        return parse(foo, |code| Token{start: 1, length: 1, node_type: 1});
    }
    #[test]
    fn test_parse() {
        let tree = p();
        assert_eq!(tree.code, "foo");
    }
}
