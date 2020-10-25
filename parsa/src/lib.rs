#![allow(unused)]

fn parse(code: &str) -> Tree {
    Tree {code: code.to_owned(), nodes: Vec::new() }
}

struct Tree {
    code: String,
    nodes: Vec<Node>,
}


#[derive(Copy, Clone)]
struct Node {
    next_node_offset: u32,
    // Positive values are token types, negative values are nodes
    node_type: i16,

    start_index: u32,
    length: u16,
    extra_data: u32,
}

impl Node {
    pub fn get_extra_data(&self) -> u32 {
        self.extra_data
    }

    pub fn set_extra_data(&mut self, extra_data: u32) {
        self.extra_data = extra_data
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
        assert_eq!(size_of::<Node>(), 16);
        assert_eq!(size_of::<CompressedNode>(), 10);
    }

    fn p() -> Tree {
        use std::env::current_dir;
        //let foo = &current_dir().unwrap().into_os_string().into_string().unwrap();
        let foo = "foo";
        return parse(foo);
    }
    #[test]
    fn test_parse() {
        let tree = p();
        assert_eq!(tree.code, "foo");
    }
}
