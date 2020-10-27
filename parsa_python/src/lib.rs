use parsa;

#[repr(i16)]
pub enum TokenType {
    String = 1,
    Number,
}

#[allow(non_camel_case_types)]
#[repr(i16)]
pub enum NodeType {
    file_input = 1,
    foo,
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
        parse_python("foo", |code| PythonToken{start: 1, length: 1, type_: TokenType::String});
        return
    }
}

parsa::create_parser!(parse_python, PythonTree, PythonToken, PythonNode,
                      TokenType, NodeType);
