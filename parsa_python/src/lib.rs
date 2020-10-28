use parsa::create_parser;

#[repr(i16)]
#[derive(Copy, Clone)]
pub enum TokenType {
    String = 1,
    Number,
    Endmarker,
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
    use parsa::*;
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
        parse_python::<PythonToken, PythonTokenizer>("foo", PythonTokenizer::new(""));
        return
    }
}

struct PythonTokenizer {
}

impl PythonTokenizer {
    fn new_tok(&self) -> PythonToken {
        PythonToken {
            start: 0,
            length: 0,
            type_: TokenType::Endmarker,
        }
    }
}

impl parsa::Tokenizer<PythonToken> for PythonTokenizer {
    fn new(_code: &str) -> Self {
        Self {}
    }

    fn yield_next(&self) -> PythonToken {
        self.new_tok()
    }

}

create_parser!(parse_python, PythonTree, PythonToken, PythonNode,
                      TokenType, NodeType);
