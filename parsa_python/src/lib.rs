use parsa::{create_parser,create_node,create_token};


struct PythonTokenizer {
}

impl PythonTokenizer {
    fn new_tok(&self) -> PythonToken {
        PythonToken {
            start_index: 0,
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

create_token!(struct PythonToken, enum TokenType, [String, Number, Endmarker]);
create_node!(struct PythonNode, enum NodeType, TokenType, [file_input, foo]);
create_parser!(fn parse_python, struct PythonTree, PythonNode,
               PythonToken, PythonTokenizer, TokenType, NodeType);
create_parser!(fn parse_pythonx, struct PythonTreex, PythonNode,
               PythonToken, PythonTokenizer, TokenType, NodeType);

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
        parse_python("bar");
        dbg!(TokenType::get_map());
        dbg!(NodeType::get_map());
        return
    }
}
