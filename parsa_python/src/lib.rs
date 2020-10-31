use parsa::{create_parser,create_type_set};


#[allow(non_camel_case_types)]
#[repr(i16)]
pub enum NodeType {
    file_input = 1,
    foo,
}

create_type_set!(enum TokenType, Endmarker);
//create_type_set!(enum BarType, bar);

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
        parse_python("bar");
        dbg!(TokenType::get_map());
        dbg!(TokenType::get_map());
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
               PythonTokenizer, TokenType, NodeType);
//create_parser!(parse_pythonx, PythonTreex, PythonTokenx, PythonNodex,
//               PythonTokenizer, TokenType, NodeType);
