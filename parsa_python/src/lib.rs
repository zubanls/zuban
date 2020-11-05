#![recursion_limit="1024"]
use parsa::{create_parser,create_node,create_token, create_grammar, Grammar};


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
create_node!(struct PythonNode, enum NodeType, TokenType, [foo, bar, multiline, multi, x, y, z, bracket1, bracket2, negative_lookahead, positive_lookahead, separator, separator2, cutoff, optional]);
create_parser!(fn parse_python, struct PythonTree, PythonNode,
               PythonToken, PythonTokenizer, TokenType, NodeType);
create_parser!(fn parse_pythonx, struct PythonTreex, PythonNode,
               PythonToken, PythonTokenizer, TokenType, NodeType);

create_grammar!(
    struct PythonGrammar, NodeType, TokenType,

    foo: bar | "baz"
    bar: "bla"
    multiline:
        | foo
        | bar
    multi: foo bar
    x: foo+
    y: foo*
    z: la foo?
    bracket1: (la foo)
    bracket2: bar (lala foo)?
    negative_lookahead: bar !foo
    positive_lookahead: bar &foo
    separator: bar.foo
    separator2: (bar (x)*).foo
    cutoff: (bar ~ foo | baz)
    optional: [bar foo] x
);

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
        parse_python("bar");
        dbg!(TokenType::get_map());
        dbg!(NodeType::get_map());
        PythonGrammar::new();
    }
}
