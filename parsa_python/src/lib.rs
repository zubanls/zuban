#![recursion_limit="1024"]
use parsa::{create_token, create_grammar, Grammar};


struct PythonTokenizer<'a> {
    code: &'a str,
}

impl PythonTokenizer<'_> {
    fn new_tok(&self) -> PythonToken {
        PythonToken {
            start_index: 0,
            length: 0,
            type_: TokenType::Endmarker,
            can_contain_syntax: false,
        }
    }
}

impl<'a> parsa::Tokenizer<'a, PythonToken> for PythonTokenizer<'a> {
    fn new(code: &'a str) -> Self {
        Self {code: code}
    }

}

impl Iterator for PythonTokenizer<'_> {
    type Item = PythonToken;
    fn next(&mut self) -> Option<Self::Item> {
        //self.new_tok()
        None
    }
}

create_token!(struct PythonToken, enum TokenType, [String, Number, Endmarker]);

create_grammar!(
    static PYTHON_GRAMMAR, struct PythonGrammar, struct PythonTree, 
    struct PythonNode, enum NodeType, PythonTokenizer, PythonToken, TokenType,

    foo: bar | "baz"
    bar: "bla"
    multiline:
        | foo
        | bar
    multi: foo bar
    x: foo+
    y: foo* bar bar multiline
    z: x foo?
    bracket1: (x foo)
    bracket2: bar (y foo)?
    negative_lookahead: bar !foo
    positive_lookahead: bar &foo
    separator: bar.foo
    separator2: (bar (x)*).foo
    cutoff: (bar ~ foo | x)
    optional: [bar foo] x
);

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
        //dbg!(TokenType::get_map());
        //dbg!(NodeType::get_map());
        //PythonGrammar::new();
        //PYTHON_GRAMMAR.parse("asdf");
    }
}
