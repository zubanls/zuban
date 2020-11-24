use parsa::{create_token};

create_token!(struct PythonToken, enum PythonTokenType,
              [Name, String, Number, Endmarker, Newline, Indent, Dedent,
               FStringStart, FStringString, FStringEnd]);

pub struct PythonTokenizer<'a> {
    code: &'a str,
}

impl PythonTokenizer<'_> {
    fn new_tok(&self) -> PythonToken {
        PythonToken {
            start_index: 0,
            length: 0,
            type_: PythonTokenType::Endmarker,
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

