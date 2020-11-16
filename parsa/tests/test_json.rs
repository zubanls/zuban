#![recursion_limit="1024"]
extern crate regex;
extern crate lazy_static;

use regex::Regex;
use std::str;

use parsa::{create_token, create_grammar, Grammar};

lazy_static::lazy_static! {
    static ref WHITESPACE: Regex = Regex::new(r"^\s+").unwrap();
    static ref STRING: Regex = Regex::new(r#"^"[^"]*"|'[^']*'"#).unwrap();
    static ref NUMBER: Regex = Regex::new(r"^[+-]?[0-9]+").unwrap();
    static ref LABEL: Regex = Regex::new(r"^\p{alpha}\w*").unwrap();
    static ref ERROR: Regex = Regex::new(r"^[^\w,:{}\[\]]+").unwrap();
}


struct JsonTokenizer<'a> {
    code: &'a str,
    index: usize,
    ended: bool,
}

impl<'a> parsa::Tokenizer<'a, JsonToken> for JsonTokenizer<'a> {
    fn new(code: &'a str) -> Self {
        assert!(code.len() < u32::MAX as usize);
        Self {code: code, index: 0, ended: false}
    }
}

impl Iterator for JsonTokenizer<'_> {
    type Item = JsonToken;

    fn next(&mut self) -> Option<Self::Item> {
        let new_token = |start, length, type_: TokenType, can_contain_syntax| {
            return Some(JsonToken {
                start_index: start as u32,
                length: length as u32,
                type_: type_,
                can_contain_syntax: can_contain_syntax,
            })
        };
        let code_bytes = &self.code.as_bytes();
        let get_code = |index: usize| unsafe {str::from_utf8_unchecked(&code_bytes[index..])};

        let whitespace = WHITESPACE.find(get_code(self.index));
        if let Some(match_) = whitespace {
            self.index += match_.end();
        }

        let index = self.index;
        const OPERATORS: &[u8; 6] = b",:{}[]";
        if let Some(byte) = code_bytes.get(self.index) {
            if OPERATORS.contains(byte) {
                self.index += 1;
                return new_token(index, 1, TokenType::Operator, true);
            }
        } else {
            if self.ended {
                return None
            } else {
                return new_token(index, 0, TokenType::Endmarker, false);
            }
        }

        for (regex, type_) in &[(&*STRING, TokenType::String),
                                (&*NUMBER, TokenType::Number),
                                (&*LABEL, TokenType::Label),
                                (&*ERROR, TokenType::Error),] {
            if let Some(match_) = regex.find(get_code(index)) {
                self.index += match_.end();
                return new_token(index, match_.end() - match_.start(), *type_, false);
            }
        }
        unreachable!();
    }
}

create_token!(struct JsonToken, enum TokenType, [Label, String, Number, Operator, Error, Endmarker]);

create_grammar!(
    static JSON_GRAMMAR, struct JsonGrammar, struct JsonTree, 
    struct JsonNode, enum NodeType, JsonTokenizer, JsonToken, TokenType,

    document: json Endmarker
    json: array | object
    value: String | Number | json

    array: "[" [json ("," json)*] "]"
    object: "{" [property ("," property)*] "}"
    property: name ":" value
    name: Label | String
);

#[test]
fn it_works() {
    JSON_GRAMMAR.parse("{asdf: 1}");
}
