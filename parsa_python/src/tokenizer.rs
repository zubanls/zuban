/*
 *  A lot of this module is inspired by parso's tokenizer.
 */
extern crate lazy_static;
extern crate regex;

use std::str;
use std::collections::HashSet;
use regex::Regex;
use parsa::{create_token, CodeIndex};

const HEX_NUMBER: &str = r"0[xX](_?[0-9a-fA-F])+";
const BIN_NUMBER: &str = r"0[bB](_?[01])+";
const OCT_NUMBER: &str = r"0[oO](_?[0-7])+";
const DEC_NUMBER: &str = r"(0(_?0)*|[1-9](_?[0-9])*)";
const EXPONENT: &str = r"[eE][-+]?[0-9](?:_?[0-9])*";

lazy_static::lazy_static! {
    static ref WHITESPACE: Regex = r(r"^[\f\t ]+");

    static ref INT_NUMBER: String = or(&[HEX_NUMBER, BIN_NUMBER, OCT_NUMBER, DEC_NUMBER]);
    static ref EXP_FLOAT: String = or(&[r"[0-9](_?[0-9])*", EXPONENT]);
    static ref POINT_FLOAT: String = or(&[
        r"[0-9](?:_?[0-9])*\.(?:[0-9](?:_?[0-9])*)?",
        r"\.[0-9](?:_?[0-9])*"]) + "(" + EXPONENT + ")?";
    static ref FLOAT_NUMBER: String = or(&[&POINT_FLOAT, &EXP_FLOAT]);
    static ref IMAG_NUMBER: String = or(&[r"[0-9](?:_?[0-9])*", &FLOAT_NUMBER]) + r"[jJ]";
    static ref NUMBER: Regex = r(&(
        "^".to_owned() + &or(&[&IMAG_NUMBER, &FLOAT_NUMBER, &INT_NUMBER])
    ));

    static ref STRING: Regex = r(&all_string_regexes(&["", "[rR]", "[uU]"]));
    static ref BYTES: Regex = r(&all_string_regexes(&["[bB][rR]?", "[rR][bB]"]));

    // Because of leftmost-then-longest match semantics, be sure to put the
    // longest operators first (e.g., if = came before ==, == would get
    // recognized as two instances of =).
    static ref OPERATOR: Regex = r(&("^".to_owned() + &or(&[
        r"\*\*=?", r">>=?", r"<<=?", r"//=?", r"->", r"\.\.\.", r":=?",
        r"[+\-*/%&@`|^!=<>]=?", r"[\[\](){}", r"[~;.,@]",
    ])));

    static ref NAME: Regex = r(r"^[A-Za-z_0-9\u0080-\uffff]+");
    static ref NEWLINE: Regex = r(r"^(\r\n?|\n)");
    static ref COMMENT: Regex = r(r"^#[^\r\n]*");
    static ref FSTRING_START: Regex = r(r#"^([Ff][Rr]?|[Rr][Ff])('|"|"""|''')"#);

    static ref ALWAYS_BREAK_NAMES: HashSet<&'static str> = [
        "import", "class", "def", "try", "except",
        "finally", "while", "with", "return", "continue",
        "break", "del", "pass", "global", "assert", "nonlocal"
    ].iter().cloned().collect();
}


fn r(regex_string: &str) -> Regex {
    Regex::new(regex_string).unwrap()
}

fn or(regexes: &[&str]) -> String {
    "(".to_owned() + &regexes.join("|") + ")"
}

fn all_string_regexes(prefixes: &[&'static str]) -> String {
    let not_single_quote = r#"[^\r\n'\\]*"#;
    let not_double_quote = r#"[^\r\n"\\]*"#;
    let backslash = r"\\(\r\n?|\n|.)";

    let single = "'".to_owned() + not_single_quote + r"(" + backslash
                 + not_single_quote + ")*'";
    let double = "\"".to_owned() + not_double_quote + r"(" + backslash
                 + not_double_quote + r#")*""#;
    let single3 = "'''".to_owned() + r"(?s:\\.|'[^'\\]|'\\.|''[^'\\]|''\\.|[^'\\])*'''";
    let double3 = r#"""""#.to_owned() + r#"(?s:\\.|"[^"\\]|"\\.|""[^"\\]|""\\.|[^"\\])*""""#;

    "^".to_owned() + &or(prefixes) + &or(&[&single, &double, &single3, &double3])
}

create_token!(struct PythonToken, enum PythonTokenType,
              [Name, Operator, String, Bytes, Number, Endmarker, Newline, 
               Indent, Dedent, ErrorDedent, FStringStart, FStringString, FStringEnd]);


#[derive(Default, Debug)]
pub struct PythonTokenizer<'a> {
    code: &'a str,

    index: usize,
    ended: bool,
    indents: Vec<Indent>,
}

#[derive(Debug)]
struct Indent {
    start: CodeIndex,
    indentation_count: usize,
}

impl<'a> parsa::Tokenizer<'a, PythonToken> for PythonTokenizer<'a> {
    fn new(code: &'a str) -> Self {
        Self {code: code, ..Default::default()}
    }

}

impl PythonTokenizer<'_> {
    #[inline]
    fn new_tok(&self, type_: PythonTokenType) -> Option<PythonToken> {
        Some(PythonToken {
            start_index: self.index as CodeIndex,
            length: 0,
            type_: type_,
            can_contain_syntax: false,
        })
    }

    #[inline]
    fn dedent_if_necessary(&mut self, indentation_count: usize) -> Option<PythonToken> {
        while indentation_count < self.indents.last().unwrap().indentation_count {
            if indentation_count > self.indents[self.indents.len() - 2].indentation_count {
                self.indents.last_mut().unwrap().indentation_count = indentation_count;
                return self.new_tok(PythonTokenType::ErrorDedent);//, (lnum, start));
            }
            self.indents.pop();
            return self.new_tok(PythonTokenType::Dedent);//, spos);
        }
        None
    }

    #[inline]
    fn code_from_start(&self) -> &str {
        // This function only exists, because the regex crate is not able to at
        // the beginning of a specific position.
        unsafe {
            str::from_utf8_unchecked(&self.code.as_bytes()[self.index as usize..])
        }
    }
}

impl Iterator for PythonTokenizer<'_> {
    type Item = PythonToken;
    fn next(&mut self) -> Option<Self::Item> {
        if self.ended {
            return None;
        }

        //self.ended = true;
        //self.new_tok(Endmarker)

        if let Some(match_) = WHITESPACE.find(self.code_from_start()) {
            self.index += match_.end();
        }

        use PythonTokenType::*;
        let c = self.code_from_start();
        if let Some(match_) = OPERATOR.find(c) {
            // TODO ; always break
            self.index = match_.end();
            return self.new_tok(Operator);
        }
        let regexes = [
            (&*STRING, PythonTokenType::String),
            (&*BYTES, PythonTokenType::Bytes),
            (&*FSTRING_START, PythonTokenType::FStringStart),
            (&*NEWLINE, PythonTokenType::Newline),
            (&*NUMBER, PythonTokenType::Number)
        ];
        for (r, token_type) in &regexes {
            if let Some(match_) = r.find(c) {
                self.index = match_.end();
                return self.new_tok(*token_type);
            }
        }
        if let Some(match_) = NAME.find(c) {
            self.index = match_.end();
            return self.new_tok(Name);
        }
             //(&*COMMENT, PythonTokenType::Comment)];


        None
    }

}

