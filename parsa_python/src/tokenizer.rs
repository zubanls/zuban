/*
 *  A lot of this module is inspired by parso's tokenizer.
 */
extern crate lazy_static;
extern crate regex;

use std::{collections::HashSet, str};

use parsa::{create_terminals, CodeIndex};
use regex::Regex;

const FORM_FEED: char = '\x0C';
const HEX_NUMBER: &str = r"0[xX](_?[0-9a-fA-F])+";
const BIN_NUMBER: &str = r"0[bB](_?[01])+";
const OCT_NUMBER: &str = r"0[oO](_?[0-7])+";
const DEC_NUMBER: &str = r"(0(_?0)*|[1-9](_?[0-9])*)";
const EXPONENT: &str = r"[eE][-+]?[0-9](_?[0-9])*";

lazy_static::lazy_static! {
    static ref INT_NUMBER: String = or(&[HEX_NUMBER, BIN_NUMBER, OCT_NUMBER, DEC_NUMBER]);
    static ref EXP_FLOAT: String = r"[0-9](_?[0-9])*".to_owned() + EXPONENT;
    static ref POINT_FLOAT: String = or(&[
        r"[0-9](_?[0-9])*\.([0-9](_?[0-9])*)?",
        r"\.[0-9](_?[0-9])*"]) + "(" + EXPONENT + ")?";
    static ref FLOAT_NUMBER: String = or(&[&POINT_FLOAT, &EXP_FLOAT]);
    static ref IMAG_NUMBER: String = or(&[r"[0-9](_?[0-9])*", &FLOAT_NUMBER]) + r"[jJ]";
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
        r"[+\-*/%&@`|^!=<>]=?", r"[\[\](){}]", r"[~;.,@]",
    ])));

    static ref NAME: Regex = r(r"^[A-Za-z_0-9\u0080-\uffff]+");
    static ref NEWLINE: Regex = r(r"^(\r\n?|\n)");
    static ref F_STRING_START: Regex = r(r#"^([Ff][Rr]?|[Rr][Ff])("""|'''|'|")"#);
    static ref UNICODE_CHARACTER_NAME: Regex = r(r"\{[A-Za-z0-9\-]+( [A-Za-z0-9\-]+)*\}");

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
    let not_single_quote = r#"[^\r\n'\\]"#;
    let not_double_quote = r#"[^\r\n"\\]"#;
    let with_backslash = r"\\(\r\n?|\n|.)";

    let single = "'".to_owned() + r"(" + with_backslash + "|" + not_single_quote + ")*'";
    let double = "\"".to_owned() + r"(" + with_backslash + "|" + not_double_quote + r#")*""#;
    // ?s: here in regex activates the flag "allow . to match \n"
    let single3 = "'''".to_owned() + r"((?s:\\.|'[^'\\]|'\\.|''[^'\\]|''\\.|[^'\\])*''')?";
    let double3 = "\"\"\"".to_owned() + r#"((?s:\\.|"[^"\\]|"\\.|""[^"\\]|""\\.|[^"\\])*""")?"#;

    "^".to_owned() + &or(prefixes) + &or(&[&single3, &double3, &single, &double])
}

create_terminals!(struct PyTerminal, enum TerminalType,
                  [Name, Operator, String, Bytes, Number, Endmarker, Newline, ErrorToken,
                   Indent, Dedent, ErrorDedent, FStringStart, FStringString, FStringEnd]);

#[derive(Default, Debug)]
pub struct PythonTokenizer<'a> {
    code: &'a str,

    previous_token_was_newline: bool,
    index: usize,
    ended: bool,
    indent_stack: Vec<usize>,
    parentheses_level: usize,
    f_string_stack: Vec<FStringNode>,
}

#[derive(Debug, Clone, Copy)]
enum QuoteType {
    Single,       // '
    Double,       // "
    SingleTriple, // '''
    DoubleTriple, // """
}

impl QuoteType {
    fn to_value(self) -> &'static str {
        match self {
            Self::Single => "'",
            Self::Double => "\"",
            Self::SingleTriple => "'''",
            Self::DoubleTriple => "\"\"\"",
        }
    }
}

#[derive(Debug)]
struct FStringNode {
    quote: QuoteType,
    parentheses_level: usize,
    format_spec_count: usize,
}

impl FStringNode {
    #[inline]
    fn open_parentheses(&mut self) {
        self.parentheses_level += 1;
    }

    #[inline]
    fn close_parentheses(&mut self) {
        if self.parentheses_level > 0 {
            self.parentheses_level -= 1;
        }
        if self.parentheses_level == 0 {
            // No parentheses means that the format spec is also finished.
            self.format_spec_count = 0
        }
    }

    #[inline]
    fn allow_multiline(&self) -> bool {
        match self.quote {
            QuoteType::Single | QuoteType::Double => false,
            QuoteType::SingleTriple | QuoteType::DoubleTriple => true,
        }
    }

    #[inline]
    fn in_expr(&self) -> bool {
        self.parentheses_level > self.format_spec_count
    }

    #[inline]
    fn in_format_spec(&self) -> bool {
        // In the syntax there can be multiple format_spec's nested: {x:{y:3}}
        !self.in_expr() && self.format_spec_count > 0
    }
}

impl<'a> parsa::Tokenizer<'a, PyTerminal> for PythonTokenizer<'a> {
    fn new(code: &'a str) -> Self {
        Self {
            code,
            indent_stack: vec![0],
            previous_token_was_newline: true,
            ..Default::default()
        }
    }
}

impl PythonTokenizer<'_> {
    #[inline]
    fn new_tok(
        &self,
        start: usize,
        can_contain_syntax: bool,
        type_: TerminalType,
    ) -> Option<PyTerminal> {
        Some(PyTerminal {
            start_index: start as CodeIndex,
            length: (self.index - start) as CodeIndex,
            type_,
            can_contain_syntax,
        })
    }

    #[inline]
    fn dedent_if_necessary(&mut self, indentation_count: usize) -> Option<PyTerminal> {
        if indentation_count < *self.indent_stack.last().unwrap() {
            if indentation_count > self.indent_stack[self.indent_stack.len() - 2] {
                *self.indent_stack.last_mut().unwrap() = indentation_count;
                return self.new_tok(self.index, false, TerminalType::ErrorDedent);
            }
            self.indent_stack.pop();
            return self.new_tok(self.index, false, TerminalType::Dedent);
        }
        None
    }

    #[inline]
    fn encountered_break_token(&mut self) -> Option<PyTerminal> {
        if self.parentheses_level != 0 || !self.f_string_stack.is_empty() {
            self.parentheses_level = 0;
            self.f_string_stack.clear();

            let mut indentation = 0;
            for character in self.code[..self.index].chars().rev() {
                if character == ' ' || character == '\t' {
                    indentation += 1;
                } else if character == '\n' || character == '\r' {
                    // We only want to dedent if the token is on a new line.
                    return self.dedent_if_necessary(indentation);
                } else {
                    return None;
                }
            }
        }
        None
    }

    #[inline]
    fn handle_fstring_stack(&mut self) -> Option<PyTerminal> {
        let in_expr = self.f_string_tos().in_expr();
        let mut iterator = code_from_start(self.code, self.index)
            .char_indices()
            .peekable();
        while let Some((i, character)) = iterator.next() {
            if (character == '{' || character == '}') && !in_expr {
                if let Some((_, next)) = iterator.next() {
                    // If the bracket appears again, we can just continue,
                    // it's part of the string.
                    if next != character || self.f_string_tos().in_format_spec() {
                        if let Some(t) = self.maybe_fstring_string(i) {
                            return Some(t);
                        }
                    }
                    return None;
                }
            } else if character == '"' {
                for (j, node) in self.f_string_stack.iter().enumerate() {
                    let quote = node.quote;
                    match quote {
                        QuoteType::Double => return self.end_f_string(i, j, quote),
                        QuoteType::DoubleTriple => {
                            if code_from_start(self.code, self.index + i).starts_with("\"\"\"") {
                                return self.end_f_string(i, j, quote);
                            }
                        }
                        _ => {}
                    }
                }
            } else if character == '\'' {
                for (j, node) in self.f_string_stack.iter().enumerate() {
                    let quote = node.quote;
                    match quote {
                        QuoteType::Single => return self.end_f_string(i, j, quote),
                        QuoteType::SingleTriple => {
                            if code_from_start(self.code, self.index + i).starts_with("'''") {
                                return self.end_f_string(i, j, quote);
                            }
                        }
                        _ => {}
                    }
                }
            } else if character == ':' && in_expr {
                let tos = self.f_string_tos();
                if tos.parentheses_level - tos.format_spec_count == 1 {
                    tos.format_spec_count += 1;
                    self.index += i + 1;
                    // We cannot just return None here, because otherwise := would be tokenized
                    // the wrong way.
                    return self.new_tok(self.index - 1, true, TerminalType::Operator);
                }
                // By returning here, we are making sure that the normal
                // tokenizer returns the as an operator.
                return None;
            } else if character == '\\' {
                if let Some(&(_, next)) = iterator.peek() {
                    if next == 'N' {
                        if let Some(match_) = UNICODE_CHARACTER_NAME
                            .find(code_from_start(self.code, self.index + i + 2))
                        {
                            iterator.nth(match_.end());
                            continue;
                        }
                    }
                    if next != '{' && next != '}' {
                        iterator.next();

                        if in_expr {
                            self.index += i + 2;
                            return self.new_tok(self.index - 2, false, TerminalType::ErrorToken);
                        }
                    }
                }
            } else if character == '\n' || character == '\r' {
                // Check if there is an f-string on the stack that allows no newlines.
                match self
                    .f_string_stack
                    .iter()
                    .enumerate()
                    .find(|(_, node)| !node.allow_multiline())
                {
                    None => {}
                    Some((j, _)) => {
                        if in_expr {
                            self.f_string_stack.drain(j..);
                            return self.next();
                        } else {
                            return self.maybe_fstring_string(i).or_else(|| {
                                self.f_string_stack.drain(j..);
                                // Since we have removed a few f-strings, it
                                // should be fine to just recurse.
                                self.next()
                            });
                        }
                    }
                }
            } else if character == '#' && in_expr {
                self.index += i; // The part before was whitespace
                let c = code_from_start(self.code, self.index);
                let length = c
                    .find(&['\n', '\r'] as &[_])
                    .map_or(c.len(), |index| index + 1);
                let start = self.index;
                self.index += length;
                return self.new_tok(start, false, TerminalType::ErrorToken);
            } else if character != ' ' && character != '\t' && character != FORM_FEED && in_expr {
                return None;
            }
        }
        // We are at the end of the code fragment and only the endmarker/dedent
        // tokens will appear
        None
    }

    #[inline]
    fn f_string_tos(&mut self) -> &mut FStringNode {
        // tos = top of stack
        self.f_string_stack.last_mut().unwrap()
    }

    #[inline]
    fn end_f_string(
        &mut self,
        string_length: usize,
        drain_from: usize,
        quote: QuoteType,
    ) -> Option<PyTerminal> {
        // This is the same if we are in_expr or not. The string ends no matter
        // what. It's a bit strange that in the expr case it returns an
        // fstring_string first, but this should be fine, since if there's a
        // syntax error in the parser, the error will be there anyway.
        let end = |node: &mut Self| {
            node.f_string_stack.drain(drain_from..);
            let start = node.index;
            node.index += match quote {
                QuoteType::Single | QuoteType::Double => 1,
                QuoteType::SingleTriple | QuoteType::DoubleTriple => 3,
            };
            node.new_tok(start, false, TerminalType::FStringEnd)
        };
        if self.f_string_tos().in_expr() {
            self.index += string_length;
            return end(self);
        }
        self.maybe_fstring_string(string_length)
            .or_else(|| end(self))
    }

    #[inline]
    fn is_still_part_of_f_string(&self, match_: regex::Match) -> bool {
        for node in &self.f_string_stack {
            if match_.as_str().contains(node.quote.to_value()) {
                return true;
            }
        }
        false
    }

    #[inline]
    fn maybe_fstring_string(&mut self, length: usize) -> Option<PyTerminal> {
        if length > 0 {
            let start = self.index;
            self.index += length;
            return self.new_tok(start, false, TerminalType::FStringString);
        }
        None
    }

    #[inline]
    fn skip_whitespace(&mut self) -> usize {
        let mut indentation = 0;
        let mut was_comment = false;
        let iterator = code_from_start(self.code, self.index).chars();
        for character in iterator {
            if character == '\n' || character == '\r' {
                if !self.previous_token_was_newline {
                    return indentation;
                }
                was_comment = false;
                indentation = 0;
            } else if !was_comment {
                if character == ' ' || character == '\t' || character == FORM_FEED {
                    if self.previous_token_was_newline {
                        indentation += 1;
                    }
                } else if character == '#' {
                    was_comment = true;
                    indentation = 0;
                } else if character == '\n' || character == '\r' {
                    if !self.previous_token_was_newline {
                        return indentation;
                    }
                    indentation = 0;
                } else if character == '\\' {
                    let mut found_newline = false;
                    if let Some(&c) = self.code.as_bytes().get(self.index + 1) {
                        if c == b'\r' {
                            self.index += 1;
                            found_newline = true
                        }
                    }
                    if let Some(&c) = self.code.as_bytes().get(self.index + 1) {
                        if c == b'\n' {
                            self.index += 1;
                            found_newline = true;
                        }
                    }
                    if !found_newline {
                        return indentation;
                    }
                    self.index += 1;
                    self.skip_whitespace();
                    return indentation;
                } else {
                    break;
                }
            }
            self.index += character.len_utf8();
        }
        indentation
    }

    #[inline]
    fn find_name_length(&self, code: &str) -> usize {
        for (i, character) in code.char_indices() {
            // TODO this is not correct, because we should implement str.isidentifier from CPython
            if !(character.is_alphabetic() || character == '_' || character.is_numeric() && i != 0)
            {
                return i;
            }
        }
        code.len()
    }
}

impl Iterator for PythonTokenizer<'_> {
    type Item = PyTerminal;
    fn next(&mut self) -> Option<Self::Item> {
        if self.ended {
            return None;
        }
        if !self.f_string_stack.is_empty() {
            if let Some(token) = self.handle_fstring_stack() {
                return Some(token);
            }
        }

        let indentation = self.skip_whitespace();

        let start = self.index;
        let c = code_from_start(self.code, self.index);
        if self.previous_token_was_newline {
            if let Some(&character) = c.as_bytes().first() {
                if character != b'\n'
                    && character != b'\r'
                    && self.parentheses_level == 0
                    && self.f_string_stack.is_empty()
                {
                    if indentation > *self.indent_stack.last().unwrap() {
                        self.indent_stack.push(indentation);
                        self.previous_token_was_newline = false;
                        return self.new_tok(start, false, TerminalType::Indent);
                    } else if let Some(token) = self.dedent_if_necessary(indentation) {
                        self.index -= indentation;
                        return Some(token);
                    }
                }
            }
            self.previous_token_was_newline = false;
        }

        if let Some(match_) = NUMBER.find(c) {
            self.index += match_.end();
            return self.new_tok(start, false, TerminalType::Number);
        }
        if let Some(match_) = OPERATOR.find(c) {
            let character = c.as_bytes()[0];
            if character == b';' {
                self.encountered_break_token();
            }
            self.index += match_.end();

            if character == b'(' || character == b'[' || character == b'{' {
                match self.f_string_stack.last_mut() {
                    None => self.parentheses_level += 1,
                    Some(node) => node.open_parentheses(),
                }
            } else if character == b')' || character == b']' || character == b'}' {
                match self.f_string_stack.last_mut() {
                    None => {
                        if self.parentheses_level > 0 {
                            self.parentheses_level -= 1
                        }
                    }
                    Some(node) => node.close_parentheses(),
                }
            }
            return self.new_tok(start, true, TerminalType::Operator);
        }
        let regexes = [
            (&*STRING, TerminalType::String),
            (&*BYTES, TerminalType::Bytes),
        ];
        for &(r, token_type) in &regexes {
            if let Some(match_) = r.find(c) {
                if !self.is_still_part_of_f_string(match_) {
                    let length = match_.end();
                    self.index += length;
                    if length <= 5
                        && (match_.as_str().contains("'''") || match_.as_str().contains("\"\"\""))
                    {
                        return self.new_tok(start, false, TerminalType::ErrorToken);
                    }
                    return self.new_tok(start, false, token_type);
                }
            }
        }
        if let Some(match_) = F_STRING_START.find(c) {
            if !self.is_still_part_of_f_string(match_) {
                self.index += match_.end();
                self.f_string_stack.push(FStringNode {
                    quote: {
                        let string = match_.as_str();
                        if string.contains("''") {
                            QuoteType::SingleTriple
                        } else if string.contains("\"\"") {
                            QuoteType::DoubleTriple
                        } else if string.contains('"') {
                            QuoteType::Double
                        } else {
                            QuoteType::Single
                        }
                    },
                    parentheses_level: 0,
                    format_spec_count: 0,
                });
                return self.new_tok(start, false, TerminalType::FStringStart);
            }
        }

        let name_length = self.find_name_length(c);
        if name_length > 0 {
            if ALWAYS_BREAK_NAMES.contains(&c[..name_length]) {
                self.encountered_break_token();
            }
            self.index += name_length;
            return self.new_tok(start, true, TerminalType::Name);
        }

        if let Some(match_) = NEWLINE.find(c) {
            self.index += match_.end();
            if self.parentheses_level == 0 && self.f_string_stack.is_empty() {
                self.previous_token_was_newline = true;
                return self.new_tok(start, false, TerminalType::Newline);
            } else {
                return self.next();
            }
        }

        match c.chars().next() {
            None => {
                if self.indent_stack.len() != 1 {
                    self.indent_stack.pop();
                    self.new_tok(start, false, TerminalType::Dedent)
                } else {
                    self.ended = true;
                    self.new_tok(start, false, TerminalType::Endmarker)
                }
            }
            Some(character) => {
                self.index += character.len_utf8();
                self.new_tok(start, false, TerminalType::ErrorToken)
            }
        }
    }
}

#[inline]
fn code_from_start(code: &str, index: usize) -> &str {
    // This function only exists, because the regex crate is not able to at
    // the beginning of a specific position.
    unsafe { str::from_utf8_unchecked(&code.as_bytes()[index..]) }
}

#[cfg(test)]
mod tests {
    use parsa::Tokenizer;
    use TerminalType::*;

    use super::*;
    #[allow(non_upper_case_globals)]
    const Op: TerminalType = Operator;

    macro_rules! parametrize {
        ($($name:ident $input:expr => $expected:tt;)*) => {$(
            #[test]
            #[allow(clippy::vec_init_then_push)]  // This is probably a bug.
            fn $name() {
                let string: &str = $input;
                let tokenizer = PythonTokenizer::new($input);
                let actual: Vec<_> = tokenizer.map(|t| (t.start_index as usize, t.length, t.type_)).collect();
                let mut expected = vec!$expected;
                expected.push((string.len(), 0, Endmarker));
                assert_eq!(actual, expected);
            }
        )*}
    }

    parametrize!(
        simple1 "asdf + 11" => [(0, 4, Name), (5, 1, Operator), (7, 2, Number)];
        simple2 "1foo1" => [(0, 1, Number), (1, 4, Name)];
        name1 "__" => [(0, 2, Name)];
        unicode1 "我あφ()" => [(0, 8, Name), (8, 1, Operator), (9, 1, Operator)];
        //unicode2 "மெல்லினம்" => [(0, 27, Name)];
        unicode3 "²" => [(0, 2, ErrorToken)];
        //unicode4 "ä²ö" => [(0, 2, Name), (2, 4, ErrorToken), (6, 8, Name)];
        //unicode5 "ää²¹öö" => [(0, 4, Name), (4, 8, ErrorToken), (8, 12, Name)];
        unicode6 " \x00a" => [(1, 0, Indent), (1, 1, ErrorToken), (2, 1, Name), (3, 0, Dedent)];

        string1 r#"u"test""# => [(0, 7, String)];
        string2 r#"u"""test""""# => [(0, 11, String)];
        string3 r#"U"""test""""# => [(0, 11, String)];
        string4 "u'''test'''" => [(0, 11, String)];
        string5 "U'''test'''" => [(0, 11, String)];
        string6 "r'''test'''" => [(0, 11, String)];
        string7 "R'''test'''" => [(0, 11, String)];
        string_with_escape1 r"'''test\''''" => [(0, 12, String)];
        string_with_escape2 r"R'''test\''''" => [(0, 13, String)];
        string_with_escape3 r"''\'test\''''" => [(0, 2, String), (2, 1, ErrorToken),
                                                 (3, 8, String), (11, 2, String)];
        bytes1 "b'foo'" => [(0, 6, Bytes)];
        bytes2 "br'foo'" => [(0, 7, Bytes)];
        bytes3 "rb'foo'" => [(0, 7, Bytes)];
        bytes4 "Rb'foo'" => [(0, 7, Bytes)];
        bytes5 "RB'foo'" => [(0, 7, Bytes)];
        bytes6 "B'foo'" => [(0, 6, Bytes)];
        bytes7 r#"B"foo""# => [(0, 6, Bytes)];
        bytes8 r#"rB"foo""# => [(0, 7, Bytes)];
        bytes9 r#"Br"foo""# => [(0, 7, Bytes)];
        multiline_string_error1 "''''\n" => [(0, 3, ErrorToken), (3, 1, ErrorToken), (4, 1, Newline)];
        multiline_string_error2 "'''" => [(0, 3, ErrorToken)];
        multiline_string_error3 "'''''" => [(0, 3, ErrorToken), (3, 2, String)];
        single_line_string_error1 "' \n'" => [(0, 1, ErrorToken), (2, 1, Newline), (3, 1, ErrorToken)];
        single_line_string_error2 "' \r'" => [(0, 1, ErrorToken), (2, 1, Newline), (3, 1, ErrorToken)];
        single_line_string_error3 "' \\'" => [(0, 1, ErrorToken), (2, 1, ErrorToken), (3, 1, ErrorToken)];
        single_line_string_error4 "( '''" => [(0, 1, Operator), (2, 3, ErrorToken)];

        number1 r"1_1" => [(0, 3, Number)];
        number2 r"1_1jfoo" => [(0, 4, Number), (4, 3, Name)];
        number3 r"3_111_133.13" => [(0, 12, Number)];
        number4 r".13" => [(0, 3, Number)];
        number5 r"1." => [(0, 2, Number)];
        number6 r"1.2j" => [(0, 4, Number)];
        number7 r"12e6" => [(0, 4, Number)];
        number8 r"1.2e6" => [(0, 5, Number)];
        not_number r"e2" => [(0, 2, Name)];

        backslash1 "\\\nfoo" => [(2, 3, Name)];
        backslash2 " \\\nfoo" => [(3, 0, Indent), (3, 3, Name), (6, 0, Dedent)];
        backslash3 "\\foo" => [(0, 1, ErrorToken), (1, 3, Name)];
        backslash4 "(+ \\\n 3.5)" => [(0, 1, Operator), (1, 1, Operator), (6, 3, Number), (9, 1, Operator)];

        indent1 "                str(\n\
                 from x import a\n\
                 def" => [(16, 0, Indent), (16, 3, Name), (19, 1, Operator),
                          (21, 4, Name), (26, 1, Name), (28, 6, Name), (35, 1, Name),
                          (36, 1, Newline), (37, 0, Dedent), (37, 3, Name)];
        indent2 "f\n g\n$" => [(0, 1, Name), (1, 1, Newline), (3, 0, Indent),
                               (3, 1, Name), (4, 1, Newline), (5, 0, Dedent), (5, 1, ErrorToken)];
        indent3 "  foo\n bar" => [(2, 0, Indent), (2, 3, Name), (5, 1, Newline),
                                  (7, 0, ErrorDedent), (7, 3, Name), (10, 0, Dedent)];
        indent4 "  foo\n bar \n baz" => [(2, 0, Indent), (2, 3, Name), (5, 1, Newline),
                                         (7, 0, ErrorDedent), (7, 3, Name), (11, 1, Newline),
                                         (13, 3, Name), (16, 0, Dedent)];
        weird_indent1 "  )\n foo " => [(2, 0, Indent), (2, 1, Op), (3, 1, Newline),
                                       (5, 0, ErrorDedent), (5, 3, Name), (9, 0, Dedent)];
        weird_indent2 "  (\n foo " => [(2, 0, Indent), (2, 1, Op), (5, 3, Name), (9, 0, Dedent)];
        weird_indent3 "a\n b\n  )\n c" => [
            (0, 1, Name), (1, 1, Newline), (3, 0, Indent), (3, 1, Name),
            (4, 1, Newline), (7, 0, Indent), (7, 1, Op), (8, 1, Newline),
            (10, 0, Dedent), (10, 1, Name), (11, 0, Dedent)];
        weird_indent4 " 1 \\\ndef" => [
            (1, 0, Indent), (1, 1, Number), (5, 3, Name), (8, 0, Dedent)];


        formfeed1 "  \x0C  " => [];
        formfeed2 "\x0C'''" => [(1, 0, Indent), (1, 3, ErrorToken), (4, 0, Dedent)];

        f_string1 "f'" => [(0, 2, FStringStart)];
        f_string2 "f''" => [(0, 2, FStringStart), (2, 1, FStringEnd)];
        f_string3 "f' {}'" => [(0, 2, FStringStart), (2, 1, FStringString),
                               (3, 1, Op), (4, 1, Op), (5, 1, FStringEnd)];
        f_string4 "f' {'" => [(0, 2, FStringStart), (2, 1, FStringString),
                              (3, 1, Op), (4, 1, FStringEnd)];
        f_string5 "f' '{}" => [(0, 2, FStringStart), (2, 1, FStringString),
                               (3, 1, FStringEnd), (4, 1, Op), (5, 1, Op)];
        f_string6 r"f'\''" => [(0, 2, FStringStart), (2, 2, FStringString), (4, 1, FStringEnd)];
        f_string7 "f'{ ''}'" => [(0, 2, FStringStart), (2, 1, Op), (4, 1, FStringEnd), (5, 3, String)];
        f_string8 "f'{ f''}'" => [(0, 2, FStringStart), (2, 1, Op), (4, 1, Name),
                                  (5, 1, FStringEnd), (6, 3, String)];

        f_string_format_spec1 "f'Some {x:.2f}{y}'" => [
            (0, 2, FStringStart), (2, 5, FStringString), (7, 1, Operator),
            (8, 1, Name), (9, 1, Op), (10, 3, FStringString), (13, 1, Op),
            (14, 1, Op), (15, 1, Name), (16, 1, Op), (17, 1, FStringEnd)];
        // := is a valid token, it's not valid if it's just a dot.
        f_string_format_spec2 "f'{x:=10}'" => [
            (0, 2, FStringStart), (2, 1, Op), (3, 1, Name),
            (4, 1, Op), (5, 3, FStringString), (8, 1, Op), (9, 1, FStringEnd)];
        f_string_format_spec3 "f'{(x:=10)}'" => [
            (0, 2, FStringStart), (2, 1, Op), (3, 1, Op), (4, 1, Name),
            (5, 2, Op), (7, 2, Number), (9, 1, Op), (10, 1, Op), (11, 1, FStringEnd)];
        f_string_format_spec4 "f'{1}}'" => [
            (0, 2, FStringStart), (2, 1, Op), (3, 1, Number), (4, 1, Op),
            (5, 1, Op), (6, 1, FStringEnd)];

        f_string_format_spec_nested1 "f'{x:{y:3}}'" => [
            (0, 2, FStringStart), (2, 1, Op), (3, 1, Name), (4, 1, Op),
            (5, 1, Op), (6, 1, Name), (7, 1, Op), (8, 1, FStringString),
            (9, 1, Op), (10, 1, Op), (11, 1, FStringEnd)];
        f_string_format_spec_nested2 "f'{2:{x:{\"f\"}}}'" => [
            (0, 2, FStringStart), (2, 1, Op), (3, 1, Number), (4, 1, Op),
            (5, 1, Op), (6, 1, Name), (7, 1, Op), (8, 1, Op), (9, 3, String),
            (12, 1, Op), (13, 1, Op), (14, 1, Op), (15, 1, FStringEnd)];

        f_string_multiline1 "f'''abc\ndef'''" => [(0, 4, FStringStart), (4, 7, FStringString),
                                                (11, 3, FStringEnd)];
        f_string_multiline2 "f'''abc{\n123}def'''" => [
            (0, 4, FStringStart), (4, 3, FStringString), (7, 1, Op),
            (9, 3, Number), (12, 1, Op), (13, 3, FStringString), (16, 3, FStringEnd)];
        f_string_multiline3 "f'''abc{\ndef}'''" => [
            (0, 4, FStringStart), (4, 3, FStringString), (7, 1, Op),
            (9, 3, Name), (12, 1, Op), (13, 3, ErrorToken)];

        f_string_line_continuation1 "f'abc\\\ndef'" => [
            (0, 2, FStringStart), (2, 8, FStringString), (10, 1, FStringEnd)];
        f_string_line_continuation2 "f'\\\n{123}\\\n'" => [
            (0, 2, FStringStart), (2, 2, FStringString), (4, 1, Op),
            (5, 3, Number), (8, 1, Op), (9, 2, FStringString), (11, 1, FStringEnd)];
        f_string_line_continuation3 "f'{\\\n123}'" => [
            (0, 2, FStringStart), (2, 1, Op), (3, 2, ErrorToken), (5, 3, Number), (8, 1, Op),
            (9, 1, FStringEnd)];
        // In format spec
        f_string_line_continuation4 "f'{123:.2\\\nf}'" => [
            (0, 2, FStringStart), (2, 1, Op), (3, 3, Number), (6, 1, Op),
            (7, 5, FStringString), (12, 1, Op), (13, 1, FStringEnd)];

        // A newline without a line continuation inside a single-line string is
        // wrong, and will generate an ERRORTOKEN
        f_string_newline "f'abc\ndef'" => [
            (0, 2, FStringStart), (2, 3, FStringString), (5, 1, Newline),
            (6, 3, Name), (9, 1, ErrorToken)];

        f_string_with_unicode_name1 r"f'\N{foo}'" => [
            (0, 2, FStringStart), (2, 7, FStringString), (9, 1, FStringEnd)];
        f_string_with_unicode_name2 r"f'\N{foo} {1}'" => [
            (0, 2, FStringStart), (2, 8, FStringString), (10, 1, Op),
            (11, 1, Number), (12, 1, Op), (13, 1, FStringEnd)];
        f_string_with_unicode_name3 r"f'\N'" => [
            (0, 2, FStringStart), (2, 2, FStringString), (4, 1, FStringEnd)];
        f_string_with_unicode_name4 r"f'\N{}'" => [
            (0, 2, FStringStart), (2, 2, FStringString), (4, 1, Op),
            (5, 1, Op), (6, 1, FStringEnd)];
    );
}
