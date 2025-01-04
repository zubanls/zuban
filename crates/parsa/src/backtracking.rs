use crate::grammar::Token;

#[derive(Debug)]
pub struct BacktrackingTokenizer<T: Token, I: Iterator<Item = T>> {
    tokenizer: I,
    tokens: Vec<T>,
    next_index: usize,
    is_recording: bool,
}

impl<T: Token, I: Iterator<Item = T>> BacktrackingTokenizer<T, I> {
    pub fn new(tokenizer: I) -> Self {
        Self {
            tokenizer,
            tokens: vec![],
            next_index: 0,
            is_recording: false,
        }
    }

    #[inline]
    pub fn start(&mut self, token: &T) -> usize {
        self.is_recording = true;
        if self.tokens.is_empty() {
            self.tokens.push(*token);
            self.next_index = 1;
            0
        } else {
            self.next_index - 1
        }
    }

    #[inline]
    pub fn reset(&mut self, token_index: usize) {
        self.next_index = token_index;
    }

    #[inline]
    pub fn stop(&mut self) {
        self.is_recording = false;
    }
}

impl<T: Token, I: Iterator<Item = T>> Iterator for BacktrackingTokenizer<T, I> {
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> {
        if !self.tokens.is_empty() {
            match self.tokens.get(self.next_index) {
                None => {
                    let next = self.tokenizer.next();
                    if self.is_recording {
                        self.next_index += 1;
                        if let Some(token) = next {
                            self.tokens.push(token);
                        }
                    } else {
                        self.next_index = 0;
                        self.tokens.clear();
                    }
                    next
                }
                Some(next) => {
                    self.next_index += 1;
                    Some(*next)
                }
            }
        } else {
            // is_recording is only true if there's at least one token.
            self.tokenizer.next()
        }
    }
}
