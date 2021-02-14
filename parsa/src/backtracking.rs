use crate::grammar::Token;

#[derive(Debug)]
pub struct BacktrackingTokenizer<T: Token, I: Iterator<Item=T>> {
    tokenizer: I,
    tokens: Vec<T>,
    next_index: usize,
}

impl<T: Token, I: Iterator<Item=T>> BacktrackingTokenizer<T, I> {
    pub fn new(tokenizer: I) -> Self {
        Self {
            tokenizer: tokenizer,
            tokens: vec!(),
            next_index: 0,
        }
    }

    #[inline]
    pub fn start(&mut self, token: &T) -> usize {
        if self.tokens.len() == 0 {
            self.tokens.push(*token);
            self.next_index = 1;
        }
        self.next_index
    }

    #[inline]
    pub fn reset(&mut self, token_index: usize) {
        self.next_index = token_index;
    }

    #[inline]
    pub fn stop(&mut self) {
        self.tokens.clear();
        self.next_index = 0;
    }
}

impl<T: Token, I: Iterator<Item=T>> Iterator for BacktrackingTokenizer<T, I> {
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> {
        if self.tokens.len() > 0 {
            match self.tokens.get(self.next_index) {
                None => {
                    self.next_index += 1;
                    let next = self.tokenizer.next();
                    if let Some(token) = next {
                        self.tokens.push(token);
                    }
                    next
                },
                Some(next) => {
                    self.next_index += 1;
                    Some(*next)
                }
            }
        } else {
            self.tokenizer.next()
        }
    }
}
