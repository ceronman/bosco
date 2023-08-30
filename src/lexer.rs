use std::ops::Range;
use std::str::CharIndices;

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum TokenKind {
    Plus,
    Minus,
    Slash,
    Star,

    True,
    False,

    Number,
    Identifier,

    WS,
    Error,
    Eof,
}

#[derive(Copy, Clone, Debug)]
pub struct Token {
    kind: TokenKind,
    start: usize,
    end: usize,
}

pub struct Lexer<'source> {
    source: &'source str,
    iterator: CharIndices<'source>,
    current: Option<(usize, char)>,
    lexeme_start: usize,
}

impl<'source> Lexer<'source> {
    pub fn new(source: &'source str) -> Self {
        let mut iterator = source.char_indices();
        let current = iterator.next();
        Self {
            source,
            iterator,
            current,
            lexeme_start: 0,
        }
    }

    pub fn next(&mut self) -> Token {
        self.lexeme_start = self.position();
        let char = match self.advance() {
            Some(c) => c,
            None => return self.make_token(TokenKind::Eof),
        };
        match char {
            ' ' | '\t' => self.whitespace(),
            '+' => self.make_token(TokenKind::Plus),
            '-' => self.make_token(TokenKind::Minus),
            '*' => self.make_token(TokenKind::Star),
            '/' => self.make_token(TokenKind::Slash),
            '0'..='9' => self.number(),
            _ => self.make_token(TokenKind::Error),
        }
    }

    fn whitespace(&mut self) -> Token {
        while let Some(' ' | '\t') = self.peek() {
            self.advance();
        }
        self.make_token(TokenKind::WS)
    }

    fn number(&mut self) -> Token {
        while let Some('0'..='9' | '_') = self.peek() {
            self.advance();
        }
        self.make_token(TokenKind::Number)
    }

    fn peek(&self) -> Option<char> {
        self.current.map(|(_, c)| c)
    }

    fn position(&self) -> usize {
        self.current.map(|(i, _)| i).unwrap_or(self.source.len())
    }

    fn advance(&mut self) -> Option<char> {
        let result = self.peek();
        self.current = self.iterator.next();
        result
    }

    fn make_token(&self, kind: TokenKind) -> Token {
        Token {
            kind,
            start: self.lexeme_start,
            end: self.position(),
        }
    }
}

#[cfg(test)]
mod tests {
    use std::iter::from_fn;
    use crate::lexer::{Lexer, Token, TokenKind};
    use TokenKind::*;

    fn test_lexer(code: &str, expected: Vec<TokenKind>, skip_ws: bool) {
        let mut lexer = Lexer::new(code);
        let tokens: Vec<Token> = from_fn(move || {
            let token = lexer.next();
            if token.kind == Eof { None } else { Some(token) }
        }).collect();

        let kinds: Vec<TokenKind> = tokens.clone().into_iter()
            .map(|token| token.kind)
            .filter(|&kind| !skip_ws || kind != WS)
            .collect();

        assert_eq!(kinds, expected);

        let text = tokens.into_iter()
            .map(|token| &code[token.start..token.end])
            .fold(String::new(), |a, b| a + b);

        assert_eq!(text.as_str(), code);
    }
    #[test]
    fn operators() {
        test_lexer("+ -", vec![Plus, Minus], true);
    }

    #[test]
    fn numbers() {
        test_lexer("123 0 00123 123_345", vec![Number, Number, Number, Number], true);
    }
}
