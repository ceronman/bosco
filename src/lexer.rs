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

pub struct Token {
    kind: TokenKind,
    range: Range<usize>,
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
        while let Some('0'..='9') = self.peek() {
            self.advance();
        }
        self.make_token(TokenKind::Number)
    }

    fn peek(&self) -> Option<char> {
        self.current.map(|(_, c)| c)
    }

    fn advance(&mut self) -> Option<char> {
        let result = self.peek();
        self.current = self.iterator.next();
        result
    }

    fn make_token(&self, kind: TokenKind) -> Token {
        let lexeme_end = self.current.map(|(i, _)| i).unwrap_or(self.source.len());
        Token {
            kind,
            range: self.lexeme_start..lexeme_end,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::lexer::{Lexer, TokenKind};
    use TokenKind::*;

    fn lex(code: &str) -> Vec<TokenKind> {
        let mut lexer = Lexer::new(code);
        let mut token = lexer.next();
        let mut result: Vec<TokenKind> = Vec::new();
        while token.kind != TokenKind::Eof {
            result.push(token.kind);
            token = lexer.next();
        }
        result
    }
    #[test]
    fn operators() {
        assert_eq!(lex(" + - "), vec![WS, Plus, WS, Minus, WS]);
    }

    #[test]
    fn numbers() {
        assert_eq!(lex("123 0 04567"), vec![Number, WS, Number, WS, Number]);
    }
}
