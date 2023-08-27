use std::iter::Peekable;
use std::ops::Range;
use std::str::Chars;

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

    Error,
    Eof,
}

pub struct Token {
    kind: TokenKind,
    range: Range<usize>,
}

pub struct Lexer<'source> {
    source: &'source str,
    chars: Peekable<Chars<'source>>,
    current: Option<char>,
    lexeme_end: usize,
    lexeme_start: usize,
}

impl<'source> Lexer<'source> {
    pub fn new(source: &'source str) -> Self {
        let mut chars = source.chars().peekable();
        let current = chars.next();
        Self {
            source,
            chars,
            current,
            lexeme_start: 0,
            lexeme_end: 0,
        }
    }

    pub fn next(&mut self) -> Token {
        self.skip_whitespace();
        match self.advance() {
            Some(char) => match char {
                '+' => self.make_token(TokenKind::Plus),
                '-' => self.make_token(TokenKind::Minus),
                '*' => self.make_token(TokenKind::Star),
                '/' => self.make_token(TokenKind::Slash),
                _ => self.make_token(TokenKind::Error),
            },
            None => Token {
                kind: TokenKind::Eof,
                range: self.lexeme_start..self.lexeme_end,
            },
        }
    }

    fn skip_whitespace(&mut self) {
        while let Some(c) = self.current {
            match c {
                ' ' | '\t' => self.advance(),
                _ => break,
            };
        }
    }

    fn advance(&mut self) -> Option<char> {
        self.lexeme_end += 1;
        let current = self.current;
        self.current = self.chars.next();
        current
    }

    fn make_token(&self, kind: TokenKind) -> Token {
        Token {
            kind,
            range: self.lexeme_start..self.lexeme_end,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::lexer::{Lexer, TokenKind};

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
    fn it_works() {
        assert_eq!(lex("+ -"), vec![TokenKind::Plus, TokenKind::Minus]);
    }
}
