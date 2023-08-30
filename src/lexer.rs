use std::str::CharIndices;

#[cfg(test)]
mod test;

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum TokenKind {
    Plus,
    Minus,
    Slash,
    Star,

    LParen,
    RParen,
    LBrace,
    RBrace,
    LBracket,
    RBracket,

    True,
    False,

    Number,
    Identifier,

    Whitespace,
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
            None => {
                let kind = TokenKind::Eof;
                return Token {
                    kind,
                    start: self.lexeme_start,
                    end: self.position(),
                };
            }
        };

        let kind = match char {
            ' ' | '\t' => self.whitespace(),
            '+' => TokenKind::Plus,
            '-' => TokenKind::Minus,
            '*' => TokenKind::Star,
            '/' => TokenKind::Slash,
            '(' => TokenKind::LParen,
            ')' => TokenKind::RParen,
            '{' => TokenKind::LBrace,
            '}' => TokenKind::RBrace,
            '[' => TokenKind::LBracket,
            ']' => TokenKind::RBracket,
            '0'..='9' => self.number(),
            c if c == '_' || c.is_alphabetic() => self.identifier(),
            _ => TokenKind::Error,
        };

        Token {
            kind,
            start: self.lexeme_start,
            end: self.position(),
        }
    }

    fn whitespace(&mut self) -> TokenKind {
        while let Some(' ' | '\t') = self.peek() {
            self.advance();
        }
        TokenKind::Whitespace
    }

    fn number(&mut self) -> TokenKind {
        while let Some('0'..='9' | '_') = self.peek() {
            self.advance();
        }
        TokenKind::Number
    }

    fn identifier(&mut self) -> TokenKind {
        while let Some(c) = self.peek() {
            if c.is_alphanumeric() || c == '_' {
                self.advance();
            } else {
                break;
            }
        }
        let lexeme = &self.source[self.lexeme_start..self.position()];
        match lexeme {
            "true" => TokenKind::True,
            "false" => TokenKind::False,
            _ => TokenKind::Identifier,
        }
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
}
