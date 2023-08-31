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

    LineComment,
    BlockComment,
    Whitespace,
    Eol,
    Eof,

    UnterminatedCommentError,
    Error,
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
            ' ' | '\t' | '\r' => self.whitespace(),
            '\n' => TokenKind::Eol,
            '+' => TokenKind::Plus,
            '-' => TokenKind::Minus,
            '*' => TokenKind::Star,
            '/' => match self.peek() {
                Some('/') => self.line_comment(),
                Some('*') => self.block_comment(),
                _ => TokenKind::Slash,
            },
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
        while let Some(' ' | '\t' | '\r') = self.peek() {
            self.advance();
        }
        TokenKind::Whitespace
    }

    fn line_comment(&mut self) -> TokenKind {
        self.advance(); // consume the second '/'
        while let Some(c) = self.peek() {
            if c != '\n' {
                self.advance();
            } else {
                break;
            }
        }
        TokenKind::LineComment
    }

    fn block_comment(&mut self) -> TokenKind {
        self.advance(); // consume '*'
        let mut level = 1;
        while let Some(c) = self.peek() {
            if c == '*' && matches!(self.peek_next(), Some('/')) {
                self.advance();
                level -= 1;
            }
            if c == '/' && matches!(self.peek_next(), Some('*')) {
                self.advance();
                level += 1;
            }
            self.advance();
            if level == 0 {
                break;
            }
        }
        if level == 0 {
            TokenKind::BlockComment
        } else {
            TokenKind::UnterminatedCommentError
        }
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

    fn peek_next(&self) -> Option<char> {
        self.iterator.clone().next().map(|(_, c)| c)
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
