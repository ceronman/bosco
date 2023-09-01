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
    Str,

    LineComment,
    BlockComment,
    Whitespace,
    Eol,

    UnterminatedCommentError,
    Error,
}

#[derive(Copy, Clone, Debug)]
pub struct Token {
    pub kind: TokenKind,
    pub start: usize,
    pub end: usize,
}

#[derive(Clone, Debug)]
pub struct Lexer<'source> {
    source: &'source str,
    iterator: CharIndices<'source>,
    lexeme_start: usize,
}

impl<'source> Lexer<'source> {
    pub fn new(source: &'source str) -> Self {
        Self {
            source,
            iterator: source.char_indices(),
            lexeme_start: 0,
        }
    }

    fn next_token(&mut self) -> Option<Token> {
        self.lexeme_start = self.offset();

        self.advance().map(|c| Token {
            kind: self.token_kind(c),
            start: self.lexeme_start,
            end: self.offset(),
        })
    }

    fn token_kind(&mut self, c: char) -> TokenKind {
        match c {
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
            '"' => self.string(),
            c if c == '_' || c.is_alphabetic() => self.identifier(),
            _ => TokenKind::Error,
        }
    }

    fn whitespace(&mut self) -> TokenKind {
        while let Some(' ' | '\t' | '\r') = self.peek() {
            self.iterator.next();
        }
        TokenKind::Whitespace
    }

    fn line_comment(&mut self) -> TokenKind {
        self.advance(); // Consume second '/'
        while let Some(c) = self.peek() {
            if c == '\n' {
                break;
            }
            self.advance();
        }
        TokenKind::LineComment
    }

    fn block_comment(&mut self) -> TokenKind {
        self.advance(); // Consume '*'
        let mut level = 1;
        while let Some(c) = self.advance() {
            if c == '*' && matches!(self.peek(), Some('/')) {
                self.advance();
                level -= 1;
            }
            if c == '/' && matches!(self.peek(), Some('*')) {
                self.advance();
                level += 1;
            }
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

    fn string(&mut self) -> TokenKind {
        while let Some(c) = self.advance() {
            if c == '"' {
                break;
            }
        }
        TokenKind::Str
    }

    fn identifier(&mut self) -> TokenKind {
        while let Some(c) = self.peek() {
            if c.is_alphanumeric() || c == '_' {
                self.advance();
            } else {
                break;
            }
        }
        let lexeme = &self.source[self.lexeme_start..self.offset()];
        match lexeme {
            "true" => TokenKind::True,
            "false" => TokenKind::False,
            _ => TokenKind::Identifier,
        }
    }

    fn advance(&mut self) -> Option<char> {
        self.iterator.next().map(|(_, c)| c)
    }

    fn peek(&self) -> Option<char> {
        self.iterator.clone().next().map(|(_, c)| c)
    }

    fn offset(&self) -> usize {
        self.iterator
            .clone()
            .next()
            .map(|(i, _)| i)
            .unwrap_or(self.source.len())
    }
}

impl<'source> Iterator for Lexer<'source> {
    type Item = Token;

    fn next(&mut self) -> Option<Self::Item> {
        self.next_token()
    }
}
