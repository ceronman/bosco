use std::str::Chars;

#[cfg(test)]
mod test;

// TODO: Re-think the need for Hash
#[derive(Copy, Clone, Eq, PartialEq, Debug, Hash)]
pub enum TokenKind {
    Plus,
    Minus,
    Slash,
    Star,

    Equals,

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

    Let,

    LineComment,
    BlockComment,
    Whitespace,
    Eol,

    UnterminatedCommentError,
    Error,
    Eof,
}

// TODO: Re-think the need for Hash
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct Token {
    pub kind: TokenKind,
    pub start: usize,
    pub end: usize,
}

pub struct Lexer<'src> {
    source: &'src str,
    chars: Chars<'src>,
    start: usize,
    offset: usize,
}

impl<'src> Lexer<'src> {
    pub fn new(source: &'src str) -> Self {
        Self {
            source,
            chars: source.chars(),
            start: 0,
            offset: 0,
        }
    }

    pub fn next_token(&mut self) -> Token {
        self.start = self.offset;
        let c = self.eat();

        Token {
            kind: self.token_kind(c),
            start: self.start,
            end: self.offset,
        }
    }

    pub fn skip_ws(&mut self) -> Token {
        loop {
            let token = self.next_token();
            match token.kind {
                TokenKind::Whitespace => continue,
                _ => return token,
            }
        }
    }

    fn token_kind(&mut self, c: Option<char>) -> TokenKind {
        let Some(c) = c else { return TokenKind::Eof };

        match c {
            ' ' | '\t' | '\r' => self.whitespace(),
            '\n' => self.eol(),
            '+' => TokenKind::Plus,
            '-' => TokenKind::Minus,
            '*' => TokenKind::Star,
            '/' => match self.peek() {
                Some('/') => self.line_comment(),
                Some('*') => self.block_comment(),
                _ => TokenKind::Slash,
            },
            '=' => TokenKind::Equals,
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

    fn eol(&mut self) -> TokenKind {
        while let Some('\n' | '\r') = self.peek() {
            self.eat();
        }
        TokenKind::Eol
    }

    fn whitespace(&mut self) -> TokenKind {
        while let Some(' ' | '\t' | '\r') = self.peek() {
            self.eat();
        }
        TokenKind::Whitespace
    }

    fn line_comment(&mut self) -> TokenKind {
        self.eat(); // Consume second '/'
        while let Some(c) = self.peek() {
            if c == '\n' {
                break;
            }
            self.eat();
        }
        TokenKind::LineComment
    }

    fn block_comment(&mut self) -> TokenKind {
        self.eat(); // Consume '*'
        let mut level = 1;
        while let Some(c) = self.eat() {
            if c == '*' && matches!(self.peek(), Some('/')) {
                self.eat();
                level -= 1;
            }
            if c == '/' && matches!(self.peek(), Some('*')) {
                self.eat();
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
            self.eat();
        }
        TokenKind::Number
    }

    fn string(&mut self) -> TokenKind {
        while let Some(c) = self.eat() {
            if c == '"' {
                break;
            }
        }
        TokenKind::Str
    }

    fn identifier(&mut self) -> TokenKind {
        while let Some(c) = self.peek() {
            if c.is_alphanumeric() || c == '_' {
                self.eat();
            } else {
                break;
            }
        }
        match &self.source[self.start..self.offset] {
            "true" => TokenKind::True,
            "false" => TokenKind::False,
            "let" => TokenKind::Let,
            _ => TokenKind::Identifier,
        }
    }

    fn eat(&mut self) -> Option<char> {
        if let Some(c) = self.chars.next() {
            self.offset += c.len_utf8();
            Some(c)
        } else {
            None
        }
    }

    fn peek(&self) -> Option<char> {
        self.chars.clone().next()
    }
}
