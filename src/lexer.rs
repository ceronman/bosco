use std::str::Chars;

#[cfg(test)]
mod test;

#[derive(Copy, Clone, Eq, PartialEq, Debug, Hash)]
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
    Eof,
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct Token {
    pub kind: TokenKind,
    pub start: usize,
    pub end: usize,
}

// TODO: Clone is expensive here because of the String
#[derive(Debug, Clone)]
pub struct Lexer<'src> {
    chars: Chars<'src>,
    start: usize,
    offset: usize,
    lexeme: String,
}

impl<'src> Lexer<'src> {
    pub fn new(chars: Chars<'src>) -> Self {
        Self {
            chars,
            start: 0,
            offset: 0,
            lexeme: String::with_capacity(32),
        }
    }

    pub fn next_token(&mut self) -> Token {
        self.lexeme.clear();
        self.start = self.offset;
        let c = self.eat();

        Token {
            kind: self.token_kind(c),
            start: self.start,
            end: self.offset,
        }
    }

    fn token_kind(&mut self, c: Option<char>) -> TokenKind {
        let Some(c) = c else { return TokenKind::Eof };

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
        match self.lexeme.as_str() {
            "true" => TokenKind::True,
            "false" => TokenKind::False,
            _ => TokenKind::Identifier,
        }
    }

    fn eat(&mut self) -> Option<char> {
        if let Some(c) = self.chars.next() {
            self.lexeme.push(c);
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
