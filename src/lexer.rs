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
    Percent,

    EqualEqual,
    BangEqual,
    Greater,
    GreaterEqual,
    Less,
    LessEqual,

    Not,
    Or,
    And,

    Equal,
    Bang,

    LParen,
    RParen,
    LBrace,
    RBrace,
    LBracket,
    RBracket,

    True,
    False,
    Int,
    Float,
    Identifier,
    Str,

    Let,
    If,
    Else,
    While,
    Fn,

    LineComment,
    BlockComment,

    Whitespace,
    Eol,
    Comma,

    UnterminatedCommentError,
    Error,
    Eof,
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct Span(pub usize, pub usize);

impl Span {
    pub fn as_str(self, content: &str) -> &str {
        &content[self.0..self.1]
    }
}

// TODO: Re-think the need for Hash
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
}

#[derive(Clone)]
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
            span: Span(self.start, self.offset),
        }
    }

    // TODO: Maybe make this configurable via lexer mode or move to parser
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

        match (c, self.peek()) {
            (' ' | '\t' | '\r', _) => self.whitespace(),
            ('\n', _) => self.eol(),
            ('+', _) => TokenKind::Plus,
            ('-', _) => TokenKind::Minus,
            ('*', _) => TokenKind::Star,
            ('/', Some('/')) => self.line_comment(),
            ('/', Some('*')) => self.block_comment(),
            ('/', _) => TokenKind::Slash,
            ('%', _) => TokenKind::Percent,
            ('=', Some('=')) => self.eat_and(TokenKind::EqualEqual),
            ('=', _) => TokenKind::Equal,
            ('!', Some('=')) => self.eat_and(TokenKind::BangEqual),
            ('!', _) => TokenKind::Bang,
            ('>', Some('=')) => self.eat_and(TokenKind::GreaterEqual),
            ('>', _) => TokenKind::Greater,
            ('<', Some('=')) => self.eat_and(TokenKind::LessEqual),
            ('<', _) => TokenKind::Less,
            ('(', _) => TokenKind::LParen,
            (')', _) => TokenKind::RParen,
            ('{', _) => TokenKind::LBrace,
            ('}', _) => TokenKind::RBrace,
            ('[', _) => TokenKind::LBracket,
            (']', _) => TokenKind::RBracket,
            (',', _) => TokenKind::Comma,
            ('0'..='9', _) => self.number(),
            ('"', _) => self.string(),
            (c, _) if c == '_' || c.is_alphabetic() => self.identifier(),
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
        while let Some('0'..='9') = self.peek() {
            self.eat();
        }
        if let Some('.') = self.peek() {
            self.eat();
            while let Some('0'..='9') = self.peek() {
                self.eat();
            }
            TokenKind::Float
        } else {
            TokenKind::Int
        }
    }

    fn string(&mut self) -> TokenKind {
        //TODO: Handle unterminated string!
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
            "if" => TokenKind::If,
            "else" => TokenKind::Else,
            "while" => TokenKind::While,
            "fn" => TokenKind::Fn,
            "or" => TokenKind::Or,
            "and" => TokenKind::And,
            "not" => TokenKind::Not,
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

    fn eat_and(&mut self, token_kind: TokenKind) -> TokenKind {
        self.eat();
        token_kind
    }

    fn peek(&self) -> Option<char> {
        self.chars.clone().next()
    }
}
