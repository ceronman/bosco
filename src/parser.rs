#[cfg(test)]
mod test;

use crate::lexer::{Lexer, Token, TokenKind};
use std::error::Error;
use std::fmt::{Display, Formatter};

#[derive(Debug)]
pub struct Module {
    pub expressions: Vec<Expression>,
}

#[derive(Debug)]
pub enum Expression {
    Call {
        callee: Token,
        args: Vec<Expression>,
    },
    Declaration {
        name: Token,
        ty: Token,
        value: Box<Expression>, // TODO: Support optional values
    },
    Literal(Literal),
    Variable {
        name: Token,
    },
}

#[derive(Debug)]
pub enum Literal {
    Number(i32),
    String { token: Token, value: String },
}

#[derive(Debug)]
pub struct ParseError {
    pub msg: String,
    pub start: usize,
    pub end: usize,
}

impl Display for ParseError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.msg)
    }
}

impl Error for ParseError {}

type Result<T> = std::result::Result<T, ParseError>;

impl Token {
    pub fn lexeme(self, source: &str) -> &str {
        &source[self.start..self.end]
    }
}

struct Parser<'src> {
    source: &'src str,
    token: Token,
    lexer: Lexer<'src>,
}

impl<'src> Parser<'src> {
    fn new(source: &'src str) -> Self {
        let mut lexer = Lexer::new(source);
        Parser {
            source,
            token: lexer.skip_ws(),
            lexer,
        }
    }

    fn parse(&mut self) -> Result<Module> {
        let mut expressions = Vec::new();
        while self.token.kind != TokenKind::Eof {
            self.maybe_eol();
            let expr = self.expression()?;
            expressions.push(expr);
            self.maybe_eol();
        }
        Ok(Module { expressions })
    }

    fn expression(&mut self) -> Result<Expression> {
        match self.token.kind {
            TokenKind::Str | TokenKind::Number => self.literal(),
            TokenKind::Let => self.declaration(),
            TokenKind::Identifier => match self.peek().kind {
                TokenKind::LParen => self.call(),
                _ => self.variable(),
            },
            other_kind => Err(ParseError {
                msg: format!("Expected expression, got {:?}", other_kind),
                start: self.token.start,
                end: self.token.end,
            }),
        }
    }

    fn literal(&mut self) -> Result<Expression> {
        let token = self.eat();
        match token.kind {
            TokenKind::Str => {
                let value = self.source[(token.start + 1)..(token.end - 1)].to_string();
                Ok(Expression::Literal(Literal::String { token, value }))
            }
            TokenKind::Number => {
                let value = token.lexeme(self.source);
                let value: i32 = value.parse().map_err(|e| ParseError {
                    msg: format!("Unable to parse number {value}: {e}"),
                    start: token.start,
                    end: token.end,
                })?;
                Ok(Expression::Literal(Literal::Number(value)))
            }
            _ => Err(ParseError {
                msg: format!("Expected literal, got {:?}", token.kind),
                start: token.start,
                end: token.end,
            }),
        }
    }

    fn variable(&mut self) -> Result<Expression> {
        Ok(Expression::Variable { name: self.eat() })
    }

    fn call(&mut self) -> Result<Expression> {
        let identifier = self.expect(TokenKind::Identifier)?;
        self.expect(TokenKind::LParen)?;
        let arg = self.expression()?;
        self.expect(TokenKind::RParen)?;
        Ok(Expression::Call {
            callee: identifier,
            args: vec![arg],
        })
    }

    fn declaration(&mut self) -> Result<Expression> {
        self.expect(TokenKind::Let)?;
        let name = self.expect(TokenKind::Identifier)?;
        let ty = self.expect(TokenKind::Identifier)?;
        self.expect(TokenKind::Equals)?;
        let value = self.expression()?;
        Ok(Expression::Declaration {
            name,
            ty,
            value: Box::new(value),
        })
    }

    fn maybe_eol(&mut self) {
        while let TokenKind::Eol = self.token.kind {
            self.eat();
        }
    }

    fn eat(&mut self) -> Token {
        let prev = self.token;
        self.token = self.lexer.skip_ws();
        prev
    }

    fn peek(&self) -> Token {
        self.lexer.clone().skip_ws()
    }

    fn expect(&mut self, token_kind: TokenKind) -> Result<Token> {
        let token = self.token;
        if token.kind == token_kind {
            self.token = self.lexer.skip_ws();
            return Ok(token);
        }

        Err(ParseError {
            msg: format!("Expected token {:?}, got {:?}", token_kind, token.kind),
            start: token.start,
            end: token.end,
        })
    }
}

pub fn parse(src: &str) -> Result<Module> {
    let mut parser = Parser::new(src);
    parser.parse()
}
