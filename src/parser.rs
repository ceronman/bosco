#[cfg(test)]
mod test;

use crate::ast::{Expression, Literal, Module, Statement};
use crate::lexer::{Lexer, Token, TokenKind};
use std::error::Error;
use std::fmt::{Display, Formatter};

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
        let mut statements = Vec::new();
        while self.token.kind != TokenKind::Eof {
            self.maybe_eol();
            let expr = self.statement()?;
            statements.push(expr);
            self.maybe_eol();
        }
        Ok(Module { statements })
    }

    fn statement(&mut self) -> Result<Statement> {
        match self.token.kind {
            TokenKind::Let => self.declaration(),
            TokenKind::Identifier => self.call(),
            other_kind => Err(ParseError {
                msg: format!("Expected statement, got {:?}", other_kind),
                start: self.token.start,
                end: self.token.end,
            }),
        }
    }

    fn expression(&mut self) -> Result<Expression> {
        match self.token.kind {
            TokenKind::Str | TokenKind::Number => self.literal(),
            TokenKind::Identifier => self.variable(),
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

    fn call(&mut self) -> Result<Statement> {
        let identifier = self.expect(TokenKind::Identifier)?;
        self.expect(TokenKind::LParen)?;
        let arg = self.expression()?;
        self.expect(TokenKind::RParen)?;
        Ok(Statement::Call {
            callee: identifier,
            args: vec![arg],
        })
    }

    fn declaration(&mut self) -> Result<Statement> {
        self.expect(TokenKind::Let)?;
        let name = self.expect(TokenKind::Identifier)?;
        let ty = self.expect(TokenKind::Identifier)?;
        self.expect(TokenKind::Equals)?;
        let value = self.expression()?;
        Ok(Statement::Declaration { name, ty, value })
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
