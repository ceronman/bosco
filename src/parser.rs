#[cfg(test)]
mod test;

use crate::ast::Expression::Binary;
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
            TokenKind::Identifier => match self.peek().kind {
                TokenKind::LParen => self.call(),
                TokenKind::Equals => self.assignment(),
                kind => self.error(format!("Unexpected token when parsing statement {kind:?}")),
            },
            other_kind => self.error(format!("Expected statement, got {other_kind:?}")),
        }
    }

    fn expression_precedence(&mut self, min_precedence: u8) -> Result<Expression> {
        let mut left = match self.token.kind {
            TokenKind::LParen => {
                self.eat();
                let inner = self.expression()?;
                self.expect(TokenKind::RParen)?;
                inner
            },
            _ => self.expression_atom()?
        };

        loop {
            let operator = self.token;
            let Some(precedence) = self.binary_precedence(operator.kind) else {
                break;
            };
            if precedence < min_precedence {
                break;
            }
            self.eat();
            let right = self.expression_precedence(precedence + 1)?;
            left = Binary {
                left: Box::new(left),
                right: Box::new(right),
                operator,
            };
        }
        Ok(left)
    }

    fn binary_precedence(&self, operator: TokenKind) -> Option<u8> {
        match operator {
            TokenKind::Plus => Some(1),
            TokenKind::Minus => Some(1),
            TokenKind::Star => Some(2),
            TokenKind::Slash => Some(2),
            TokenKind::Percent => Some(2),
            _ => None,
        }
    }

    fn expression_atom(&mut self) -> Result<Expression> {
        match self.token.kind {
            TokenKind::Str | TokenKind::Number => self.literal(),
            TokenKind::Identifier => self.variable(),
            other_kind => self.error(format!("Expected expression, got {other_kind:?}")),
        }
    }

    fn expression(&mut self) -> Result<Expression> {
        self.expression_precedence(0)
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
            _ => self.error(format!("Expected literal, got {:?}", token.kind)),
        }
    }

    fn variable(&mut self) -> Result<Expression> {
        Ok(Expression::Variable { name: self.eat() })
    }

    fn call(&mut self) -> Result<Statement> {
        let callee = self.expect(TokenKind::Identifier)?;
        self.expect(TokenKind::LParen)?;
        let arg = self.expression()?;
        self.expect(TokenKind::RParen)?;
        Ok(Statement::Call {
            callee,
            args: vec![arg],
        })
    }

    fn assignment(&mut self) -> Result<Statement> {
        let name = self.expect(TokenKind::Identifier)?;
        self.expect(TokenKind::Equals)?;
        let value = self.expression()?;
        Ok(Statement::Assignment { name, value })
    }

    fn declaration(&mut self) -> Result<Statement> {
        self.expect(TokenKind::Let)?;
        let name = self.expect(TokenKind::Identifier)?;
        let ty = self.expect(TokenKind::Identifier)?; // TODO: Better error message one missing ty
        self.expect(TokenKind::Equals)?;
        let value = self.expression()?;
        Ok(Statement::Declaration { name, ty, value })
    }

    fn maybe_eol(&mut self) {
        while let TokenKind::Eol = self.token.kind {
            self.eat();
        }
    }

    fn peek(&self) -> Token {
        self.lexer.clone().skip_ws()
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

        self.error(format!(
            "Expected token {:?}, got {:?}",
            token_kind, token.kind
        ))
    }

    fn error<T>(&self, msg: String) -> Result<T> {
        Err(ParseError {
            msg,
            start: self.token.start,
            end: self.token.end,
        })
    }
}

pub fn parse(src: &str) -> Result<Module> {
    let mut parser = Parser::new(src);
    parser.parse()
}
