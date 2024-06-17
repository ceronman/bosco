#[cfg(test)]
mod test;

use crate::ast::{Expression, Literal, Module, Statement};
use crate::lexer::{Lexer, Token, TokenKind};
use anyhow::Result;
use thiserror::Error;

#[derive(Error, Debug)]
#[error("Parse Error: {msg} at {start}..{end}")]
pub struct ParseError {
    pub msg: String,
    pub start: usize,
    pub end: usize,
}

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
        Ok(Module {
            statement: Statement::Block { statements },
        })
    }

    fn statement(&mut self) -> Result<Statement> {
        self.maybe_eol();
        match self.token.kind {
            TokenKind::LBrace => self.block(),
            TokenKind::Let => self.declaration(),
            TokenKind::If => self.if_statement(),
            TokenKind::While => self.while_statement(),
            TokenKind::Identifier => match self.peek().kind {
                TokenKind::LParen => self.call(),
                TokenKind::Equal => self.assignment(),
                kind => self.error(format!("Unexpected token when parsing statement {kind:?}")),
            },
            other_kind => self.error(format!("Expected statement, got {other_kind:?}")),
        }
    }

    fn expression_precedence(&mut self, min_precedence: u8) -> Result<Expression> {
        // TODO: Generalize?
        let mut left = match self.token.kind {
            TokenKind::LParen => {
                self.advance();
                let inner = self.expression()?; // TODO: Prattify, test nesting
                self.expect(TokenKind::RParen)?;
                inner
            }
            TokenKind::Not => {
                self.advance();
                let right = self.expression_precedence(7)?;
                Expression::Not {
                    right: Box::new(right),
                }
            }
            _ => self.expression_atom()?,
        };

        loop {
            let operator = self.token;
            let Some(precedence) = self.binary_precedence(operator.kind) else {
                break;
            };
            if precedence < min_precedence {
                break;
            }
            self.advance();
            let right = self.expression_precedence(precedence + 1)?;

            // TODO: Generalize?
            left = match operator.kind {
                TokenKind::Or => Expression::Or {
                    left: Box::new(left),
                    right: Box::new(right),
                },
                TokenKind::And => Expression::And {
                    left: Box::new(left),
                    right: Box::new(right),
                },
                _ => Expression::Binary {
                    left: Box::new(left),
                    right: Box::new(right),
                    operator,
                },
            };
        }
        Ok(left)
    }

    fn binary_precedence(&self, operator: TokenKind) -> Option<u8> {
        use TokenKind::*;
        match operator {
            Or => Some(1),
            And => Some(2),
            EqualEqual | BangEqual => Some(3),
            Greater | GreaterEqual | Less | LessEqual => Some(4),
            Plus | Minus => Some(5),
            Star | Slash | Percent => Some(6),
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
        let token = self.token;
        match token.kind {
            TokenKind::Str => {
                let value = self.source[(token.start + 1)..(token.end - 1)].to_string();
                self.advance();
                Ok(Expression::Literal(Literal::String { token, value }))
            }
            TokenKind::Number => {
                let value = token.lexeme(self.source);
                let value: i32 = value.parse().map_err(|e| ParseError {
                    msg: format!("Unable to parse number {value}: {e}"),
                    start: token.start,
                    end: token.end,
                })?;
                self.advance();
                Ok(Expression::Literal(Literal::Number(value)))
            }
            _ => self.error(format!("Expected literal, got {:?}", token.kind)),
        }
    }

    fn variable(&mut self) -> Result<Expression> {
        Ok(Expression::Variable {
            name: self.expect(TokenKind::Identifier)?,
        })
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
        self.expect(TokenKind::Equal)?;
        let value = self.expression()?;
        Ok(Statement::Assignment { name, value })
    }

    fn declaration(&mut self) -> Result<Statement> {
        self.expect(TokenKind::Let)?;
        let name = self.expect(TokenKind::Identifier)?;
        let ty = self.expect(TokenKind::Identifier)?; // TODO: Better error message one missing ty
        self.expect(TokenKind::Equal)?;
        let value = self.expression()?;
        Ok(Statement::Declaration { name, ty, value })
    }

    fn if_statement(&mut self) -> Result<Statement> {
        self.expect(TokenKind::If)?;
        let condition = self.expression()?;
        let then_block = Box::new(self.block()?);
        let else_block = if self.eat(TokenKind::Else) {
            Some(Box::new(self.block()?))
        } else {
            None
        };

        Ok(Statement::If {
            condition,
            then_block,
            else_block,
        })
    }

    fn block(&mut self) -> Result<Statement> {
        self.expect(TokenKind::LBrace)?;
        self.maybe_eol();
        let mut statements = Vec::new();
        while self.token.kind != TokenKind::RBrace {
            statements.push(self.statement()?);
            self.maybe_eol();
        }
        self.expect(TokenKind::RBrace)?;
        self.maybe_eol();
        Ok(Statement::Block { statements })
    }

    fn while_statement(&mut self) -> Result<Statement> {
        self.expect(TokenKind::While)?;
        let condition = self.expression()?;
        let body = self.block()?;
        Ok(Statement::While {
            condition,
            body: Box::new(body),
        })
    }

    fn maybe_eol(&mut self) {
        while self.eat(TokenKind::Eol) {}
    }

    fn peek(&self) -> Token {
        self.lexer.clone().skip_ws()
    }

    fn advance(&mut self) {
        self.token = self.lexer.skip_ws();
    }

    fn eat(&mut self, kind: TokenKind) -> bool {
        if self.token.kind == kind {
            self.advance();
            true
        } else {
            false
        }
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
        }
        .into())
    }
}

pub fn parse(src: &str) -> Result<Module> {
    let mut parser = Parser::new(src);
    parser.parse()
}
