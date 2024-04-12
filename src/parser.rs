use std::borrow::Cow;

use crate::lexer::{Lexer, Token, TokenKind};

#[derive(Debug)]
pub struct Module {
    pub expressions: Vec<Expression>
}

#[derive(Debug)]
pub enum Expression {
    Call { callee: Token, args: Vec<Expression> },
    Literal { token: Token }
}

#[derive(Debug)]
pub struct ParseError {
    msg: Cow<'static, str>,
    start: usize,
    end: usize,
}

type Result<T> = std::result::Result<T, ParseError>;

pub struct Parser<'src> {
    token: Option<Token>,
    lexer: Lexer<'src>,
}

impl<'src> Parser<'src> {
    pub fn new(source: &'src str) -> Self {
        let mut lexer = Lexer::new(source.chars());
        Parser {
            token: lexer.next(),
            lexer
        }
    }

    pub fn parse(&mut self) -> Result<Module> {
        let mut expressions = Vec::new();
        while self.token.is_some() {
            let expr = self.expression()?;
            expressions.push(expr);
        }
        Ok(Module { expressions })
    }

    fn expression(&mut self) -> Result<Expression> {
        match self.peek()?.kind {
            TokenKind::Str => self.literal(),
            TokenKind::Identifier => self.call(),
            _ => Err(ParseError {
                msg: "Unexpected token".into(),
                start: 0,
                end: 0,
            })
        }
    }

    fn literal(&mut self) -> Result<Expression> {
        let token = self.eat()?;
        match token.kind {
            TokenKind::Str => Ok(Expression::Literal { token }),
            _ => Err(ParseError {
                msg: format!("Unexpected token {:?}", token.kind).into(),
                start: token.start,
                end: token.end,
            })
        }
    }

    fn call(&mut self) -> Result<Expression> {
        let identifier = self.expect(TokenKind::Identifier)?;
        self.expect(TokenKind::LParen)?;
        let arg = self.expression()?;
        Ok(Expression::Call { callee: identifier, args: vec![arg] })
    }

    fn eat(&mut self) -> Result<Token> {
        let prev= self.peek()?;
        self.advance();
        Ok(prev)
    }

    fn advance(&mut self) {
        self.token = self.lexer.next();
    }

    fn peek(&self) -> Result<Token> {
        self.token.ok_or(ParseError {
            msg: "Unexpected EOF".into(),
            start: 0,
            end: 0,
        })
    }

    fn expect(&mut self, token_kind: TokenKind) -> Result<Token> {
        let token = self.peek()?;
        if self.peek()?.kind == token_kind {
            self.advance();
            return Ok(token)
        }
        return Err(ParseError {
            msg: format!("Expected token {:?}, got {:?}", token_kind, token.kind).into(),
            start: token.start,
            end: token.end,
        })
    }
}