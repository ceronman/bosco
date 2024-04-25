#[cfg(test)]
mod test;

use crate::lexer::{Lexer, Token, TokenKind};

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
    Literal {
        token: Token,
    },
}

#[derive(Debug)]
pub struct ParseError {
    msg: String,
    start: usize,
    end: usize,
}

type Result<T> = std::result::Result<T, ParseError>;

pub struct Parser<'src> {
    token: Token,
    lexer: Lexer<'src>,
}

impl<'src> Parser<'src> {
    pub fn new(source: &'src str) -> Self {
        let mut lexer = Lexer::new(source.chars());
        Parser {
            token: lexer.next_token(),
            lexer,
        }
    }

    pub fn parse(&mut self) -> Result<Module> {
        let mut expressions = Vec::new();
        while self.token.kind != TokenKind::Eof {
            let expr = self.expression()?;
            expressions.push(expr);
        }
        Ok(Module { expressions })
    }

    fn expression(&mut self) -> Result<Expression> {
        match self.token.kind {
            TokenKind::Str => self.literal(),
            TokenKind::Identifier => self.call(),
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
            TokenKind::Str => Ok(Expression::Literal { token }),
            _ => Err(ParseError {
                msg: format!("Expected literal, got {:?}", token.kind),
                start: token.start,
                end: token.end,
            }),
        }
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

    fn eat(&mut self) -> Token {
        let prev = self.token;
        self.token = self.lexer.next_token();
        prev
    }

    fn peek(&self) -> Token {
        self.token
    }

    fn expect(&mut self, token_kind: TokenKind) -> Result<Token> {
        let token = self.peek();
        if token.kind == token_kind {
            self.token = self.lexer.next_token();
            return Ok(token);
        }

        Err(ParseError {
            msg: format!("Expected token {:?}, got {:?}", token_kind, token.kind),
            start: token.start,
            end: token.end,
        })
    }
}
