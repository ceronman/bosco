use crate::lexer::{Lexer, Token, TokenKind};

#[derive(Debug)]
pub struct Module {
    pub expressions: Vec<Expression>
}

#[derive(Debug)]
pub enum Expression {
    Call(Call),
    Literal { token: Token }
}

#[derive(Debug)]
pub struct Call {
    pub callee: Box<Expression>,
    pub args: Vec<Expression>
}

type Result<T> = std::result::Result<T, &'static str>;

pub struct Parser<'src> {
    lexer: Lexer<'src>,
}

impl<'src> Parser<'src> {
    pub fn new(source: &'src str) -> Self {
        Parser {
            lexer: Lexer::new(source.chars())
        }
    }

    pub fn parse(&mut self) -> Result<Module> {
        let mut expressions = Vec::new();
        while let Ok(e) = self.expression() {
            expressions.push(e)
        }
        Ok(Module { expressions })
    }

    fn expression(&mut self) -> Result<Expression> {
        match self.peek().ok_or("Unexpected EOF")?.kind {
            TokenKind::Str => self.literal(),
            _ => Err("todo")
        }
    }

    fn literal(&mut self) -> Result<Expression> {
        if let Some(token) = self.eat() {
            match token.kind {
                TokenKind::Str => Ok(Expression::Literal { token }),
                _ => Err("Unexpected token")
            }
        } else {
            Err("Unexpected EOF")
        }
    }

    fn call(&mut self, _identifier: Token) -> Result<Expression> {
        todo!()
    }

    fn eat(&mut self) -> Option<Token> {
        self.lexer.next()
    }

    fn peek(&self) -> Option<Token> {
        self.lexer.clone().next()
    }

    fn expect(&mut self, token_kind: TokenKind, msg: &'static str) -> Result<Token> {
        if let Some(token) = self.peek() {
            if token.kind == token_kind {
                self.eat();
                return Ok(token)
            }
        }
        return Err(msg)
    }
}