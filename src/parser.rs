use crate::lexer::{Lexer, Token, TokenKind};

#[derive(Debug)]
pub struct Program {
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


pub struct Parser<'src> {
    lexer: Lexer<'src>,
}

impl<'src> Parser<'src> {
    pub fn new(source: &'src str) -> Self {
        Parser {
            lexer: Lexer::new(source.chars())
        }
    }

    pub fn parse(&mut self) -> Program {
        let mut expressions = Vec::new();
        while let Some(e) = self.expression() {
            expressions.push(e)
        }
        Program { expressions }
    }

    fn expression(&mut self) -> Option<Expression> {
        self.eat().and_then(|token: Token| {
            match token.kind {
                TokenKind::Str => Some(Expression::Literal { token }),
                TokenKind::Identifier => self.call(token),
                _ => None
            }
        })
    }

    fn call(&mut self, _identifier: Token) -> Option<Expression> {
        todo!()
    }

    fn eat(&mut self) -> Option<Token> {
        self.lexer.next()
    }

    fn peek(&self) -> Option<Token> {
        self.lexer.clone().next()
    }
}