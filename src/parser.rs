use crate::lexer::{Lexer, Token, TokenKind};
use crate::parser::Expression::Call;

#[derive(Debug)]
pub struct Module {
    pub expressions: Vec<Expression>
}

#[derive(Debug)]
pub enum Expression {
    Call { callee: Token, args: Vec<Expression> },
    Literal { token: Token }
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
            TokenKind::Identifier => self.call(),
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

    fn call(&mut self) -> Result<Expression> {
        let identifier = self.expect(TokenKind::Identifier)?;
        self.expect(TokenKind::LParen)?;
        let arg = self.expression()?;
        Ok(Expression::Call { callee: identifier, args: vec![arg] })
    }

    fn eat(&mut self) -> Option<Token> {
        self.lexer.next()
    }

    fn peek(&self) -> Option<Token> {
        self.lexer.clone().next()
    }

    fn expect(&mut self, token_kind: TokenKind) -> Result<Token> {
        if let Some(token) = self.peek() {
            if token.kind == token_kind {
                self.eat();
                return Ok(token)
            }
        }
        return Err("Unexpected token")
    }
}