#[cfg(test)]
mod test;

use crate::ast::{Expr, ExprKind, Literal, Module, Node, NodeId, Stmt, StmtKind};
use crate::lexer::{Lexer, Span, Token, TokenKind};
use anyhow::Result;
use thiserror::Error;

#[derive(Error, Debug)]
#[error("Parse Error: {msg} at {span:?}")]
pub struct ParseError {
    pub msg: String,
    pub span: Span,
}

struct Parser<'src> {
    source: &'src str,
    token: Token,
    lexer: Lexer<'src>,
    id_counter: NodeId,
}

impl<'src> Parser<'src> {
    fn new(source: &'src str) -> Self {
        let mut lexer = Lexer::new(source);
        Parser {
            source,
            token: lexer.skip_ws(),
            lexer,
            id_counter: 0,
        }
    }

    fn parse(&mut self) -> Result<Module> {
        let start = self.token.span;
        let mut statements = Vec::new();
        while self.token.kind != TokenKind::Eof {
            self.maybe_eol();
            let expr = self.statement()?;
            statements.push(expr);
            self.maybe_eol();
        }
        let end = self.token.span;
        Ok(Module {
            statement: Stmt {
                node: self.node(start, end),
                kind: StmtKind::Block { statements },
            },
        })
    }

    fn statement(&mut self) -> Result<Stmt> {
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

    fn expression_precedence(&mut self, min_precedence: u8) -> Result<Expr> {
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
                Expr {
                    node: self.node(self.token.span, right.node.span),
                    kind: ExprKind::Not {
                        right: Box::new(right),
                    },
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
                TokenKind::Or => Expr {
                    node: self.node(left.node.span, right.node.span),
                    kind: ExprKind::Or {
                        left: Box::new(left),
                        right: Box::new(right),
                    },
                },
                TokenKind::And => Expr {
                    node: self.node(left.node.span, right.node.span),
                    kind: ExprKind::And {
                        left: Box::new(left),
                        right: Box::new(right),
                    },
                },
                _ => Expr {
                    node: self.node(left.node.span, right.node.span),
                    kind: ExprKind::Binary {
                        left: Box::new(left),
                        right: Box::new(right),
                        operator,
                    },
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

    fn expression_atom(&mut self) -> Result<Expr> {
        match self.token.kind {
            TokenKind::Str | TokenKind::Number => self.literal(),
            TokenKind::Identifier => self.variable(),
            other_kind => self.error(format!("Expected expression, got {other_kind:?}")),
        }
    }

    fn expression(&mut self) -> Result<Expr> {
        self.expression_precedence(0)
    }

    fn literal(&mut self) -> Result<Expr> {
        let token = self.token;
        let kind = match token.kind {
            TokenKind::Str => {
                let lexeme = self.token.span.as_str(self.source);
                let value = lexeme[1..(lexeme.len() - 1)].to_string(); // TODO: Improve
                self.advance();
                ExprKind::Literal(Literal::String { token, value })
            }
            TokenKind::Number => {
                let value = token.span.as_str(self.source);
                let value: i32 = value.parse().map_err(|e| ParseError {
                    msg: format!("Unable to parse number {value}: {e}"),
                    span: token.span,
                })?;
                self.advance();
                ExprKind::Literal(Literal::Number(value))
            }
            _ => return self.error(format!("Expected literal, got {:?}", token.kind)),
        };
        Ok(Expr {
            node: self.node(token.span, token.span),
            kind,
        })
    }

    fn variable(&mut self) -> Result<Expr> {
        let name = self.expect(TokenKind::Identifier)?;
        Ok(Expr {
            node: self.node(name.span, name.span),
            kind: ExprKind::Variable { name },
        })
    }

    fn call(&mut self) -> Result<Stmt> {
        let callee = self.expect(TokenKind::Identifier)?;
        self.expect(TokenKind::LParen)?;
        let args = self.arguments()?;
        let rparen = self.expect(TokenKind::RParen)?;
        Ok(Stmt {
            node: self.node(callee.span, rparen.span),
            kind: StmtKind::Call { callee, args },
        })
    }

    fn arguments(&mut self) -> Result<Vec<Expr>> {
        if self.token.kind == TokenKind::RParen {
            Ok(vec![])
        } else {
            Ok(vec![self.expression()?])
        }
    }

    fn assignment(&mut self) -> Result<Stmt> {
        let name = self.expect(TokenKind::Identifier)?;
        self.expect(TokenKind::Equal)?;
        let value = self.expression()?;
        Ok(Stmt {
            node: self.node(name.span, value.node.span),
            kind: StmtKind::Assignment { name, value },
        })
    }

    fn declaration(&mut self) -> Result<Stmt> {
        let let_kw = self.expect(TokenKind::Let)?;
        let name = self.expect(TokenKind::Identifier)?;
        let ty = self.expect_msg(TokenKind::Identifier, |token| {
            format!("Expected variable type, got {:?}", token.kind)
        })?;
        self.expect(TokenKind::Equal)?;
        let value = self.expression()?;
        Ok(Stmt {
            node: self.node(let_kw.span, value.node.span),
            kind: StmtKind::Declaration { name, ty, value },
        })
    }

    fn if_statement(&mut self) -> Result<Stmt> {
        let if_kw = self.expect(TokenKind::If)?;
        let condition = self.expression()?;
        let then_block = self.block()?;
        let else_block = if self.eat(TokenKind::Else) {
            Some(self.block()?)
        } else {
            None
        };

        Ok(Stmt {
            node: self.node(
                if_kw.span,
                else_block.as_ref().unwrap_or(&then_block).node.span,
            ),
            kind: StmtKind::If {
                condition,
                then_block: Box::new(then_block),
                else_block: else_block.map(Box::new),
            },
        })
    }

    fn block(&mut self) -> Result<Stmt> {
        let lbrace = self.expect(TokenKind::LBrace)?;
        self.maybe_eol();
        let mut statements = Vec::new();
        while self.token.kind != TokenKind::RBrace {
            statements.push(self.statement()?);
            self.maybe_eol();
        }
        let rbrace = self.expect(TokenKind::RBrace)?;
        self.maybe_eol();
        Ok(Stmt {
            node: self.node(lbrace.span, rbrace.span),
            kind: StmtKind::Block { statements },
        })
    }

    fn while_statement(&mut self) -> Result<Stmt> {
        let while_kw = self.expect(TokenKind::While)?;
        let condition = self.expression()?;
        let body = self.block()?;
        Ok(Stmt {
            node: self.node(while_kw.span, body.node.span),
            kind: StmtKind::While {
                condition,
                body: Box::new(body),
            },
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
        self.expect_msg(token_kind, |token| {
            format!("Expected token {:?}, got {:?}", token_kind, token.kind)
        })
    }

    fn expect_msg(
        &mut self,
        token_kind: TokenKind,
        msg: impl Fn(Token) -> String,
    ) -> Result<Token> {
        let token = self.token;
        if token.kind == token_kind {
            self.token = self.lexer.skip_ws();
            return Ok(token);
        }

        self.error(msg(token))
    }

    fn error<T>(&self, msg: String) -> Result<T> {
        Err(ParseError {
            msg,
            span: self.token.span,
        }
        .into())
    }

    fn node(&mut self, start: Span, end: Span) -> Node {
        let result = Node {
            _id: self.id_counter,
            span: Span(start.0, end.1),
        };
        self.id_counter += 1;
        result
    }
}

pub fn parse(src: &str) -> Result<Module> {
    let mut parser = Parser::new(src);
    parser.parse()
}
