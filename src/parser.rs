#[cfg(test)]
mod test;

use crate::ast::StmtKind::ExprStmt;
use crate::ast::{
    BinOp, BinOpKind, Expr, ExprKind, Function, Identifier, Item, ItemKind, LiteralKind, Module,
    Node, NodeId, Param, Stmt, StmtKind, Symbol, Ty,
};
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
            token: lexer.next_token(),
            lexer,
            id_counter: 0,
        }
    }

    fn parse(&mut self) -> Result<Module> {
        let mut items = Vec::new();
        while self.token.kind != TokenKind::Eof {
            self.maybe_eol();
            let item = self.item()?;
            items.push(item);
            self.maybe_eol();
        }
        let start = items.first().map(|i| i.node.span).unwrap_or(Span(0, 0));
        let end = items.last().map(|i| i.node.span).unwrap_or(Span(0, 0));
        Ok(Module {
            _node: self.node(start, end),
            items,
        })
    }

    fn item(&mut self) -> Result<Item> {
        match self.token.kind {
            TokenKind::Fn | TokenKind::Export => self.function(),
            other => self.parse_error(format!("Expected declaration, got {other:?}")),
        }
    }

    fn function(&mut self) -> Result<Item> {
        let exported = self.eat(TokenKind::Export);
        let fn_keyword = self.expect(TokenKind::Fn)?;
        let name = self.identifier()?;
        self.expect(TokenKind::LParen)?;
        let mut params = Vec::new();
        if self.token.kind != TokenKind::RParen {
            loop {
                self.maybe_eol();
                params.push(self.param()?);

                if !self.eat(TokenKind::Comma) {
                    break;
                }
            }
        }
        self.expect(TokenKind::RParen)?;
        let return_ty = if self.token.kind == TokenKind::Identifier {
            Some(self.ty()?)
        } else {
            None
        };
        let body = self.statement()?;
        Ok(Item {
            node: self.node(fn_keyword.span, body.node.span),
            kind: ItemKind::Function(Function {
                exported,
                name,
                return_ty,
                params,
                body,
            }),
        })
    }

    fn identifier(&mut self) -> Result<Identifier> {
        let token = self.expect(TokenKind::Identifier)?;
        let symbol = token.span.as_str(self.source).into();
        Ok(Identifier {
            node: self.node(token.span, token.span),
            symbol,
        })
    }

    fn ty(&mut self) -> Result<Ty> {
        let token = self.expect_msg(TokenKind::Identifier, |token| {
            format!("Expected type, found {:?} instead", token.kind)
        })?;
        let symbol = token.span.as_str(self.source).into();
        Ok(Identifier {
            node: self.node(token.span, token.span),
            symbol,
        })
    }

    fn param(&mut self) -> Result<Param> {
        let name = self.identifier()?;
        let ty = self.ty()?;
        Ok(Param { name, ty })
    }

    fn statement(&mut self) -> Result<Stmt> {
        self.maybe_eol();
        match self.token.kind {
            TokenKind::LBrace => self.block(),
            TokenKind::Let => self.declaration(),
            TokenKind::If => self.if_statement(),
            TokenKind::While => self.while_statement(),
            TokenKind::Return => self.return_statement(),
            TokenKind::Identifier if self.peek().kind == TokenKind::Equal => self.assignment(),
            _ => self.expr_stmt(),
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

            // TODO: Ugly, cleanup!
            if let TokenKind::LParen = operator.kind {
                self.advance();
                let mut args = Vec::new();
                if self.token.kind != TokenKind::RParen {
                    loop {
                        self.maybe_eol();
                        args.push(self.expression()?);

                        if !self.eat(TokenKind::Comma) {
                            break;
                        }
                    }
                }
                let rparen = self.expect(TokenKind::RParen)?;
                left = Expr {
                    node: self.node(left.node.span, rparen.span),
                    kind: ExprKind::Call {
                        callee: Box::new(left),
                        args,
                    },
                };
                continue;
            }

            let binop = self.binop()?;

            let right = self.expression_precedence(precedence + 1)?;
            left = Expr {
                node: self.node(left.node.span, right.node.span),
                kind: ExprKind::Binary {
                    left: Box::new(left),
                    right: Box::new(right),
                    operator: binop,
                },
            }
        }
        Ok(left)
    }

    fn binop(&mut self) -> Result<BinOp> {
        let op = self.token;
        let kind = match op.kind {
            TokenKind::Plus => BinOpKind::Add,
            TokenKind::Minus => BinOpKind::Sub,
            TokenKind::Star => BinOpKind::Mul,
            TokenKind::Slash => BinOpKind::Div,
            TokenKind::Percent => BinOpKind::Mod,
            TokenKind::EqualEqual => BinOpKind::Eq,
            TokenKind::BangEqual => BinOpKind::Ne,
            TokenKind::Less => BinOpKind::Lt,
            TokenKind::LessEqual => BinOpKind::Le,
            TokenKind::Greater => BinOpKind::Gt,
            TokenKind::GreaterEqual => BinOpKind::Ge,
            TokenKind::And => BinOpKind::And,
            TokenKind::Or => BinOpKind::Or,
            _ => return self.parse_error(format!("Invalid binary operator {op:?}")),
        };
        self.advance();
        Ok(BinOp {
            node: self.node(op.span, op.span),
            kind,
        })
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
            LParen => Some(7),
            _ => None,
        }
    }

    fn expression_atom(&mut self) -> Result<Expr> {
        match self.token.kind {
            TokenKind::Str
            | TokenKind::Int
            | TokenKind::Float
            | TokenKind::False
            | TokenKind::True => self.literal(),
            TokenKind::Identifier => self.variable(),
            other_kind => self.parse_error(format!("Expected expression, got {other_kind:?}")),
        }
    }

    fn expression(&mut self) -> Result<Expr> {
        self.expression_precedence(0)
    }

    fn literal(&mut self) -> Result<Expr> {
        let token = self.token;
        let kind = match token.kind {
            TokenKind::True => ExprKind::Literal(LiteralKind::Bool(true)),
            TokenKind::False => ExprKind::Literal(LiteralKind::Bool(false)),
            TokenKind::Str => {
                // TODO: Improve parsing!
                let lexeme = self.token.span.as_str(self.source);
                let value = &lexeme[1..(lexeme.len() - 1)];
                ExprKind::Literal(LiteralKind::String(Symbol::from(value)))
            }
            TokenKind::Int => {
                let value = token.span.as_str(self.source);
                let value: i32 = value.parse().map_err(|e| ParseError {
                    msg: format!("Unable to parse integer {value}: {e}"),
                    span: token.span,
                })?;
                ExprKind::Literal(LiteralKind::Int(value))
            }
            TokenKind::Float => {
                let value = token.span.as_str(self.source);
                let value: f64 = value.parse().map_err(|e| ParseError {
                    msg: format!("Unable to parse float {value}: {e}"),
                    span: token.span,
                })?;
                ExprKind::Literal(LiteralKind::Float(value))
            }
            _ => return self.parse_error(format!("Expected literal, got {:?}", token.kind)),
        };
        self.advance();
        Ok(Expr {
            node: self.node(token.span, token.span),
            kind,
        })
    }

    fn variable(&mut self) -> Result<Expr> {
        let name = self.identifier()?;
        Ok(Expr {
            node: name.node,
            kind: ExprKind::Variable(name),
        })
    }

    fn assignment(&mut self) -> Result<Stmt> {
        let name = self.identifier()?;
        self.expect(TokenKind::Equal)?;
        let value = self.expression()?;
        Ok(Stmt {
            node: self.node(name.node.span, value.node.span),
            kind: StmtKind::Assignment { name, value },
        })
    }

    fn expr_stmt(&mut self) -> Result<Stmt> {
        let expr = self.expression()?;
        Ok(Stmt {
            node: self.node(expr.node.span, expr.node.span),
            kind: ExprStmt(expr),
        })
    }

    fn declaration(&mut self) -> Result<Stmt> {
        let let_kw = self.expect(TokenKind::Let)?;
        let name = self.identifier()?;
        let ty = self.ty()?;
        let (value, end_span) = if self.eat(TokenKind::Equal) {
            let initializer = self.expression()?;
            let span = initializer.node.span;
            (Some(initializer), span)
        } else {
            (None, ty.node.span)
        };
        Ok(Stmt {
            node: self.node(let_kw.span, end_span),
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

    fn return_statement(&mut self) -> Result<Stmt> {
        let return_kw = self.expect(TokenKind::Return)?;
        let expr = self.expression()?;
        Ok(Stmt {
            node: self.node(return_kw.span, expr.node.span),
            kind: StmtKind::Return { expr },
        })
    }

    fn maybe_eol(&mut self) {
        while self.eat(TokenKind::Eol) {}
    }

    fn peek(&self) -> Token {
        self.lexer.clone().next_non_trivial_token()
    }

    fn advance(&mut self) {
        self.token = self.lexer.next_non_trivial_token();
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
            self.advance();
            return Ok(token);
        }

        self.parse_error(msg(token))
    }

    fn parse_error<T>(&self, msg: impl Into<String>) -> Result<T> {
        Err(ParseError {
            msg: msg.into(),
            span: self.token.span,
        }
        .into())
    }

    fn node(&mut self, start: Span, end: Span) -> Node {
        let result = Node {
            id: self.id_counter,
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
