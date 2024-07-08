#[cfg(test)]
mod test;

use crate::ast::StmtKind::ExprStmt;
use crate::ast::{
    AssignTarget, AssignTargetKind, BinOp, BinOpKind, Expr, ExprKind, Function, Identifier, Item,
    ItemKind, LiteralKind, Module, Node, NodeId, Param, Stmt, StmtKind, Symbol, Type, TypeParam,
    UnOp, UnOpKind,
};
use crate::lexer::{Lexer, Span, Token, TokenKind};
use anyhow::Result;
use std::str::FromStr;
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
        let name =
            self.identifier(|t| format!("Expected function name, found {:?} instead", t.kind))?;
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

    fn identifier(&mut self, msg: impl Fn(Token) -> String) -> Result<Identifier> {
        let token = self.expect_msg(TokenKind::Identifier, msg)?;
        let symbol = token.span.as_str(self.source).into();
        Ok(Identifier {
            node: self.node(token.span, token.span),
            symbol,
        })
    }

    fn ty(&mut self) -> Result<Type> {
        let name = self.identifier(|t| format!("Expected type, found {:?} instead", t.kind))?;
        let mut end = name.node.span;
        let mut params = Vec::new();
        if self.eat(TokenKind::Less) {
            if self.token.kind != TokenKind::Greater {
                loop {
                    self.maybe_eol();
                    params.push(self.type_parameter()?);
                    if !self.eat(TokenKind::Comma) {
                        break;
                    }
                }
            }
            end = self.expect(TokenKind::Greater)?.span;
        }

        Ok(Type {
            node: self.node(name.node.span, end),
            name,
            params,
        })
    }

    fn type_parameter(&mut self) -> Result<TypeParam> {
        let token = self.token;
        let param =
            match token.kind {
                TokenKind::Identifier => TypeParam::Type(self.identifier(|t| {
                    format!("Expected type parameter, found {:?} instead", t.kind)
                })?),
                TokenKind::Int => {
                    // TODO: Duplicate with literal int parsing
                    let value = token.span.as_str(self.source);
                    let value: u32 = value.parse().map_err(|e| ParseError {
                        msg: format!("Unable to parse const type parameter {value}: {e}"),
                        span: token.span,
                    })?;
                    self.advance();
                    TypeParam::Const(value)
                }
                _ => return self.parse_error("Expected type parameter"),
            };
        Ok(param)
    }

    fn param(&mut self) -> Result<Param> {
        let name =
            self.identifier(|t| format!("Expected param name, found {:?} instead", t.kind))?;
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
            TokenKind::Identifier
                if matches!(self.peek().kind, TokenKind::Equal | TokenKind::LBracket) =>
            {
                self.assignment()
            }
            _ => self.expr_stmt(),
        }
    }

    fn expression_precedence(&mut self, min_precedence: u8) -> Result<Expr> {
        let mut prefix = match self.token.kind {
            TokenKind::LParen => self.grouping()?,
            TokenKind::Str
            | TokenKind::Int
            | TokenKind::Float
            | TokenKind::False
            | TokenKind::True => self.literal()?,
            TokenKind::Identifier => self.variable()?,
            TokenKind::Not | TokenKind::Minus => self.unary_expr()?,

            other_kind => {
                return self.parse_error(format!("Expected expression, got {other_kind:?}"))
            }
        };

        loop {
            let Some(precedence) = self.infix_precedence() else {
                break;
            };
            if precedence < min_precedence {
                break;
            }

            prefix = match self.token.kind {
                TokenKind::LParen => self.call(prefix)?,
                TokenKind::LBracket => self.array_index(prefix)?,
                _ => self.binary_expr(prefix, precedence)?,
            };
        }

        Ok(prefix)
    }

    fn grouping(&mut self) -> Result<Expr> {
        self.expect(TokenKind::LParen)?;
        let inner = self.expression()?;
        self.expect(TokenKind::RParen)?;
        Ok(inner)
    }

    fn unary_expr(&mut self) -> Result<Expr> {
        let Some(precedence) = self.prefix_precedence() else {
            return self.parse_error("Unknown infix precedence");
        };
        let operator = self.unary_operator()?;
        let right = self.expression_precedence(precedence)?;
        Ok(Expr {
            node: self.node(operator.node.span, right.node.span),
            kind: ExprKind::Unary {
                operator,
                right: Box::new(right),
            },
        })
    }

    fn call(&mut self, prefix: Expr) -> Result<Expr> {
        self.expect(TokenKind::LParen)?;
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
        Ok(Expr {
            node: self.node(prefix.node.span, rparen.span),
            kind: ExprKind::Call {
                callee: Box::new(prefix),
                args,
            },
        })
    }

    fn array_index(&mut self, prefix: Expr) -> Result<Expr> {
        self.expect(TokenKind::LBracket)?;
        self.maybe_eol();
        let index = self.expression()?;
        let rbracket = self.expect(TokenKind::RBracket)?;
        Ok(Expr {
            node: self.node(prefix.node.span, rbracket.span),
            kind: ExprKind::ArrayIndex {
                expr: Box::new(prefix),
                index: Box::new(index),
            },
        })
    }

    fn binary_expr(&mut self, prefix: Expr, precedence: u8) -> Result<Expr> {
        let operator = self.binary_operator()?;
        let right = self.expression_precedence(precedence + 1)?;
        Ok(Expr {
            node: self.node(prefix.node.span, right.node.span),
            kind: ExprKind::Binary {
                left: Box::new(prefix),
                right: Box::new(right),
                operator,
            },
        })
    }

    fn binary_operator(&mut self) -> Result<BinOp> {
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

    fn unary_operator(&mut self) -> Result<UnOp> {
        let op = self.token;
        let kind = match op.kind {
            TokenKind::Minus => UnOpKind::Neg,
            TokenKind::Not => UnOpKind::Not,
            _ => return self.parse_error(format!("Invalid unary operator {op:?}")),
        };
        self.advance();
        Ok(UnOp {
            node: self.node(op.span, op.span),
            kind,
        })
    }

    #[rustfmt::skip]
    fn prefix_precedence(&self) -> Option<u8> {
        use TokenKind::*;
        match self.token.kind {
            Not | Minus             => Some(7),
            _                       => None
        }
    }

    #[rustfmt::skip]
    fn infix_precedence(&self) -> Option<u8> {
        use TokenKind::*;
        match self.token.kind {
            LParen | LBracket       => Some(7),
            Star | Slash | Percent  => Some(6),
            Plus | Minus            => Some(5),
            Greater | GreaterEqual
            | Less | LessEqual      => Some(4),
            EqualEqual | BangEqual  => Some(3),
            And                     => Some(2),
            Or                      => Some(1),

            _                       => None
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

    fn number<T: FromStr>(&mut self, token: Token) -> Result<T> {
        let value = token.span.as_str(self.source);
        let result: T = value.parse().map_err(|_| ParseError {
            msg: format!("Unable to parse number {value}"),
            span: token.span,
        })?;
        Ok(result)
    }

    fn variable(&mut self) -> Result<Expr> {
        let name =
            self.identifier(|t| format!("Expected variable name, found {:?} instead", t.kind))?;
        Ok(Expr {
            node: name.node,
            kind: ExprKind::Variable(name),
        })
    }

    fn assignment(&mut self) -> Result<Stmt> {
        let target = self.assign_target()?;
        self.expect(TokenKind::Equal)?;
        let value = self.expression()?;
        Ok(Stmt {
            node: self.node(target.node.span, value.node.span),
            kind: StmtKind::Assignment { target, value },
        })
    }

    fn assign_target(&mut self) -> Result<AssignTarget> {
        let name =
            self.identifier(|t| format!("Expected variable name, found {:?} instead", t.kind))?;
        let result = if self.eat(TokenKind::LBracket) {
            let index_token = self.expect(TokenKind::Int)?;
            let index: u32 = self.number(index_token)?;
            let rbracket = self.expect(TokenKind::RBracket)?;
            AssignTarget {
                node: self.node(name.node.span, rbracket.span),
                kind: AssignTargetKind::Array { name, index },
            }
        } else {
            AssignTarget {
                node: self.node(name.node.span, name.node.span),
                kind: AssignTargetKind::Variable(name),
            }
        };
        Ok(result)
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
        let name =
            self.identifier(|t| format!("Expected variable name, found {:?} instead", t.kind))?;
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
