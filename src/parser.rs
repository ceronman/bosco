use crate::ast::StmtKind::{Assignment, ExprStmt};
use crate::ast::{
    BinOp, BinOpKind, Expr, ExprKind, Field, Function, Identifier, Item, ItemKind, LiteralKind,
    Module, Node, NodeId, Param, Record, Stmt, StmtKind, Symbol, Type, TypeParam, UnOp, UnOpKind,
};
use crate::error::{parse_error, CompilerResult};
use crate::lexer::{Lexer, Span, Token, TokenKind};
use std::rc::Rc;

#[cfg(test)]
mod test;

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

    fn parse(&mut self) -> CompilerResult<Module> {
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
            items: items.into(),
        })
    }

    fn item(&mut self) -> CompilerResult<Item> {
        match self.token.kind {
            TokenKind::Fn | TokenKind::Export => self.function(),
            TokenKind::Record => self.record(),
            other => Err(parse_error!(
                self.token.span,
                "Expected declaration, got {other:?}"
            )),
        }
    }

    fn function(&mut self) -> CompilerResult<Item> {
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
                params: params.into(),
                body,
            }),
        })
    }

    fn record(&mut self) -> CompilerResult<Item> {
        let record_keyword = self.expect(TokenKind::Record)?;
        let name =
            self.identifier(|t| format!("Expected record name, found {:?} instead", t.kind))?;
        self.expect(TokenKind::LBrace)?;
        let mut fields = Vec::new();
        while self.token.kind != TokenKind::RBrace {
            self.maybe_eol();
            fields.push(self.field()?);
            self.maybe_eol();
        }
        let rparen = self.expect(TokenKind::RBrace)?;
        Ok(Item {
            node: self.node(record_keyword.span, rparen.span),
            kind: ItemKind::Record(Record {
                name,
                fields: fields.into(),
            }),
        })
    }

    fn identifier(&mut self, msg: impl Fn(Token) -> String) -> CompilerResult<Identifier> {
        let token = self.expect_msg(TokenKind::Identifier, msg)?;
        let symbol = token.span.as_str(self.source).into();
        Ok(Identifier {
            node: self.node(token.span, token.span),
            symbol,
        })
    }

    fn ty(&mut self) -> CompilerResult<Type> {
        let start = self.token;
        let pointer = self.eat(TokenKind::Star);
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
            node: self.node(start.span, end),
            pointer,
            name,
            params: params.into(),
        })
    }

    fn type_parameter(&mut self) -> CompilerResult<TypeParam> {
        let token = self.token;
        let param = match token.kind {
            TokenKind::Identifier => TypeParam::Type(Rc::new(self.ty()?)),
            TokenKind::Int => {
                // TODO: Duplicate with literal int parsing
                let value = token.span.as_str(self.source);
                let value: u32 = value.parse().map_err(|e| {
                    parse_error!(
                        token.span,
                        "Unable to parse const type parameter {value}: {e}"
                    )
                })?;
                self.advance();
                TypeParam::Const(value)
            }
            _ => return Err(parse_error!(self.token.span, "Expected type parameter")),
        };
        Ok(param)
    }

    fn param(&mut self) -> CompilerResult<Param> {
        let name =
            self.identifier(|t| format!("Expected param name, found {:?} instead", t.kind))?;
        let ty = self.ty()?;
        Ok(Param { name, ty })
    }

    fn field(&mut self) -> CompilerResult<Field> {
        let name =
            self.identifier(|t| format!("Expected field name, found {:?} instead", t.kind))?;
        let ty = self.ty()?;
        Ok(Field { name, ty })
    }

    fn statement(&mut self) -> CompilerResult<Stmt> {
        self.maybe_eol();
        match self.token.kind {
            TokenKind::LBrace => self.block(),
            TokenKind::Let => self.declaration(),
            TokenKind::If => self.if_statement(),
            TokenKind::While => self.while_statement(),
            TokenKind::Return => self.return_statement(),
            _ => self.expr_stmt(),
        }
    }

    fn expression_precedence(&mut self, min_precedence: u8) -> CompilerResult<Expr> {
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
                return Err(parse_error!(
                    self.token.span,
                    "Expected expression, got {other_kind:?}"
                ))
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
                TokenKind::Dot => self.field_access(prefix)?,
                _ => self.binary_expr(prefix, precedence)?,
            };
        }

        Ok(prefix)
    }

    fn grouping(&mut self) -> CompilerResult<Expr> {
        let lparen = self.expect(TokenKind::LParen)?;
        let inner = self.expression()?;
        let rparen = self.expect(TokenKind::RParen)?;
        Ok(Expr {
            node: self.node(lparen.span, rparen.span),
            kind: inner.kind,
        })
    }

    fn unary_expr(&mut self) -> CompilerResult<Expr> {
        let Some(precedence) = self.prefix_precedence() else {
            return Err(parse_error!(self.token.span, "Unknown infix precedence"));
        };
        let operator = self.unary_operator()?;
        let right = self.expression_precedence(precedence)?;
        Ok(Expr {
            node: self.node(operator.node.span, right.node.span),
            kind: ExprKind::Unary {
                operator,
                right: Rc::new(right),
            },
        })
    }

    fn call(&mut self, prefix: Expr) -> CompilerResult<Expr> {
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
                callee: Rc::new(prefix),
                args: args.into(),
            },
        })
    }

    fn array_index(&mut self, prefix: Expr) -> CompilerResult<Expr> {
        self.expect(TokenKind::LBracket)?;
        self.maybe_eol();
        let index = self.expression()?;
        let rbracket = self.expect(TokenKind::RBracket)?;
        Ok(Expr {
            node: self.node(prefix.node.span, rbracket.span),
            kind: ExprKind::ArrayIndex {
                expr: Rc::new(prefix),
                index: Rc::new(index),
            },
        })
    }

    fn field_access(&mut self, prefix: Expr) -> CompilerResult<Expr> {
        self.expect(TokenKind::Dot)?;
        self.maybe_eol();
        let field =
            self.identifier(|t| format!("Expected field name, found {:?} instead", t.kind))?;
        Ok(Expr {
            node: self.node(prefix.node.span, field.node.span),
            kind: ExprKind::FieldAccess {
                expr: Rc::new(prefix),
                field,
            },
        })
    }

    fn binary_expr(&mut self, prefix: Expr, precedence: u8) -> CompilerResult<Expr> {
        let operator = self.binary_operator()?;
        let right = self.expression_precedence(precedence + 1)?;
        Ok(Expr {
            node: self.node(prefix.node.span, right.node.span),
            kind: ExprKind::Binary {
                left: Rc::new(prefix),
                right: Rc::new(right),
                operator,
            },
        })
    }

    fn binary_operator(&mut self) -> CompilerResult<BinOp> {
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
            _ => {
                return Err(parse_error!(
                    self.token.span,
                    "Invalid binary operator {op:?}"
                ))
            }
        };
        self.advance();
        Ok(BinOp {
            node: self.node(op.span, op.span),
            kind,
        })
    }

    fn unary_operator(&mut self) -> CompilerResult<UnOp> {
        let op = self.token;
        let kind = match op.kind {
            TokenKind::Minus => UnOpKind::Neg,
            TokenKind::Not => UnOpKind::Not,
            _ => {
                return Err(parse_error!(
                    self.token.span,
                    "Invalid unary operator {op:?}"
                ))
            }
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
            Dot | LParen            => Some(8),
            LBracket                => Some(7),
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

    fn expression(&mut self) -> CompilerResult<Expr> {
        self.expression_precedence(0)
    }

    fn literal(&mut self) -> CompilerResult<Expr> {
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
                let value: i32 = value.parse().map_err(|e| {
                    parse_error!(token.span, "Unable to parse integer {value}: {e}")
                })?;
                ExprKind::Literal(LiteralKind::Int(value))
            }
            TokenKind::Float => {
                let value = token.span.as_str(self.source);
                let value: f64 = value
                    .parse()
                    .map_err(|e| parse_error!(token.span, "Unable to parse float {value}: {e}"))?;
                ExprKind::Literal(LiteralKind::Float(value))
            }
            _ => {
                return Err(parse_error!(
                    self.token.span,
                    "Expected literal, got {:?}",
                    token.kind
                ))
            }
        };
        self.advance();
        Ok(Expr {
            node: self.node(token.span, token.span),
            kind,
        })
    }

    fn variable(&mut self) -> CompilerResult<Expr> {
        let name =
            self.identifier(|t| format!("Expected variable name, found {:?} instead", t.kind))?;
        Ok(Expr {
            node: name.node,
            kind: ExprKind::Variable(name),
        })
    }

    fn expr_stmt(&mut self) -> CompilerResult<Stmt> {
        let expr = self.expression()?;

        if self.eat(TokenKind::Equal) {
            let value = self.expression()?;
            Ok(Stmt {
                node: self.node(expr.node.span, value.node.span),
                kind: Assignment {
                    target: expr,
                    value,
                },
            })
        } else {
            Ok(Stmt {
                node: self.node(expr.node.span, expr.node.span),
                kind: ExprStmt(expr),
            })
        }
    }

    fn declaration(&mut self) -> CompilerResult<Stmt> {
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

    fn if_statement(&mut self) -> CompilerResult<Stmt> {
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
                then_block: Rc::new(then_block),
                else_block: else_block.map(Rc::new),
            },
        })
    }

    fn block(&mut self) -> CompilerResult<Stmt> {
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
            kind: StmtKind::Block {
                statements: statements.into(),
            },
        })
    }

    fn while_statement(&mut self) -> CompilerResult<Stmt> {
        let while_kw = self.expect(TokenKind::While)?;
        let condition = self.expression()?;
        let body = self.block()?;
        Ok(Stmt {
            node: self.node(while_kw.span, body.node.span),
            kind: StmtKind::While {
                condition,
                body: Rc::new(body),
            },
        })
    }

    fn return_statement(&mut self) -> CompilerResult<Stmt> {
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

    // fn peek(&self) -> Token {
    //     self.lexer.clone().next_non_trivial_token()
    // }

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

    fn expect(&mut self, token_kind: TokenKind) -> CompilerResult<Token> {
        self.expect_msg(token_kind, |token| {
            format!("Expected token {:?}, got {:?}", token_kind, token.kind)
        })
    }

    fn expect_msg(
        &mut self,
        token_kind: TokenKind,
        msg: impl Fn(Token) -> String,
    ) -> CompilerResult<Token> {
        let token = self.token;
        if token.kind == token_kind {
            self.advance();
            return Ok(token);
        }

        Err(parse_error!(self.token.span, "{}", msg(token)))
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

pub fn parse(src: &str) -> CompilerResult<Module> {
    let mut parser = Parser::new(src);
    parser.parse()
}
