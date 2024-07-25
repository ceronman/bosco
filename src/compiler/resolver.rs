use std::collections::{HashMap, VecDeque};
use std::rc::Rc;

use crate::ast;
use crate::ast::{BinOpKind, Expr, ExprKind, Function, Identifier, Item, ItemKind, LiteralKind, Module, NodeId, Param, Stmt, StmtKind, Symbol, UnOpKind};
use crate::error::{CompilerResult, error};

#[derive(Debug, Clone,  Eq, PartialEq)]
enum Type {
    Void,
    Primitive(Primitive),
    Array { inner: Rc<Type>,  size: usize },
    Record { fields: Rc<[TypedName]> },
    Function { params: Rc<[TypedName]>, return_ty: Rc<Type> }
}

#[derive(Debug, Clone, Eq, PartialEq)]
enum Primitive {
    Int,
    Float,
    Bool
}

#[derive(Debug, Eq, PartialEq)]
struct TypedName {
    name: Symbol,
    ty: Rc<Type>,
}

#[derive(Debug)]
enum ResolutionState {
    Unresolved,
    Resolving(Item),
    Resolved(Type)
}

struct Resolver {
    scopes: VecDeque<HashMap<Symbol, ResolutionState>>,
    expr_types: HashMap<NodeId, Type>,
}

impl Resolver {
    fn declare(&mut self, ident: &Identifier, state: ResolutionState) -> CompilerResult<()> {
        let Some(scope) = self.scopes.front_mut() else {
            return Err(error!(
                ident.node.span,
                "Variable '{}' was declared outside of any scope", ident.symbol
            ));
        };

        if scope.contains_key(&ident.symbol) {
            return Err(error!(
                ident.node.span,
                "Variable '{}' was already declared in this scope", ident.symbol
            ));
        }

        scope.insert(ident.symbol.clone(), state);

        Ok(())
    }

    fn lookup(&mut self, ident: &Identifier) -> CompilerResult<Type> {
        for env in &self.scopes {
            if let Some(ResolutionState::Resolved(ty)) = env.get(&ident.symbol) {
                return Ok(ty.clone());
            }
        }
        Err(error!(
            ident.node.span,
            "Undeclared variable '{}'", ident.symbol
        ))
    }

    fn lookup_type(&self, _ast_ty: &ast::Type) -> CompilerResult<Type> {
        todo!()
    }

    fn begin_scope(&mut self) {
        self.scopes.push_front(Default::default())
    }

    fn end_scope(&mut self) {
        self.scopes.pop_front();
    }

    fn collect_top_level_types(&mut self, module: &Module) -> CompilerResult<()> {
        // Prelude
        let scope = self.scopes.front_mut().unwrap(); // TODO: Unwrap
        scope.insert(Symbol::from("void"), ResolutionState::Resolved(Type::Void));
        scope.insert(Symbol::from("int"), ResolutionState::Resolved(Type::Primitive(Primitive::Int)));
        scope.insert(Symbol::from("float"), ResolutionState::Resolved(Type::Primitive(Primitive::Float)));
        scope.insert(Symbol::from("bool"), ResolutionState::Resolved(Type::Primitive(Primitive::Bool)));

        for item in &module.items {
            match &item.kind {
                ItemKind::Function(_) => {}
                ItemKind::Record(record) => {
                    self.declare(&record.name, ResolutionState::Resolving(item.clone()))?;
                }
            }
        }
        Ok(())
    }

    fn resolve(&mut self, module: &Module) -> CompilerResult<()> {
        self.begin_scope();
        self.collect_top_level_types(module)?;
        for item in &module.items {
            self.resolve_item(item)?;
        }
        self.end_scope();
        debug_assert!(self.scopes.len() == 0);
        Ok(())
    }

    fn resolve_item(&mut self, item: &Item) -> CompilerResult<()> {
        match &item.kind {
            ItemKind::Function(function) => {
                self.resolve_function(function)?;
            }

            ItemKind::Record(_) => {}
        }
        Ok(())
    }

    fn resolve_function(&mut self, function: &Function) -> CompilerResult<()> {
        self.begin_scope();
        for Param { name, ty} in &function.params {
            self.declare(name, ResolutionState::Resolved(self.lookup_type(&ty)?))?;
        }
        self.resolve_stmt(&function.body)?;
        self.end_scope();
        Ok(())
    }

    fn resolve_stmt(&mut self, statement: &Stmt) -> CompilerResult<()> {
        match &statement.kind {
            StmtKind::Block { statements } => {
                self.begin_scope();
                for statement in statements {
                    self.resolve_stmt(statement)?
                }
                self.end_scope();
            }

            StmtKind::ExprStmt(expr) => {
                self.resolve_expr(expr)?;
            }

            StmtKind::Declaration { name, ty, value } => {
                self.declare(name, ResolutionState::Resolved(self.lookup_type(&ty)?))?;
                if let Some(value) = value {
                    self.resolve_expr(value)?;
                }
            }

            StmtKind::Assignment { target, value } => {
                self.resolve_expr(target)?;
                self.resolve_expr(value)?;
            }

            StmtKind::If {
                condition,
                then_block,
                else_block,
            } => {
                self.resolve_expr(condition)?;
                self.resolve_stmt(then_block)?;
                else_block.as_ref().map(|b| self.resolve_stmt(b));
            }

            StmtKind::While { condition, body } => {
                self.resolve_expr(condition)?;
                self.resolve_stmt(body)?
            }

            StmtKind::Return { expr } => {
                self.resolve_expr(expr)?;
            }
        }
        Ok(())
    }

    fn resolve_expr(&mut self, expr: &Expr) -> CompilerResult<Type> {
        let ty = match &expr.kind {
            ExprKind::Literal(LiteralKind::Int(_)) => Type::Primitive(Primitive::Int),
            ExprKind::Literal(LiteralKind::Float(_)) => Type::Primitive(Primitive::Float),
            ExprKind::Literal(LiteralKind::String { .. }) => Type::Primitive(Primitive::Int), // TODO: Add String type
            ExprKind::Literal(LiteralKind::Bool(_)) => Type::Primitive(Primitive::Bool),
            ExprKind::Variable(ident) => self.lookup(ident)?,
            ExprKind::ArrayIndex { expr, index } => {
                let Type::Primitive(Primitive::Int) = self.resolve_expr(index)? else {
                    return Err(error!(
                        index.node.span,
                        "Type Error: Array index must be Int"
                    ));
                };

                let expr_ty = self.resolve_expr(expr)?;

                let Type::Array { inner, ..} = expr_ty else {
                    return Err(error!(
                        expr.node.span,
                        "Type Error: Expecting an Array, found {expr_ty:?}"
                    ));
                };
                (*inner).clone()
            }
            ExprKind::FieldAccess { expr, field } => {
                let expr_ty = self.resolve_expr(expr)?;
                let Type::Record { fields } = expr_ty else {
                    return Err(error!(
                        expr.node.span,
                        "Type Error: Expecting an Record, found {expr_ty:?}"
                    ));
                };
                let Some(field) = fields.iter().find(|f| f.name == field.symbol) else {
                    return Err(error!(
                        expr.node.span,
                        "Type Error: unknown field {:?}", field.symbol
                    ));
                };
                (*field.ty).clone()
            },
            ExprKind::Binary {
                left,
                right,
                operator,
            } => {
                let left_ty = self.resolve_expr(left)?;
                let right_ty = self.resolve_expr(right)?;

                if left_ty != right_ty {
                    return Err(error!(
                        expr.node.span,
                        "Type Error: operator {:?} has incompatible types {left_ty:?} and {right_ty:?}", operator.kind)
                    );
                }

                match operator.kind {
                    BinOpKind::Le
                    | BinOpKind::Lt
                    | BinOpKind::Eq
                    | BinOpKind::Ne
                    | BinOpKind::Ge
                    | BinOpKind::Gt => Type::Primitive(Primitive::Bool),
                    BinOpKind::And | BinOpKind::Or => {
                        if left_ty != Type::Primitive(Primitive::Bool) {
                            return Err(error!(
                                left.node.span,
                                "Type Error: operand should be 'bool'",
                            ));
                        }
                        if right_ty != Type::Primitive(Primitive::Bool) {
                            return Err(error!(
                                right.node.span,
                                "Type Error: operand should be 'bool'",
                            ));
                        }
                        Type::Primitive(Primitive::Bool)
                    }
                    BinOpKind::Mod if left_ty == Type::Primitive(Primitive::Float) => {
                        return Err(error!(
                            expr.node.span,
                            "Type Error: '%' operator doesn't work on floats",
                        ));
                    }
                    _ => left_ty,
                }
            }

            ExprKind::Unary { operator, right } => {
                let right_ty = self.resolve_expr(right)?;
                if operator.kind == UnOpKind::Not && right_ty != Type::Primitive(Primitive::Bool) {
                    return Err(error!(
                        right.node.span,
                        "Type Error: operand should be 'bool'"
                    ));
                }
                right_ty
            }

            ExprKind::Call { callee, args } => {
                if let ExprKind::Variable(ident) = &callee.kind {
                    // TODO: hack!
                    if ident.symbol.as_str() == "print" {
                        if args.len() != 1 {
                            return Err(error!(
                                expr.node.span,
                                "The 'print' function requires a single argument",
                            ));
                        }
                        return Ok(Type::Void);
                    }

                    // let sig = self.symbol_table.lookup_function(ident)?;

                    // if args.len() != sig.params.len() {
                    //     return Err(error!(
                    //         expr.node.span,
                    //         "Function called with incorrect number of arguments",
                    //     ));
                    // }
                    for (i, arg) in args.iter().enumerate() {
                        let arg_ty = self.resolve_expr(arg)?;
                        // let param_ty = &sig.params[i];
                        // if arg_ty != *param_ty {
                        //     return Err(error!(
                        //         arg.node.span,
                        //         "Type Error: argument type mismatch",
                        //     ));
                        // }
                    }
                    // sig.return_ty.clone()
                    Type::Void
                } else {
                    return Err(error!(
                        callee.node.span,
                        "First class functions not supported",
                    ));
                }
            }
        };
        self.expr_types.insert(expr.node.id, ty.clone());
        Ok(ty)
    }
}