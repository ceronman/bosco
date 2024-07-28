use std::cell::RefCell;
use std::collections::{HashMap, VecDeque};
use std::rc::Rc;

use crate::ast;
use crate::ast::{
    BinOpKind, Expr, ExprKind, Function, Identifier, Item, ItemKind, LiteralKind, Module, NodeId,
    Param, Stmt, StmtKind, Symbol, TypeParam, UnOpKind,
};
use crate::error::{CompilerError, CompilerResult, error};
use crate::lexer::Span;

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Type {
    Void,
    Int,
    Float,
    Bool,
    Array {
        inner: Rc<Type>,
        size: u32,
    },
    Record {
        fields: Rc<[TypedName]>,
    },
    Function {
        params: Rc<[TypedName]>,
        return_ty: Rc<Type>,
    },
}

#[derive(Debug, Eq, PartialEq)]
pub struct TypedName {
    name: Symbol,
    ty: Rc<Type>,
}

#[derive(Debug)]
enum ResolveState {
    Unresolved(Item),
    InProgress,
    Resolved(Type),
}

#[derive(Default)]
pub struct Resolver {
    scopes: VecDeque<HashMap<Symbol, Rc<RefCell<ResolveState>>>>,
    pub node_types: HashMap<NodeId, Type>,
}

impl Resolver {
    fn declare(
        &mut self,
        symbol: &Symbol,
        state: ResolveState,
        error_builder: impl Fn() -> CompilerError,
    ) -> CompilerResult<()> {
        let Some(scope) = self.scopes.front_mut() else {
            panic!("There are no scopes available") // TODO: Think about panics
        };

        if scope.contains_key(&symbol) {
            return Err(error_builder());
        }

        scope.insert(symbol.clone(), Rc::from(RefCell::new(state)));

        Ok(())
    }

    fn lookup(
        &mut self,
        ident: &Identifier,
        error_builder: impl Fn() -> CompilerError,
    ) -> CompilerResult<Type> {
        let state = self
            .scopes
            .iter()
            .find_map(|scope| scope.get(&ident.symbol).cloned());
        let Some(state) = state else {
            return Err(error_builder());
        };
        let ty = match &*state.borrow() {
            ResolveState::Unresolved(item) => {
                let ty = self.resolve_item(&item)?;
                ty.clone()
            }
            ResolveState::InProgress => {
                return Err(error!(
                    ident.node.span,
                    "Type '{}' contains cycles", ident.symbol
                ))
            }
            ResolveState::Resolved(ty) => return Ok(ty.clone()),
        };
        state.replace(ResolveState::Resolved(ty.clone()));
        Ok(ty)
    }

    fn begin_scope(&mut self) {
        self.scopes.push_front(Default::default())
    }

    fn end_scope(&mut self) {
        self.scopes.pop_front();
    }

    // TODO: Maybe this can be unified with `declare()`
    fn declare_builtin(&mut self, name: &str, ty: Type) -> CompilerResult<()> {
        let Some(scope) = self.scopes.front_mut() else {
            return Err(error!(
                Span(0, 0),
                "Builtin '{name}' was declared outside of any scope"
            ));
        };
        let symbol = Symbol::from(name);
        if scope.contains_key(&symbol) {
            return Err(error!(
                Span(0, 0),
                "Builtin 'name' was already declared in this scope"
            ));
        }
        scope.insert(symbol, Rc::from(RefCell::new(ResolveState::Resolved(ty))));
        Ok(())
    }

    fn collect_top_level_types(&mut self, module: &Module) -> CompilerResult<()> {
        self.declare_builtin("void", Type::Void)?;
        self.declare_builtin("int", Type::Int)?;
        self.declare_builtin("float", Type::Float)?;
        self.declare_builtin("bool", Type::Bool)?;

        // TODO: Define proper imports
        self.declare_builtin(
            "print_int",
            Type::Function {
                params: Rc::new([TypedName {
                    name: Symbol::from("value"),
                    ty: Rc::new(Type::Int),
                }]),
                return_ty: Rc::new(Type::Void),
            },
        )?;
        self.declare_builtin(
            "print_float",
            Type::Function {
                params: Rc::new([TypedName {
                    name: Symbol::from("value"),
                    ty: Rc::new(Type::Float),
                }]),
                return_ty: Rc::new(Type::Void),
            },
        )?;

        for item in &module.items {
            match &item.kind {
                ItemKind::Function(function) => {
                    self.declare(
                        &function.name.symbol,
                        ResolveState::Unresolved(item.clone()),
                        || {
                            error!(
                                function.name.node.span,
                                "Function '{}' was already defined", function.name.symbol
                            )
                        },
                    )?;
                }
                ItemKind::Record(record) => {
                    self.declare(
                        &record.name.symbol,
                        ResolveState::Unresolved(item.clone()),
                        || {
                            error!(
                                record.name.node.span,
                                "Record '{}' was already defined", record.name.symbol
                            )
                        },
                    )?;
                }
            }
        }
        Ok(())
    }

    pub fn resolve(&mut self, module: &Module) -> CompilerResult<()> {
        self.begin_scope();
        self.collect_top_level_types(module)?;
        for item in &module.items {
            self.resolve_item(item)?;
        }
        self.end_scope();
        debug_assert!(self.scopes.len() == 0);
        Ok(())
    }

    fn resolve_item(&mut self, item: &Item) -> CompilerResult<Type> {
        let ty = match &item.kind {
            ItemKind::Function(function) => self.resolve_function(function)?,

            ItemKind::Record(record) => {
                let mut fields = Vec::with_capacity(record.fields.len());
                for f in &record.fields {
                    fields.push(TypedName {
                        name: f.name.symbol.clone(),
                        ty: self.resolve_ty(&f.ty)?.into(),
                    })
                }
                Type::Record {
                    fields: Rc::from(fields),
                }
            }
        };
        Ok(ty)
    }

    fn resolve_function(&mut self, function: &Function) -> CompilerResult<Type> {
        self.begin_scope(); // TODO: Is it necessary?
        let mut params = Vec::new();
        for Param { name, ty } in &function.params {
            let param_ty = self.resolve_ty(ty)?;
            params.push(TypedName {
                name: name.symbol.clone(),
                ty: Rc::new(param_ty.clone()),
            });
            self.declare(&name.symbol, ResolveState::Resolved(param_ty), || {
                error!(
                    name.node.span,
                    "Parameter '{}' is already defined", name.symbol
                )
            })?;
        }
        self.resolve_stmt(&function.body)?;
        self.end_scope();

        let return_ty = match &function.return_ty {
            Some(t) => self.resolve_ty(t)?,
            None => Type::Void,
        };

        Ok(Type::Function {
            params: Rc::from(params),
            return_ty: Rc::from(return_ty),
        })
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
                let var_ty = self.resolve_ty(&ty)?;
                self.declare(&name.symbol, ResolveState::Resolved(var_ty.clone()), || {
                    error!(
                        name.node.span,
                        "Variable '{}' was already declared in this scope", name.symbol
                    )
                })?;
                if let Some(value) = value {
                    let initializer_ty = self.resolve_expr(value)?;
                    if var_ty != initializer_ty {
                        return Err(error!(
                            value.node.span,
                            "Type Error: expected {var_ty:?} but found {initializer_ty:?}"
                        ));
                    }
                }
            }

            StmtKind::Assignment { target, value } => {
                let target_ty = self.resolve_expr(target)?;
                let value_ty = self.resolve_expr(value)?;
                if target_ty != value_ty {
                    return Err(error!(
                        value.node.span,
                        "Type Error: expected {target_ty:?} but found {value_ty:?}"
                    ));
                }
            }

            StmtKind::If {
                condition,
                then_block,
                else_block,
            } => {
                let condition_ty = self.resolve_expr(condition)?;
                if condition_ty != Type::Bool {
                    return Err(error!(
                        condition.node.span,
                        "Type Error: condition should be 'bool', but got {condition_ty:?}"
                    ));
                }
                self.resolve_stmt(then_block)?;
                if let Some(e) = else_block {
                    self.resolve_stmt(e)?;
                }
            }

            StmtKind::While { condition, body } => {
                let condition_ty = self.resolve_expr(condition)?;
                if condition_ty != Type::Bool {
                    return Err(error!(
                        condition.node.span,
                        "Type Error: condition should be 'bool', but got {condition_ty:?}"
                    ));
                }
                self.resolve_stmt(body)?
            }

            StmtKind::Return { expr } => {
                // TODO!
                self.resolve_expr(expr)?;
            }
        }
        Ok(())
    }

    fn resolve_expr(&mut self, expr: &Expr) -> CompilerResult<Type> {
        let ty = match &expr.kind {
            ExprKind::Literal(LiteralKind::Int(_)) => Type::Int,
            ExprKind::Literal(LiteralKind::Float(_)) => Type::Float,
            ExprKind::Literal(LiteralKind::String { .. }) => Type::Int, // TODO: Add String type
            ExprKind::Literal(LiteralKind::Bool(_)) => Type::Bool,
            ExprKind::Variable(ident) => self.lookup(ident, || {
                error!(ident.node.span, "Undeclared variable '{}'", ident.symbol)
            })?,
            ExprKind::ArrayIndex { expr, index } => {
                let Type::Int = self.resolve_expr(index)? else {
                    return Err(error!(
                        index.node.span,
                        "Type Error: Array index must be Int"
                    ));
                };

                let expr_ty = self.resolve_expr(expr)?;

                let Type::Array { inner, .. } = expr_ty else {
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
            }
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
                    | BinOpKind::Gt => Type::Bool,
                    BinOpKind::And | BinOpKind::Or => {
                        if left_ty != Type::Bool {
                            return Err(error!(
                                left.node.span,
                                "Type Error: operand should be 'bool'",
                            ));
                        }
                        if right_ty != Type::Bool {
                            return Err(error!(
                                right.node.span,
                                "Type Error: operand should be 'bool'",
                            ));
                        }
                        Type::Bool
                    }
                    BinOpKind::Mod if left_ty == Type::Float => {
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
                if operator.kind == UnOpKind::Not && right_ty != Type::Bool {
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

                    let callee_ty = self.lookup(ident, || {
                        error!(ident.node.span, "Unknown function '{}'", ident.symbol)
                    })?;

                    let Type::Function { params, return_ty } = callee_ty else {
                        return Err(error!(
                            ident.node.span,
                            "'{}' is not a function", ident.symbol
                        )); // TODO: Test
                    };

                    if args.len() != params.len() {
                        return Err(error!(
                            expr.node.span,
                            "Function called with incorrect number of arguments",
                        ));
                    }
                    for (i, arg) in args.iter().enumerate() {
                        let arg_ty = self.resolve_expr(arg)?;
                        let param_ty = &params[i].ty;
                        if arg_ty != **param_ty {
                            return Err(error!(
                                arg.node.span,
                                "Type Error: argument type mismatch",
                            ));
                        }
                    }
                    (*return_ty).clone()
                } else {
                    return Err(error!(
                        callee.node.span,
                        "First class functions not supported", // TODO: Test this
                    ));
                }
            }
        };
        self.node_types.insert(expr.node.id, ty.clone());
        Ok(ty)
    }

    fn resolve_ty(&mut self, ty: &ast::Type) -> CompilerResult<Type> {
        // TODO: This is sort of a hack!
        if ty.name.symbol.as_str() == "Array" {
            let mut params = ty.params.iter();
            let Some(TypeParam::Type(inner)) = params.next() else {
                return Err(error!(
                    ty.node.span,
                    "Array requires a valid inner type parameter",
                ));
            };
            let Some(TypeParam::Const(size)) = params.next() else {
                return Err(error!(
                    ty.node.span,
                    "Array requires a valid size type parameter",
                ));
            };
            let inner = self.resolve_ty(&*inner)?;
            return Ok(Type::Array {
                inner: inner.into(),
                size: *size,
            });
        }
        return self.lookup(&ty.name, || {
            error!(ty.name.node.span, "Unknown Type '{}'", ty.name.symbol)
        });
    }
}
