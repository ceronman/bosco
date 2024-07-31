use crate::ast;
use crate::ast::{
    BinOpKind, Expr, ExprKind, Function, Identifier, Item, ItemKind, LiteralKind, Module, NodeId,
    Param, Stmt, StmtKind, Symbol, TypeParam, UnOpKind,
};
use crate::error::{error, CompilerError, CompilerResult};
use crate::lexer::Span;
use std::collections::hash_map::Entry;
use std::collections::{HashMap, VecDeque};
use std::rc::Rc;

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
        params: Rc<[Type]>,
        return_ty: Rc<Type>,
    },
}

#[derive(Debug, Eq, PartialEq)]
pub struct TypedName {
    pub name: Symbol,
    pub ty: Rc<Type>,
}

#[derive(Debug)]
enum ResolveState {
    Unresolved(Item),
    InProgress,
    Resolved(Type),
}

#[derive(Default)]
pub struct Resolver {
    module_types: HashMap<Symbol, ResolveState>,
    pub node_types: HashMap<NodeId, Type>,
    scopes: VecDeque<HashMap<Symbol, Type>>,
    context_function: Option<Type>,
}

impl Resolver {
    fn declare_type(
        &mut self,
        name: Symbol,
        state: ResolveState,
        err: impl Fn() -> CompilerError,
    ) -> CompilerResult<()> {
        match self.module_types.entry(name) {
            Entry::Occupied(_) => Err(err()),
            Entry::Vacant(v) => {
                v.insert(state);
                Ok(())
            }
        }
    }

    fn lookup_type(&mut self, ident: &Identifier) -> CompilerResult<Type> {
        let Some(state) = self.module_types.get_mut(&ident.symbol) else {
            return Err(error!(ident.node.span, "Unknown type '{}'", ident.symbol));
        };

        let ty = match state {
            ResolveState::Unresolved(item) => {
                let item = item.clone();
                *state = ResolveState::InProgress;
                self.resolve_item(&item)?
            }
            ResolveState::InProgress => {
                return Err(error!(
                    ident.node.span,
                    "Type '{}' contains cycles", ident.symbol
                ))
            }
            ResolveState::Resolved(ty) => {
                return Ok(ty.clone());
            }
        };

        let state = self.module_types.get_mut(&ident.symbol).unwrap();
        *state = ResolveState::Resolved(ty.clone());
        Ok(ty)
    }

    fn declare_local(
        &mut self,
        identifier: &Identifier,
        ty: Type,
        err: impl Fn() -> CompilerError,
    ) -> CompilerResult<()> {
        // TODO: Think about panics
        let scope = self
            .scopes
            .front_mut()
            .expect("There should be at least one scope available");

        if scope.contains_key(&identifier.symbol) {
            return Err(err());
        }

        scope.insert(identifier.symbol.clone(), ty);
        Ok(())
    }

    fn lookup_local(&mut self, ident: &Identifier) -> CompilerResult<Type> {
        return self
            .scopes
            .iter()
            .find_map(|scope| scope.get(&ident.symbol))
            .cloned()
            .ok_or_else(|| error!(ident.node.span, "Undeclared variable '{}'", ident.symbol));
    }

    fn begin_scope(&mut self) {
        self.scopes.push_front(Default::default())
    }

    fn end_scope(&mut self) {
        self.scopes.pop_front();
    }

    fn declare_builtin(&mut self, name: &str, ty: Type) -> CompilerResult<()> {
        self.declare_type(Symbol::from(name), ResolveState::Resolved(ty), || {
            error!(Span(0, 0), "Builtin '{name}' is already declared")
        })
    }

    fn declare_builtins(&mut self) -> CompilerResult<()> {
        self.declare_builtin("void", Type::Void)?;
        self.declare_builtin("int", Type::Int)?;
        self.declare_builtin("float", Type::Float)?;
        self.declare_builtin("bool", Type::Bool)?;

        // TODO: Define proper imports
        self.declare_builtin(
            "print_int",
            Type::Function {
                params: Rc::new([Type::Int]),
                return_ty: Rc::new(Type::Void),
            },
        )?;
        self.declare_builtin(
            "print_float",
            Type::Function {
                params: Rc::new([Type::Float]),
                return_ty: Rc::new(Type::Void),
            },
        )?;
        Ok(())
    }

    fn collect_top_level_types(&mut self, module: &Module) -> CompilerResult<()> {
        for item in &module.items {
            // TODO: Make name a shared field for item
            let name = match &item.kind {
                ItemKind::Function(f) => &f.name,
                ItemKind::Record(r) => &r.name,
            };
            self.declare_type(
                name.symbol.clone(),
                ResolveState::Unresolved(item.clone()),
                || {
                    error!(
                        name.node.span,
                        "{} '{}' was already defined",
                        match item.kind {
                            ItemKind::Function(_) => "Function",
                            ItemKind::Record(_) => "Record",
                        },
                        name.symbol
                    )
                },
            )?;
        }

        for item in &module.items {
            let name = match &item.kind {
                ItemKind::Function(f) => &f.name,
                ItemKind::Record(r) => &r.name,
            };
            let ty = self.lookup_type(name)?;
            self.node_types.insert(name.node.id, ty);
        }

        Ok(())
    }

    pub fn resolve(&mut self, module: &Module) -> CompilerResult<()> {
        self.declare_builtins()?;
        self.collect_top_level_types(module)?;

        self.begin_scope();

        for item in &module.items {
            match &item.kind {
                ItemKind::Function(f) => self.check_function(f)?,
                _ => {}
            }
        }
        self.end_scope();
        debug_assert!(self.scopes.len() == 0);
        Ok(())
    }

    fn resolve_item(&mut self, item: &Item) -> CompilerResult<Type> {
        let ty = match &item.kind {
            ItemKind::Function(function) => {
                let params= function.params
                    .iter().map(|p| self.resolve_ty(&p.ty))
                    .collect::<CompilerResult<Vec<Type>>>()?;

                let return_ty = match &function.return_ty {
                    Some(t) => self.resolve_ty(t)?,
                    None => Type::Void,
                };

                Type::Function {
                    params: Rc::from(params),
                    return_ty: Rc::from(return_ty),
                }
            }
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

    fn check_function(&mut self, function: &Function) -> CompilerResult<()> {
        self.context_function = Some(self.lookup_type(&function.name)?);
        self.begin_scope(); // TODO: Is it necessary?
        for Param { name, ty } in &function.params {
            let param_ty = self.lookup_type(&ty.name)?;
            self.declare_local(&name, param_ty, || {
                error!(
                    name.node.span,
                    "Parameter '{}' is already declared", name.symbol
                )
            })?
        }
        self.check_stmt(&function.body)?;
        self.end_scope();
        self.context_function = None;
        Ok(())
    }

    fn check_stmt(&mut self, stmt: &Stmt) -> CompilerResult<()> {
        match &stmt.kind {
            StmtKind::Block { statements } => {
                self.begin_scope();
                for statement in statements {
                    self.check_stmt(statement)?
                }
                self.end_scope();
            }

            StmtKind::ExprStmt(expr) => {
                self.check_expr(expr)?;
            }

            StmtKind::Declaration { name, ty, value } => {
                let var_ty = self.resolve_ty(&ty)?;
                self.node_types.insert(name.node.id, var_ty.clone());
                self.declare_local(&name, var_ty.clone(), || {
                    error!(
                        name.node.span,
                        "Variable '{}' is already declared in this scope", name.symbol
                    )
                })?;
                if let Some(value) = value {
                    let initializer_ty = self.check_expr(value)?;
                    if var_ty != initializer_ty {
                        return Err(error!(
                            value.node.span,
                            "Type Error: expected {var_ty:?} but found {initializer_ty:?}"
                        ));
                    }
                }
            }

            StmtKind::Assignment { target, value } => {
                let target_ty = self.check_expr(target)?;
                let value_ty = self.check_expr(value)?;
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
                let condition_ty = self.check_expr(condition)?;
                if condition_ty != Type::Bool {
                    return Err(error!(
                        condition.node.span,
                        "Type Error: condition should be 'bool', but got {condition_ty:?}"
                    ));
                }
                self.check_stmt(then_block)?;
                if let Some(e) = else_block {
                    self.check_stmt(e)?;
                }
            }

            StmtKind::While { condition, body } => {
                let condition_ty = self.check_expr(condition)?;
                if condition_ty != Type::Bool {
                    return Err(error!(
                        condition.node.span,
                        "Type Error: condition should be 'bool', but got {condition_ty:?}"
                    ));
                }
                self.check_stmt(body)?
            }

            StmtKind::Return { expr } => {
                let Some(Type::Function { return_ty, .. }) = self.context_function.clone() else {
                    return Err(error!(stmt.node.span, "Return outside of a function"));
                };
                let expr_ty = self.check_expr(expr)?;
                if expr_ty != *return_ty {
                    return Err(error!(
                        stmt.node.span,
                        "Type Error: return type mismatch, expected {return_ty:?}, but found {expr_ty:?}"
                    ));
                }
                self.check_expr(expr)?;
            }
        }
        Ok(())
    }

    fn check_expr(&mut self, expr: &Expr) -> CompilerResult<Type> {
        let ty = match &expr.kind {
            ExprKind::Literal(LiteralKind::Int(_)) => Type::Int,
            ExprKind::Literal(LiteralKind::Float(_)) => Type::Float,
            ExprKind::Literal(LiteralKind::String { .. }) => Type::Int, // TODO: Add String type
            ExprKind::Literal(LiteralKind::Bool(_)) => Type::Bool,
            ExprKind::Variable(ident) => self.lookup_local(ident)?,
            ExprKind::ArrayIndex { expr, index } => {
                let Type::Int = self.check_expr(index)? else {
                    return Err(error!(
                        index.node.span,
                        "Type Error: Array index must be Int"
                    ));
                };

                let expr_ty = self.check_expr(expr)?;

                let Type::Array { inner, .. } = expr_ty else {
                    return Err(error!(
                        expr.node.span,
                        "Type Error: Expecting an Array, found {expr_ty:?}"
                    ));
                };
                (*inner).clone()
            }
            ExprKind::FieldAccess { expr, field } => {
                let expr_ty = self.check_expr(expr)?;
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
                let left_ty = self.check_expr(left)?;
                let right_ty = self.check_expr(right)?;

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
                let right_ty = self.check_expr(right)?;
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

                    let Type::Function { params, return_ty } = self.lookup_type(ident)? else {
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
                        let arg_ty = self.check_expr(arg)?;
                        let param_ty = &params[i];
                        if arg_ty != *param_ty {
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

    fn resolve_ty(&mut self, ast_ty: &ast::Type) -> CompilerResult<Type> {
        // TODO: This is sort of a hack!
        if ast_ty.name.symbol.as_str() == "Array" {
            let mut params = ast_ty.params.iter();
            let Some(TypeParam::Type(inner)) = params.next() else {
                return Err(error!(
                    ast_ty.node.span,
                    "Array requires a valid inner type parameter",
                ));
            };
            let Some(TypeParam::Const(size)) = params.next() else {
                return Err(error!(
                    ast_ty.node.span,
                    "Array requires a valid size type parameter",
                ));
            };
            let inner = self.resolve_ty(&*inner)?;
            return Ok(Type::Array {
                inner: inner.into(),
                size: *size,
            });
        }

        let ty = self.lookup_type(&ast_ty.name)?;
        self.node_types.insert(ast_ty.node.id, ty.clone());
        Ok(ty)
    }
}
