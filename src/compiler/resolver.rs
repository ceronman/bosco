use std::cell::RefCell;
use std::collections::{HashMap, VecDeque};
use std::rc::Rc;

use crate::ast;
use crate::ast::{
    BinOpKind, Expr, ExprKind, Function, Identifier, Item, ItemKind, LiteralKind, Module, NodeId,
    Param, Stmt, StmtKind, Symbol, TypeParam, UnOpKind,
};
use crate::compiler::Counter;
use crate::error::{CompilerError, CompilerResult, error};
use crate::lexer::Span;

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Type {
    Void,
    Int,
    Float,
    Bool,
    Array { inner: Rc<Type>, size: u32 },
    Record { fields: Rc<[Field]> },
    Function(Signature),
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Signature {
    pub params: Rc<[Type]>,
    pub return_ty: Rc<Type>,
}

#[derive(Debug, Eq, PartialEq)]
pub struct Field {
    pub name: Symbol,
    pub ty: Rc<Type>,
}

#[derive(Debug)]
enum ResolutionState {
    Delayed(Item),
    InProgress,
    Resolved(Declaration)
}

pub type DeclarationId = u32;

#[derive(Debug, Clone)]
pub struct Declaration {
    pub id: DeclarationId,
    pub ty: Type,
    pub kind: DeclarationKind,
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum DeclarationKind {
    Local(DeclarationId),
    Function,
    Type,
}

type Scope = HashMap<Symbol, Rc<RefCell<ResolutionState>>>;

#[derive(Default)]
pub struct Resolver {
    ids: Counter,
    scopes: VecDeque<Scope>,
    pub node_types: HashMap<NodeId, Type>,
    pub declarations: Vec<Declaration>,
    pub uses: HashMap<NodeId, Declaration>,
}

impl Resolver {
    fn declare(&mut self, symbol: Symbol, state: ResolutionState, err: impl Fn() -> CompilerError) -> CompilerResult<()> {
        // TODO: Think about panics
        let scope = self
            .scopes
            .front_mut()
            .expect("There should be at least one scope available");

        if scope.contains_key(&symbol) {
            return Err(err());
        }

        if let ResolutionState::Resolved(decl) = &state {
            self.declarations.push(decl.clone());
        }
        scope.insert(symbol, Rc::new(RefCell::new(state)));

        Ok(())
    }

    fn lookup(&mut self, ident: &Identifier) -> CompilerResult<Declaration> {
        let state = self.scopes
            .iter()
            .find_map(|scope| scope.get(&ident.symbol))
            .cloned()
            .ok_or_else(|| error!(ident.node.span, "Undeclared variable '{}'", ident.symbol))?; // TODO: error message

        let item = match &*state.borrow() {
            ResolutionState::Delayed(item) => {
                item.clone()
            }
            ResolutionState::InProgress => {
                return Err(error!(
                    ident.node.span,
                    "Type '{}' contains cycles", ident.symbol
                ))
            }
            ResolutionState::Resolved(d) => return Ok(d.clone())
        };
        state.replace(ResolutionState::InProgress);
        let decl = self.resolve_item(&item)?;
        state.replace(ResolutionState::Resolved(decl.clone()));
        self.declarations.push(decl.clone());
        self.uses.insert(ident.node.id, decl.clone());
        Ok(decl)
    }

    fn declare_local(
        &mut self,
        ident: &Identifier,
        ty: Type,
        func_id: DeclarationId,
        err: impl Fn() -> CompilerError,
    ) -> CompilerResult<()> {
        let decl = Declaration {
            id: self.ids.next(),
            ty,
            kind: DeclarationKind::Local(func_id),
        };
        self.declare(ident.symbol.clone(), ResolutionState::Resolved(decl.clone()), err)?;
        self.uses.insert(ident.node.id, decl);
        Ok(())
    }

    fn declare_builtin(&mut self, name: &str, ty: Type) -> CompilerResult<()> {
        let decl = Declaration {
            id: self.ids.next(),
            ty,
            kind: DeclarationKind::Type,
        };
        self.declare(Symbol::from(name), ResolutionState::Resolved(decl), || {
            error!(Span(0, 0), "Builtin '{name}' is already declared")
        })
    }

    fn declare_builtins(&mut self) -> CompilerResult<()> {
        self.declare_builtin("void", Type::Void)?;
        self.declare_builtin("int", Type::Int)?;
        self.declare_builtin("float", Type::Float)?;
        self.declare_builtin("bool", Type::Bool)?;
        Ok(())
    }

    pub fn import_function(
        &mut self,
        name: &str,
        params: &[Type],
        return_ty: Type,
    ) -> CompilerResult<()> {
        let signature = Signature {
            params: params.into(),
            return_ty: return_ty.into(),
        };
        let ty = Type::Function(signature.clone());

        let decl = Declaration {
            id: self.ids.next(),
            ty,
            kind: DeclarationKind::Function,
        };

        self.declare(Symbol::from(name), ResolutionState::Resolved(decl), || {
            error!(Span(0, 0), "Imported function '{name}' is already declared")
        })?;

        Ok(())
    }

    fn collect_top_level_types(&mut self, module: &Module) -> CompilerResult<()> {
        for item in &module.items {
            // TODO: Maybe record and function can share some data here.
            match &item.kind {
                ItemKind::Function(f) => {
                    self.declare(
                        f.name.symbol.clone(),
                        ResolutionState::Delayed(item.clone()),
                        || error!(f.name.node.span, "Function '{}' was already declared", f.name.symbol))?
                }
                ItemKind::Record(r) => {
                    self.declare(
                        r.name.symbol.clone(),
                        ResolutionState::Delayed(item.clone()),
                        || error!(r.name.node.span, "Record '{}' was already declared", r.name.symbol))?
                }
            };

        }

        Ok(())
    }

    pub fn resolve(&mut self, module: &Module) -> CompilerResult<()> {
        self.begin_scope();
        self.import_function("print", &[Type::Int, Type::Int], Type::Void)?;
        self.import_function("print_int", &[Type::Int], Type::Void)?;
        self.import_function("print_float", &[Type::Float], Type::Void)?;
        self.declare_builtins()?;
        self.collect_top_level_types(module)?;

        for item in &module.items {
            if let ItemKind::Function(f) = &item.kind {
                let decl = self.lookup(&f.name)?;
                self.uses.insert(f.name.node.id, decl.clone());
                self.check_function(&decl, f)?;
            }
        }
        self.end_scope();
        debug_assert!(self.scopes.len() == 0);
        Ok(())
    }

    fn resolve_item(&mut self, item: &Item) -> CompilerResult<Declaration> {
        let decl = match &item.kind {
            ItemKind::Function(function) => {
                let params = function
                    .params
                    .iter()
                    .map(|p| self.resolve_ty(&p.ty))
                    .collect::<CompilerResult<Vec<Type>>>()?;

                let return_ty = match &function.return_ty {
                    Some(t) => self.resolve_ty(t)?,
                    None => Type::Void,
                };

                Declaration {
                    id: self.ids.next(),
                    ty: Type::Function(Signature {
                        params: Rc::from(params),
                        return_ty: Rc::from(return_ty),
                    }),
                    kind: DeclarationKind::Function,
                }
            }
            ItemKind::Record(record) => {
                let mut fields = Vec::with_capacity(record.fields.len());
                for f in &record.fields {
                    fields.push(Field {
                        name: f.name.symbol.clone(),
                        ty: self.resolve_ty(&f.ty)?.into(),
                    })
                }

                Declaration {
                    id: self.ids.next(),
                    ty: Type::Record {
                        fields: Rc::from(fields),
                    },
                    kind: DeclarationKind::Type,
                }
            }
        };
        Ok(decl)
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

        let decl = self.lookup(&ast_ty.name)?;
        self.node_types.insert(ast_ty.name.node.id, decl.ty.clone());
        Ok(decl.ty)
    }

    fn check_function(
        &mut self,
        func_decl: &Declaration,
        function: &Function,
    ) -> CompilerResult<()> {
        self.begin_scope();
        for Param { name, ty } in &function.params {
            let param_ty = self.lookup(&ty.name)?.ty;
            self.declare_local(&name, param_ty, func_decl.id, || {
                error!(
                    name.node.span,
                    "Parameter '{}' is already declared", name.symbol
                )
            })?
        }
        self.check_stmt(func_decl, &function.body)?;
        self.end_scope();
        debug_assert!(self.scopes.len() == 1);
        Ok(())
    }

    fn check_stmt(&mut self, func_decl: &Declaration, stmt: &Stmt) -> CompilerResult<()> {
        match &stmt.kind {
            StmtKind::Block { statements } => {
                self.begin_scope();
                for statement in statements {
                    self.check_stmt(func_decl, statement)?
                }
                self.end_scope();
            }

            StmtKind::ExprStmt(expr) => {
                self.check_expr(func_decl, expr)?;
            }

            StmtKind::Declaration { name, ty, value } => {
                let var_ty = self.resolve_ty(&ty)?;
                self.declare_local(&name, var_ty.clone(), func_decl.id, || {
                    error!(
                        name.node.span,
                        "Variable '{}' is already declared in this scope", name.symbol
                    )
                })?;
                if let Some(value) = value {
                    let initializer_ty = self.check_expr(func_decl, value)?;
                    if var_ty != initializer_ty {
                        return Err(error!(
                            value.node.span,
                            "Type Error: expected {var_ty:?} but found {initializer_ty:?}"
                        ));
                    }
                }
            }

            StmtKind::Assignment { target, value } => {
                let target_ty = self.check_expr(func_decl, target)?;
                let value_ty = self.check_expr(func_decl, value)?;
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
                let condition_ty = self.check_expr(func_decl, condition)?;
                if condition_ty != Type::Bool {
                    return Err(error!(
                        condition.node.span,
                        "Type Error: condition should be 'bool', but got {condition_ty:?}"
                    ));
                }
                self.check_stmt(func_decl, then_block)?;
                if let Some(e) = else_block {
                    self.check_stmt(func_decl, e)?;
                }
            }

            StmtKind::While { condition, body } => {
                let condition_ty = self.check_expr(func_decl, condition)?;
                if condition_ty != Type::Bool {
                    return Err(error!(
                        condition.node.span,
                        "Type Error: condition should be 'bool', but got {condition_ty:?}"
                    ));
                }
                self.check_stmt(func_decl, body)?
            }

            StmtKind::Return { expr } => {
                let Type::Function(signature) = &func_decl.ty else {
                    panic!("Should not happen")
                };
                let return_ty = signature.return_ty.clone();
                let expr_ty = self.check_expr(func_decl, expr)?;
                if expr_ty != *return_ty {
                    return Err(error!(
                        stmt.node.span,
                        "Type Error: return type mismatch, expected {return_ty:?}, but found {expr_ty:?}"
                    ));
                }
                self.check_expr(func_decl, expr)?;
            }
        }
        Ok(())
    }

    fn check_expr(&mut self, func_decl: &Declaration, expr: &Expr) -> CompilerResult<Type> {
        let ty = match &expr.kind {
            ExprKind::Literal(LiteralKind::Int(_)) => Type::Int,
            ExprKind::Literal(LiteralKind::Float(_)) => Type::Float,
            ExprKind::Literal(LiteralKind::String { .. }) => Type::Int, // TODO: Add String type
            ExprKind::Literal(LiteralKind::Bool(_)) => Type::Bool,
            ExprKind::Variable(ident) => {
                let decl = self.lookup(ident)?;
                self.uses.insert(ident.node.id, decl.clone());
                decl.ty
            }
            ExprKind::ArrayIndex { expr, index } => {
                let Type::Int = self.check_expr(func_decl, index)? else {
                    return Err(error!(
                        index.node.span,
                        "Type Error: Array index must be Int"
                    ));
                };

                let expr_ty = self.check_expr(func_decl, expr)?;

                let Type::Array { inner, .. } = expr_ty else {
                    return Err(error!(
                        expr.node.span,
                        "Type Error: Expecting an Array, found {expr_ty:?}"
                    ));
                };
                (*inner).clone()
            }
            ExprKind::FieldAccess { expr, field } => {
                let expr_ty = self.check_expr(func_decl, expr)?;
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
                let left_ty = self.check_expr(func_decl, left)?;
                let right_ty = self.check_expr(func_decl, right)?;

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
                let right_ty = self.check_expr(func_decl, right)?;
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
                    let decl = self.lookup(ident)?;
                    self.uses.insert(ident.node.id, decl.clone()); // FIXME! This should not be here.

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

                    let Type::Function(signature) = decl.ty else {
                        return Err(error!(
                            ident.node.span,
                            "'{}' is not a function", ident.symbol
                        )); // TODO: Test
                    };

                    if args.len() != signature.params.len() {
                        return Err(error!(
                            expr.node.span,
                            "Function called with incorrect number of arguments",
                        ));
                    }
                    for (i, arg) in args.iter().enumerate() {
                        let arg_ty = self.check_expr(func_decl, arg)?;
                        let param_ty = &signature.params[i];
                        if arg_ty != *param_ty {
                            return Err(error!(
                                arg.node.span,
                                "Type Error: argument type mismatch",
                            ));
                        }
                    }
                    (*signature.return_ty).clone()
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

    fn begin_scope(&mut self) {
        self.scopes.push_front(Default::default())
    }

    fn end_scope(&mut self) {
        self.scopes.pop_front();
    }
}
