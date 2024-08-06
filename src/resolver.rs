use std::cell::RefCell;
use std::collections::{HashMap, VecDeque};
use std::rc::Rc;

use crate::ast;
use crate::ast::{
    BinOpKind, Expr, ExprKind, Function, Identifier, Item, ItemKind, LiteralKind, Module, NodeId,
    Param, Stmt, StmtKind, Symbol, TypeParam, UnOpKind,
};
use crate::error::{error, CompilerResult};
use crate::types::{Field, Signature, Type};

#[derive(Debug)]
enum ResolutionState {
    Delayed(Item),
    InProgress,
    Resolved(DeclarationId),
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
pub struct Resolution {
    pub node_types: HashMap<NodeId, Type>,
    pub declarations: Vec<Declaration>,
    pub uses: HashMap<NodeId, DeclarationId>,
}

#[derive(Default)]
struct Resolver {
    scopes: VecDeque<Scope>,
    res: Resolution,
}

impl Resolver {
    fn new_decl(&mut self, ty: Type, kind: DeclarationKind) -> DeclarationId {
        let id = self.res.declarations.len() as u32;
        let decl = Declaration { id, ty, kind };
        self.res.declarations.push(decl);
        id
    }

    fn declare(&mut self, ident: &Identifier, state: ResolutionState) -> CompilerResult<()> {
        let Some(scope) = self.scopes.front_mut() else {
            // TODO: Make fatal or internal error
            return Err(error!(
                ident.node.span,
                "Fatal: name declaration out of scope"
            ));
        };
        let name = ident.symbol.clone();

        if scope.contains_key(&name) {
            // TODO: Add information about previous declaration in the error
            return Err(error!(
                ident.node.span,
                "Name '{name}' is already declared in this scope"
            ));
        }

        scope.insert(name, Rc::new(RefCell::new(state)));

        Ok(())
    }

    fn lookup(&mut self, ident: &Identifier) -> CompilerResult<DeclarationId> {
        let state = self
            .scopes
            .iter()
            .find_map(|scope| scope.get(&ident.symbol))
            .cloned()
            .ok_or_else(|| error!(ident.node.span, "Undeclared '{}'", ident.symbol))?;

        let item = match &*state.borrow() {
            ResolutionState::Delayed(item) => item.clone(),
            ResolutionState::InProgress => {
                return Err(error!(
                    ident.node.span,
                    "Type '{}' contains cycles", ident.symbol
                ))
            }
            ResolutionState::Resolved(d) => return Ok(*d),
        };
        state.replace(ResolutionState::InProgress);
        let decl = self.resolve_item(&item)?;
        state.replace(ResolutionState::Resolved(decl));
        Ok(decl)
    }

    fn declare_local(
        &mut self,
        ident: &Identifier,
        ty: Type,
        func_id: DeclarationId,
    ) -> CompilerResult<()> {
        let decl = self.new_decl(ty, DeclarationKind::Local(func_id));
        self.declare(ident, ResolutionState::Resolved(decl))?;
        self.res.uses.insert(ident.node.id, decl);
        Ok(())
    }

    fn declare_builtin(&mut self, name: &str, ty: Type) -> CompilerResult<()> {
        let decl = self.new_decl(ty, DeclarationKind::Type);
        self.declare(&Identifier::fake(name), ResolutionState::Resolved(decl))
    }

    fn declare_builtins(&mut self) -> CompilerResult<()> {
        self.declare_builtin("void", Type::Void)?;
        self.declare_builtin("int", Type::Int)?;
        self.declare_builtin("float", Type::Float)?;
        self.declare_builtin("bool", Type::Bool)?;
        Ok(())
    }

    fn import_function(
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

        let decl = self.new_decl(ty, DeclarationKind::Function);
        self.declare(&Identifier::fake(name), ResolutionState::Resolved(decl))?;

        Ok(())
    }

    fn collect_top_level_types(&mut self, module: &Module) -> CompilerResult<()> {
        for item in &module.items {
            // TODO: Maybe record and function can share some data here.
            let name = match &item.kind {
                ItemKind::Function(f) => &f.name,
                ItemKind::Record(r) => &r.name,
            };

            self.declare(name, ResolutionState::Delayed(item.clone()))?;
        }

        Ok(())
    }

    fn resolve(&mut self, module: &Module) -> CompilerResult<()> {
        self.begin_scope();
        self.import_function("print", &[Type::Int, Type::Int], Type::Void)?;
        self.import_function("print_int", &[Type::Int], Type::Void)?;
        self.import_function("print_float", &[Type::Float], Type::Void)?;
        self.declare_builtins()?;
        self.collect_top_level_types(module)?;

        for item in &module.items {
            match &item.kind {
                ItemKind::Function(f) => {
                    let decl = self.lookup(&f.name)?;
                    self.res.uses.insert(f.name.node.id, decl);
                    self.check_function(decl, f)?;
                }

                ItemKind::Record(r) => {
                    let decl = self.lookup(&r.name)?;
                    self.res.uses.insert(r.name.node.id, decl);
                }
            }
        }
        self.end_scope();
        debug_assert!(self.scopes.is_empty());
        Ok(())
    }

    fn resolve_item(&mut self, item: &Item) -> CompilerResult<DeclarationId> {
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

                self.new_decl(
                    Type::Function(Signature {
                        params: Rc::from(params),
                        return_ty: Rc::from(return_ty),
                    }),
                    DeclarationKind::Function,
                )
            }
            ItemKind::Record(record) => {
                let mut fields = Vec::with_capacity(record.fields.len());
                for f in &record.fields {
                    fields.push(Field {
                        name: f.name.symbol.clone(),
                        ty: self.resolve_ty(&f.ty)?.into(),
                    })
                }

                self.new_decl(
                    Type::Record {
                        fields: Rc::from(fields),
                    },
                    DeclarationKind::Type,
                )
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
            let inner = self.resolve_ty(inner)?;
            return Ok(Type::Array {
                inner: inner.into(),
                size: *size,
            });
        }

        let decl_id = self.lookup(&ast_ty.name)?;
        let decl = &self.res.declarations[decl_id as usize];
        self.res
            .node_types
            .insert(ast_ty.name.node.id, decl.ty.clone());
        Ok(decl.ty.clone())
    }

    fn check_function(
        &mut self,
        func_id: DeclarationId,
        function: &Function,
    ) -> CompilerResult<()> {
        self.begin_scope();
        for Param { name, ty } in &function.params {
            let param_ty = self.resolve_ty(ty)?;
            self.declare_local(name, param_ty, func_id)?
        }
        self.check_stmt(func_id, &function.body)?;
        self.end_scope();
        debug_assert!(self.scopes.len() == 1);
        Ok(())
    }

    fn check_stmt(&mut self, func_id: DeclarationId, stmt: &Stmt) -> CompilerResult<()> {
        match &stmt.kind {
            StmtKind::Block { statements } => {
                self.begin_scope();
                for statement in statements {
                    self.check_stmt(func_id, statement)?
                }
                self.end_scope();
            }

            StmtKind::ExprStmt(expr) => {
                self.check_expr(expr)?;
            }

            StmtKind::Declaration { name, ty, value } => {
                let var_ty = self.resolve_ty(ty)?;
                self.declare_local(name, var_ty.clone(), func_id)?;
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
                self.check_stmt(func_id, then_block)?;
                if let Some(e) = else_block {
                    self.check_stmt(func_id, e)?;
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
                self.check_stmt(func_id, body)?
            }

            StmtKind::Return { expr } => {
                let func_decl = &self.res.declarations[func_id as usize];
                let Type::Function(signature) = &func_decl.ty else {
                    panic!("Should not happen")
                };
                let return_ty = signature.return_ty.clone();
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
            ExprKind::Variable(ident) => {
                let decl_id = self.lookup(ident)?;
                let decl = &self.res.declarations[decl_id as usize];
                self.res.uses.insert(ident.node.id, decl_id);
                decl.ty.clone()
            }
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
                    let decl_id = self.lookup(ident)?;
                    self.res.uses.insert(ident.node.id, decl_id);

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

                    let decl = &self.res.declarations[decl_id as usize];
                    let Type::Function(signature) = decl.ty.clone() else {
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
                        let arg_ty = self.check_expr(arg)?;
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
        self.res.node_types.insert(expr.node.id, ty.clone());
        Ok(ty)
    }

    fn begin_scope(&mut self) {
        self.scopes.push_front(Default::default())
    }

    fn end_scope(&mut self) {
        self.scopes.pop_front();
    }
}

pub fn resolve(module: &Module) -> CompilerResult<Resolution> {
    let mut r = Resolver::default();
    r.resolve(module)?;
    Ok(r.res)
}
