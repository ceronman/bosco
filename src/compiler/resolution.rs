use anyhow::Result;
use std::collections::{HashMap, VecDeque};
use std::rc::Rc;

use crate::ast::{
    Expr, ExprKind, Function, Identifier, Item, ItemKind, Module, NodeId, Param, Stmt, StmtKind,
    Symbol,
};
use crate::compiler::{compile_error, Counter, Ty};

#[derive(Copy, Clone, Debug)] // TODO: Should this be copy?
pub struct LocalVar {
    pub index: u32,
    pub ty: Ty,
}

// TODO: Maybe store Function node instead using Rc<Function> ?
#[derive(Debug, Clone)]
pub struct FnSignature {
    pub params: Vec<Ty>,
    pub return_ty: Ty,
    pub index: u32,
    pub local_vars: Vec<Ty>, // TODO: Duplicate in SymbolTable
}

#[derive(Default)]
pub(super) struct SymbolTable {
    environments: VecDeque<HashMap<Symbol, LocalVar>>, // TODO: Use interned strings instead
    local_counter: Counter,
    locals: HashMap<NodeId, LocalVar>, // TODO: Maybe move ty in local var to the type checker?
    functions: HashMap<Symbol, Rc<FnSignature>>, // TODO: Figure out a better thing than String here.
    function_counter: Counter,
    function_locals: Vec<LocalVar>,
}

impl SymbolTable {
    fn declare(&mut self, ident: &Identifier, ty: Ty) -> Result<()> {
        let Some(env) = self.environments.front_mut() else {
            return compile_error(
                format!(
                    "Variable '{}' was declared outside of any scope",
                    ident.symbol
                ),
                ident.node.span,
            );
        };

        if env.contains_key(&ident.symbol) {
            return compile_error(
                format!(
                    "Variable '{}' was already declared in this scope",
                    ident.symbol
                ),
                ident.node.span,
            );
        }
        let local_var = LocalVar {
            index: self.local_counter.next(),
            ty,
        };
        env.insert(ident.symbol.clone(), local_var);
        self.locals.insert(ident.node.id, local_var);
        self.function_locals.push(local_var);
        Ok(())
    }

    fn resolve_var(&mut self, ident: &Identifier) -> Result<()> {
        for env in &self.environments {
            if let Some(&local_var) = env.get(&ident.symbol) {
                self.locals.insert(ident.node.id, local_var);
                return Ok(());
            }
        }
        compile_error(
            format!("Undeclared variable '{}'", ident.symbol),
            ident.node.span,
        )
    }

    pub(super) fn lookup_var(&self, ident: &Identifier) -> Result<LocalVar> {
        let Some(&local) = self.locals.get(&ident.node.id) else {
            return compile_error(
                format!("Undeclared variable '{}'", ident.symbol),
                ident.node.span,
            );
        };
        Ok(local)
    }

    pub(super) fn lookup_function(&self, name: &Identifier) -> Option<Rc<FnSignature>> {
        self.functions.get(&name.symbol).cloned()
    }

    fn begin_scope(&mut self) {
        self.environments.push_front(Default::default())
    }

    fn end_scope(&mut self) {
        self.environments.pop_front();
    }

    pub(super) fn resolve(&mut self, module: &Module) -> Result<()> {
        for item in &module.items {
            self.resolve_item(item)?;
        }
        Ok(())
    }

    pub(super) fn resolve_item(&mut self, item: &Item) -> Result<()> {
        match &item.kind {
            ItemKind::Function(function) => {
                self.resolve_function(function)?;
            }
        }
        Ok(())
    }

    pub(super) fn import_function(&mut self, name: Symbol, params: &[Ty], return_ty: Ty) {
        // TODO: Check duplicate functions!
        self.functions.insert(
            name,
            Rc::new(FnSignature {
                params: params.into(),
                return_ty,
                index: self.function_counter.next(),
                local_vars: vec![],
            }),
        );
    }

    fn resolve_function(&mut self, function: &Function) -> Result<()> {
        //TODO: Ugly
        self.function_locals.clear();
        self.local_counter.reset();

        self.begin_scope(); // TODO: Double because of blocks
        for Param { name, ty, .. } in &function.params {
            self.declare(name, Ty::from_ast(ty)?)?;
        }
        self.resolve_stmt(&function.body)?;
        self.end_scope();

        let name = function.name.symbol.clone();
        // FIXME: Unwraps!
        let signature = FnSignature {
            params: function
                .params
                .iter()
                .map(|p| Ty::from_ast(&p.ty).unwrap())
                .collect(),
            return_ty: function
                .return_ty
                .as_ref()
                .map(|r| Ty::from_ast(r).unwrap())
                .unwrap_or(Ty::Void),
            index: self.function_counter.next(),
            local_vars: self.function_locals.iter().map(|l| l.ty).collect(),
        };
        // TODO: Check duplicate functions!
        self.functions.insert(name, Rc::new(signature));

        Ok(())
    }

    fn resolve_stmt(&mut self, statement: &Stmt) -> Result<()> {
        match &statement.kind {
            StmtKind::Block { statements } => {
                self.begin_scope();
                for statement in statements {
                    self.resolve_stmt(statement)?
                }
                self.end_scope();
            }

            StmtKind::ExprStmt(expr) => {
                self.resolve_expression(expr)?;
            }

            StmtKind::Declaration { name, ty, value } => {
                self.declare(name, Ty::from_ast(ty)?)?;
                if let Some(value) = value {
                    self.resolve_expression(value)?;
                }
            }

            StmtKind::Assignment { name, value } => {
                self.resolve_var(name)?;
                self.resolve_expression(value)?;
            }

            StmtKind::If {
                condition,
                then_block,
                else_block,
            } => {
                self.resolve_expression(condition)?;
                self.resolve_stmt(then_block)?;
                else_block.as_ref().map(|b| self.resolve_stmt(b));
            }

            StmtKind::While { condition, body } => {
                self.resolve_expression(condition)?;
                self.resolve_stmt(body)?
            }

            StmtKind::Return { expr } => {
                self.resolve_expression(expr)?;
            }
        }
        Ok(())
    }

    fn resolve_expression(&mut self, expr: &Expr) -> Result<()> {
        match &expr.kind {
            ExprKind::Literal(_) => {}
            ExprKind::Variable(ident) => self.resolve_var(ident)?,
            ExprKind::Binary { left, right, .. } => {
                self.resolve_expression(left)?;
                self.resolve_expression(right)?;
            }
            ExprKind::Unary { right, .. } => self.resolve_expression(right)?,

            ExprKind::Call {
                callee: _callee,
                args,
            } => {
                for arg in args {
                    self.resolve_expression(arg)?;
                }
            }
        }
        Ok(())
    }
}
