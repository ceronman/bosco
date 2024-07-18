use std::collections::hash_map::Entry;
use std::collections::{HashMap, VecDeque};
use std::rc::Rc;

use crate::ast::{
    Expr, ExprKind, Function, Identifier, Item, ItemKind, Module, NodeId, Param, Stmt, StmtKind,
    Symbol,
};
use crate::compiler::{Counter, Ty};
use crate::error::{error, CompilerError, CompilerResult};
use crate::lexer::Span;

#[derive(Debug)]
pub struct Local {
    pub address: Address,
    pub ty: Ty,
}

#[derive(Debug)]
pub enum Address {
    None,
    Var(u32),
    Mem(u32),
}

type LocalVarRef = Rc<Local>;

#[derive(Debug)]
pub struct FnSignature {
    pub params: Vec<Ty>,
    pub return_ty: Ty,
    pub index: u32,
    pub locals: Vec<Ty>,
}

#[derive(Default)]
pub(super) struct SymbolTable {
    environments: VecDeque<HashMap<Symbol, LocalVarRef>>,
    locals: HashMap<NodeId, LocalVarRef>,
    functions: HashMap<Symbol, Rc<FnSignature>>,
    function_counter: Counter,
    function_locals: Vec<Ty>,
    free_address: u32,
}

impl SymbolTable {
    fn declare(&mut self, ident: &Identifier, ty: Ty) -> CompilerResult<()> {
        let Some(env) = self.environments.front_mut() else {
            return Err(error!(
                ident.node.span,
                "Variable '{}' was declared outside of any scope", ident.symbol
            ));
        };

        if env.contains_key(&ident.symbol) {
            return Err(error!(
                ident.node.span,
                "Variable '{}' was already declared in this scope", ident.symbol
            ));
        }

        let address = match &ty {
            Ty::Array(_, _) => {
                let pointer = self.free_address;
                self.free_address += ty.size();
                Address::Mem(pointer)
            }
            Ty::Void => Address::None,
            _ => {
                let index = self.function_locals.len() as u32;
                self.function_locals.push(ty.clone());
                Address::Var(index)
            }
        };

        let local_var = Rc::from(Local { address, ty });
        env.insert(ident.symbol.clone(), Rc::clone(&local_var));
        self.locals.insert(ident.node.id, Rc::clone(&local_var));

        Ok(())
    }

    fn resolve_var(&mut self, ident: &Identifier) -> CompilerResult<()> {
        for env in &self.environments {
            if let Some(local_var) = env.get(&ident.symbol) {
                self.locals.insert(ident.node.id, Rc::clone(local_var));
                return Ok(());
            }
        }
        Err(error!(
            ident.node.span,
            "Undeclared variable '{}'", ident.symbol
        ))
    }

    pub(super) fn lookup_var(&self, ident: &Identifier) -> CompilerResult<LocalVarRef> {
        let Some(local) = self.locals.get(&ident.node.id) else {
            return Err(error!(
                ident.node.span,
                "Undeclared variable '{}'", ident.symbol
            ));
        };
        Ok(Rc::clone(local))
    }

    pub(super) fn lookup_function(&self, name: &Identifier) -> CompilerResult<Rc<FnSignature>> {
        match self.functions.get(&name.symbol) {
            Some(f) => Ok(Rc::clone(f)),
            None => Err(error!(name.node.span, "Unknown function '{}'", name.symbol)),
        }
    }

    fn begin_scope(&mut self) {
        self.environments.push_front(Default::default())
    }

    fn end_scope(&mut self) {
        self.environments.pop_front();
    }

    pub(super) fn resolve(&mut self, module: &Module) -> CompilerResult<()> {
        for item in &module.items {
            self.resolve_item(item)?;
        }
        Ok(())
    }

    pub(super) fn resolve_item(&mut self, item: &Item) -> CompilerResult<()> {
        match &item.kind {
            ItemKind::Function(function) => {
                self.resolve_function(function)?;
            }

            ItemKind::Record(_) => todo!(),
        }
        Ok(())
    }

    pub(super) fn import_function(
        &mut self,
        name: Symbol,
        params: &[Ty],
        return_ty: Ty,
    ) -> CompilerResult<()> {
        let signature = Rc::new(FnSignature {
            params: params.into(),
            return_ty,
            index: self.function_counter.next(),
            locals: vec![],
        });

        match self.functions.entry(name) {
            Entry::Occupied(e) => {
                return Err(error!(
                    Span(0, 0), // TODO: Imported functions should be defined in source code eventually
                    "Imported function '{}' has already been declared",
                    e.key(),
                ));
            }
            Entry::Vacant(v) => v.insert(signature),
        };

        Ok(())
    }

    fn resolve_function(&mut self, function: &Function) -> CompilerResult<()> {
        //TODO: Ugly
        self.function_locals.clear();

        self.begin_scope();
        for Param { name, ty, .. } in &function.params {
            self.declare(name, Ty::from_ast(ty)?)?;
        }
        self.resolve_stmt(&function.body)?;
        self.end_scope();

        let name = function.name.symbol.clone();

        let mut params = Vec::new();
        for p in &function.params {
            params.push(Ty::from_ast(&p.ty)?);
        }

        let return_ty = match &function.return_ty {
            Some(t) => Ty::from_ast(t)?,
            None => Ty::Void,
        };

        let signature = FnSignature {
            params,
            return_ty,
            index: self.function_counter.next(),
            locals: self.function_locals.clone(),
        };

        match self.functions.entry(name) {
            Entry::Occupied(e) => {
                return Err(error!(
                    function.name.node.span,
                    "Function '{}' was already defined",
                    e.key()
                ))
            }
            Entry::Vacant(v) => v.insert(Rc::new(signature)),
        };

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
                self.resolve_expression(expr)?;
            }

            StmtKind::Declaration { name, ty, value } => {
                self.declare(name, Ty::from_ast(ty)?)?;
                if let Some(value) = value {
                    self.resolve_expression(value)?;
                }
            }

            StmtKind::Assignment { target, value } => {
                self.resolve_expression(target)?;
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

    fn resolve_expression(&mut self, expr: &Expr) -> CompilerResult<()> {
        match &expr.kind {
            ExprKind::Literal(_) => {}
            ExprKind::Variable(ident) => self.resolve_var(ident)?,
            ExprKind::ArrayIndex { expr, index } => {
                self.resolve_expression(expr)?;
                self.resolve_expression(index)?;
            }
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
