use std::collections::{HashMap, VecDeque};

use crate::ast::{Expr, ExprKind, Item, ItemKind, Module, Stmt, StmtKind};
use crate::compiler::{compile_error, LocalVar, Ty};
use crate::lexer::Token;
use anyhow::Result;

pub(super) struct SymbolTable<'src> {
    source: &'src str,
    environments: VecDeque<HashMap<String, LocalVar>>, // TODO: Use interned strings instead
    locals: HashMap<Token, LocalVar>,
}

impl<'src> SymbolTable<'src> {
    pub(super) fn new(source: &'src str) -> Self {
        SymbolTable {
            source,
            environments: Default::default(),
            locals: Default::default(),
        }
    }

    fn declare(&mut self, name_token: &Token, ty_token: &Token) -> Result<u32> {
        let index: u32 = self.locals.len().try_into()?;
        let name = name_token.span.as_str(self.source);
        let Some(env) = self.environments.front_mut() else {
            return compile_error(
                format!("Variable '{name}' was declared outside of any scope"),
                name_token.span,
            );
        };

        if env.contains_key(name) {
            return compile_error(
                format!("Variable '{name}' was already declared in this scope"),
                name_token.span,
            );
        }
        let ty_name = ty_token.span.as_str(self.source);
        let Some(ty) = Ty::from_lexeme(ty_name) else {
            return compile_error(format!("Unknown type {ty_name}"), ty_token.span);
        };
        let local_var = LocalVar { index, ty };
        env.insert(name.into(), local_var);
        self.locals.insert(*name_token, local_var);
        Ok(index)
    }

    fn resolve_var(&mut self, token: &Token) -> Result<()> {
        let name = token.span.as_str(self.source);
        for env in &self.environments {
            if let Some(&index) = env.get(name) {
                self.locals.insert(*token, index);
                return Ok(());
            }
        }
        compile_error(format!("Undeclared variable '{name}'"), token.span)
    }

    pub(super) fn lookup_var(&self, token: &Token) -> Result<LocalVar> {
        let name = token.span.as_str(self.source);
        let Some(&local) = self.locals.get(token) else {
            return compile_error(format!("Undeclared variable '{name}'"), token.span);
        };
        Ok(local)
    }

    fn begin_scope(&mut self) {
        self.environments.push_front(Default::default())
    }

    fn end_scope(&mut self) {
        self.environments.pop_front();
    }

    pub(super) fn locals(&self) -> impl Iterator<Item = LocalVar> + '_ {
        self.locals.values().copied()
    }

    pub(super) fn resolve(&mut self, module: &Module) -> Result<()> {
        for item in &module.items {
            self.resolve_item(item)?;
        }
        Ok(())
    }

    fn resolve_item(&mut self, item: &Item) -> Result<()> {
        match &item.kind {
            // TODO: Resolve parameters
            ItemKind::Function { body, .. } => {
                self.resolve_stmt(body)?;
            }
        }
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
            StmtKind::Call { callee: _, args } => {
                for arg in args {
                    self.resolve_expression(arg)?;
                }
            }
            StmtKind::Declaration { name, ty, value } => {
                self.declare(name, ty)?;
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
        }
        Ok(())
    }

    fn resolve_expression(&mut self, expr: &Expr) -> Result<()> {
        match &expr.kind {
            ExprKind::Literal(_) => {}
            ExprKind::Variable { name } => self.resolve_var(name)?,
            ExprKind::Binary { left, right, .. }
            | ExprKind::Or { left, right, .. }
            | ExprKind::And { left, right, .. } => {
                self.resolve_expression(left)?;
                self.resolve_expression(right)?;
            }
            ExprKind::Not { right } => self.resolve_expression(right)?,
        }
        Ok(())
    }
}
