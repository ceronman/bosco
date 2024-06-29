use std::collections::{HashMap, VecDeque};

use anyhow::Result;

use crate::ast::{Expr, ExprKind, Function, Item, ItemKind, Module, Param, Stmt, StmtKind};
use crate::compiler::{compile_error, Counter, Ty};
use crate::lexer::Token;

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

pub(super) struct SymbolTable<'src> {
    source: &'src str,
    environments: VecDeque<HashMap<String, LocalVar>>, // TODO: Use interned strings instead
    local_counter: Counter,
    locals: HashMap<Token, LocalVar>, // TODO: Maybe move ty in local var to the type checker?
    functions: HashMap<String, FnSignature>, // TODO: Figure out a better thing than String here.
    function_counter: Counter,
    function_locals: Vec<LocalVar>,
}

impl<'src> SymbolTable<'src> {
    pub(super) fn new(source: &'src str) -> Self {
        SymbolTable {
            source,
            environments: Default::default(),
            local_counter: Counter(0),
            locals: Default::default(),
            functions: Default::default(),
            function_counter: Counter(0),
            function_locals: vec![],
        }
    }

    fn declare(&mut self, name_token: &Token, ty_token: &Token) -> Result<()> {
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
        let local_var = LocalVar {
            index: self.local_counter.next(),
            ty: Ty::from_lexeme(ty_token, self.source)?,
        };
        env.insert(name.into(), local_var);
        self.locals.insert(*name_token, local_var);
        self.function_locals.push(local_var);
        Ok(())
    }

    fn resolve_var(&mut self, token: &Token) -> Result<()> {
        let name = token.span.as_str(self.source);
        for env in &self.environments {
            if let Some(&local_var) = env.get(name) {
                self.locals.insert(*token, local_var);
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

    pub(super) fn lookup_function(&self, name: &str) -> Option<FnSignature> {
        self.functions.get(name).map(|s| (*s).clone()) // TODO: Clone?
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

    pub(super) fn import_function(
        &mut self,
        name: impl Into<String>,
        params: Vec<Ty>,
        return_ty: Ty,
    ) {
        // TODO: Check duplicate functions!
        self.functions.insert(
            name.into(),
            FnSignature {
                params,
                return_ty,
                index: self.function_counter.next(),
                local_vars: vec![],
            },
        );
    }

    fn resolve_function(&mut self, function: &Function) -> Result<()> {
        //TODO: Ugly
        self.function_locals.clear();
        self.local_counter.reset();

        self.begin_scope(); // TODO: Double because of blocks
        for Param { name, ty, .. } in &function.params {
            self.declare(name, ty)?;
        }
        self.resolve_stmt(&function.body)?;
        self.end_scope();

        let name = function.name.span.as_str(self.source);
        // FIXME: Unwraps!
        let signature = FnSignature {
            params: function
                .params
                .iter()
                .map(|p| Ty::from_lexeme(&p.ty, self.source).unwrap())
                .collect(),
            return_ty: function
                .return_ty
                .map(|r| Ty::from_lexeme(&r, self.source).unwrap())
                .unwrap_or(Ty::Void),
            index: self.function_counter.next(),
            local_vars: self.function_locals.iter().map(|l| l.ty).collect(),
        };
        // TODO: Check duplicate functions!
        self.functions.insert(name.into(), signature);

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

            StmtKind::Return { expr } => {
                self.resolve_expression(expr)?;
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
