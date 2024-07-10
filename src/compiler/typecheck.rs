use anyhow::Result;

use crate::ast::{
    AssignTargetKind, BinOpKind, Expr, ExprKind, Function, Item, ItemKind, LiteralKind, Module,
    Stmt, StmtKind, UnOpKind,
};
use crate::compiler::{compile_error, Compiler, Ty};

// TODO: Make into an independent compilation unit like Symbol Table?
impl Compiler {
    pub(super) fn type_check(&mut self, module: &Module) -> Result<()> {
        for item in &module.items {
            self.type_check_item(item)?;
        }
        Ok(())
    }

    fn type_check_item(&mut self, item: &Item) -> Result<()> {
        match &item.kind {
            ItemKind::Function(f) => self.type_check_function(f)?,
        }
        Ok(())
    }

    fn type_check_function(&mut self, function: &Function) -> Result<()> {
        self.current_function = Some(self.symbol_table.lookup_function(&function.name)?);
        self.type_check_stmt(&function.body)?;
        Ok(())
    }

    fn type_check_stmt(&mut self, stmt: &Stmt) -> Result<()> {
        match &stmt.kind {
            StmtKind::Block { statements } => {
                for stmt in statements {
                    self.type_check_stmt(stmt)?
                }
            }
            StmtKind::ExprStmt(expr) => {
                self.type_check_expr(expr)?;
            }
            StmtKind::Declaration { name, value, .. } => {
                let var_ty = &self.symbol_table.lookup_var(name)?.ty;
                if let Some(value) = value {
                    let initializer_ty = self.type_check_expr(value)?;
                    if initializer_ty != *var_ty {
                        return compile_error(
                            format!("Type Error: expected {var_ty:?} but found {initializer_ty:?}"),
                            value.node.span,
                        );
                    }
                }
            }
            StmtKind::Assignment { target, value } => {
                let var_ty = match &target.kind {
                    AssignTargetKind::Variable(name) => {
                        self.symbol_table.lookup_var(name)?.ty.clone()
                    }
                    AssignTargetKind::Array { name, .. } => {
                        let array_ty = &self.symbol_table.lookup_var(name)?.ty;
                        let Ty::Array(inner, _) = array_ty else {
                            return compile_error(format!("The type '{array_ty:?}' cannot be indexed because it's not an array"), name.node.span);
                        };
                        (**inner).clone()
                    }
                };
                let initializer_ty = self.type_check_expr(value)?;
                if initializer_ty != var_ty {
                    return compile_error(
                        format!("Type Error: expected {var_ty:?} but found {initializer_ty:?}"),
                        value.node.span,
                    );
                }
            }
            StmtKind::If {
                condition,
                then_block,
                else_block,
            } => {
                let condition_ty = self.type_check_expr(condition)?;
                if condition_ty != Ty::Bool {
                    return compile_error(
                        format!("Type Error: condition should be 'bool', but got {condition_ty:?}"),
                        condition.node.span,
                    );
                }
                self.type_check_stmt(then_block)?;
                if let Some(e) = else_block {
                    self.type_check_stmt(e)?;
                }
            }
            StmtKind::While { condition, body } => {
                let condition_ty = self.type_check_expr(condition)?;
                if condition_ty != Ty::Bool {
                    return compile_error(
                        format!("Type Error: condition should be 'bool', but got {condition_ty:?}"),
                        condition.node.span,
                    );
                }
                self.type_check_stmt(body)?;
            }

            StmtKind::Return { expr } => {
                let Some(signature) = self.current_function.clone() else {
                    return compile_error("Return outside of a function", stmt.node.span);
                };
                let expr_ty = self.type_check_expr(expr)?;
                if expr_ty != signature.return_ty {
                    return compile_error(
                        format!("Type Error: return type mismatch, expected {:?}, but found {expr_ty:?}", signature.return_ty),
                        stmt.node.span
                    );
                }
            }
        }
        Ok(())
    }

    fn type_check_expr(&mut self, expr: &Expr) -> Result<Ty> {
        let ty = match &expr.kind {
            ExprKind::Literal(LiteralKind::Int(_)) => Ty::Int,
            ExprKind::Literal(LiteralKind::Float(_)) => Ty::Float,
            ExprKind::Literal(LiteralKind::String { .. }) => Ty::Int, // TODO: Add String type
            ExprKind::Literal(LiteralKind::Bool(_)) => Ty::Bool,
            ExprKind::Variable(ident) => {
                let local_var = self.symbol_table.lookup_var(ident)?;
                local_var.ty.clone()
            }
            ExprKind::ArrayIndex { expr, .. } => {
                let expr_ty = self.type_check_expr(expr)?;
                let Ty::Array(inner, _) = expr_ty else {
                    return compile_error(
                        format!("Expecting an Array, found {expr_ty:?}"),
                        expr.node.span,
                    );
                };
                (*inner).clone()
            }
            ExprKind::Binary {
                left,
                right,
                operator,
            } => {
                let left_ty = self.type_check_expr(left)?;
                let right_ty = self.type_check_expr(right)?;

                if left_ty != right_ty {
                    return compile_error(
                        format!("Type Error: operator {:?} has incompatible types {left_ty:?} and {right_ty:?}", operator.kind),
                        expr.node.span,
                    );
                }

                match operator.kind {
                    BinOpKind::Le
                    | BinOpKind::Lt
                    | BinOpKind::Eq
                    | BinOpKind::Ne
                    | BinOpKind::Ge
                    | BinOpKind::Gt => Ty::Bool,
                    BinOpKind::And | BinOpKind::Or => {
                        if left_ty != Ty::Bool {
                            return compile_error(
                                "Type Error: operand should be 'bool'",
                                left.node.span,
                            );
                        }
                        if right_ty != Ty::Bool {
                            return compile_error(
                                "Type Error: operand should be 'bool'",
                                right.node.span,
                            );
                        }
                        Ty::Bool
                    }
                    BinOpKind::Mod if left_ty == Ty::Float => {
                        return compile_error(
                            "Type Error: '%' operator doesn't work on floats",
                            expr.node.span,
                        );
                    }
                    _ => left_ty,
                }
            }
            ExprKind::Unary { operator, right } => {
                let right_ty = self.type_check_expr(right)?;
                if operator.kind == UnOpKind::Not && right_ty != Ty::Bool {
                    return compile_error("Type Error: operand should be 'bool'", right.node.span);
                }
                right_ty
            }

            ExprKind::Call { callee, args } => {
                if let ExprKind::Variable(ident) = &callee.kind {
                    // TODO: hack!
                    if ident.symbol.as_str() == "print" {
                        if args.len() != 1 {
                            return compile_error(
                                "The 'print' function requires a single argument",
                                expr.node.span,
                            );
                        }
                        return Ok(Ty::Void);
                    }

                    let sig = self.symbol_table.lookup_function(ident)?;

                    if args.len() != sig.params.len() {
                        return compile_error(
                            "Function called with incorrect number of arguments",
                            expr.node.span,
                        );
                    }
                    for (i, arg) in args.iter().enumerate() {
                        let arg_ty = self.type_check_expr(arg)?;
                        let param_ty = &sig.params[i];
                        if arg_ty != *param_ty {
                            return compile_error(
                                "Type Error: argument type mismatch",
                                arg.node.span,
                            );
                        }
                    }
                    sig.return_ty.clone()
                } else {
                    return compile_error("First class functions not supported", callee.node.span);
                }
            }
        };
        self.expression_types.insert(expr.node.id, ty.clone());
        Ok(ty)
    }
}
