use crate::ast::{Expr, ExprKind, Function, LiteralKind, Stmt, StmtKind};
use crate::compiler::{compile_error, Compiler, Ty};
use crate::lexer::TokenKind;
use anyhow::Result;

impl<'src> Compiler<'src> {
    pub(super) fn type_check_function(&mut self, function: &Function) -> Result<()> {
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
            StmtKind::Call { callee, args } => {
                let callee_name = callee.span.as_str(self.source);
                if args.len() != 1 {
                    return compile_error(
                        format!("The '{callee_name}' function requires a single argument"),
                        stmt.node.span,
                    );
                }
                let arg_ty = self.type_check_expr(&args[0])?;
                match callee_name {
                    "print" => {} // TODO: Strings
                    "print_int" => {
                        if arg_ty != Ty::Int {
                            return compile_error(
                                "Function 'print_int' requires an int as argument",
                                stmt.node.span,
                            );
                        }
                    }
                    "print_float" => {
                        if arg_ty != Ty::Float {
                            return compile_error(
                                "Function 'print_float' requires an float as argument",
                                stmt.node.span,
                            );
                        }
                    }

                    _ => {
                        return compile_error(
                            format!("Unknown function '{callee_name}'"),
                            stmt.node.span,
                        )
                    } // TODO: duplicated error in compilation
                }
            }
            StmtKind::Declaration { name, value, .. } => {
                let var_ty = self.symbol_table.lookup_var(name)?.ty;
                if let Some(value) = value {
                    let initializer_ty = self.type_check_expr(value)?;
                    if initializer_ty != var_ty {
                        return compile_error(
                            format!("Type Error: expected {var_ty:?} but found {initializer_ty:?}"),
                            value.node.span,
                        );
                    }
                }
            }
            StmtKind::Assignment { name, value } => {
                let var_ty = self.symbol_table.lookup_var(name)?.ty;
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
                self.type_check_expr(expr)?;
                // TODO: Check that matches current function
            }
        }
        Ok(())
    }

    fn type_check_expr(&mut self, expr: &Expr) -> Result<Ty> {
        let ty = match &expr.kind {
            ExprKind::Literal(LiteralKind::Int(_)) => Ty::Int,
            ExprKind::Literal(LiteralKind::Float(_)) => Ty::Float,
            ExprKind::Literal(LiteralKind::String { .. }) => Ty::Int, // TODO: Fix me!
            ExprKind::Literal(LiteralKind::Bool(_)) => Ty::Bool,      // TODO: Fix me!
            ExprKind::Variable { name } => {
                let local_var = self.symbol_table.lookup_var(name)?;
                local_var.ty
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

                if operator.kind == TokenKind::Percent && left_ty == Ty::Float {
                    return compile_error(
                        "Type Error: '%' operator doesn't work on floats",
                        expr.node.span,
                    );
                }

                match operator.kind {
                    TokenKind::LessEqual
                    | TokenKind::Less
                    | TokenKind::EqualEqual
                    | TokenKind::BangEqual
                    | TokenKind::GreaterEqual
                    | TokenKind::Greater => Ty::Bool,
                    _ => left_ty,
                }
            }
            ExprKind::Or { left, right } | ExprKind::And { left, right } => {
                let left_ty = self.type_check_expr(left)?;

                if left_ty != Ty::Bool {
                    return compile_error("Type Error: operand should be 'bool'", left.node.span);
                }
                let right_ty = self.type_check_expr(right)?;
                if right_ty != Ty::Bool {
                    return compile_error("Type Error: operand should be 'bool'", right.node.span);
                }
                Ty::Bool
            }
            ExprKind::Not { right } => {
                let right_ty = self.type_check_expr(right)?;
                if right_ty != Ty::Bool {
                    return compile_error("Type Error: operand should be 'bool'", right.node.span);
                }
                Ty::Bool
            }
        };
        self.expression_types.insert(expr.node.id, ty);
        Ok(ty)
    }
}
