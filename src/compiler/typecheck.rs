use crate::ast::{
    BinOpKind, Expr, ExprKind, Function, Item, ItemKind, LiteralKind, Module, Stmt, StmtKind,
    UnOpKind,
};
use crate::compiler::{Compiler, Ty};
use crate::error::{error, CompilerResult};

// TODO: Make into an independent compilation unit like Symbol Table?
impl Compiler {
    pub(super) fn type_check(&mut self, module: &Module) -> CompilerResult<()> {
        for item in &module.items {
            self.type_check_item(item)?;
        }
        Ok(())
    }

    fn type_check_item(&mut self, item: &Item) -> CompilerResult<()> {
        match &item.kind {
            ItemKind::Function(f) => self.type_check_function(f)?,

            ItemKind::Record(_) => todo!(),
        }
        Ok(())
    }

    fn type_check_function(&mut self, function: &Function) -> CompilerResult<()> {
        self.current_function = Some(self.symbol_table.lookup_function(&function.name)?);
        self.type_check_stmt(&function.body)?;
        Ok(())
    }

    fn type_check_stmt(&mut self, stmt: &Stmt) -> CompilerResult<()> {
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
                        return Err(error!(
                            value.node.span,
                            "Type Error: expected {var_ty:?} but found {initializer_ty:?}"
                        ));
                    }
                }
            }
            StmtKind::Assignment { target, value } => {
                let var_ty = self.type_check_expr(target)?;
                let initializer_ty = self.type_check_expr(value)?;
                if initializer_ty != var_ty {
                    return Err(error!(
                        value.node.span,
                        "Type Error: expected {var_ty:?} but found {initializer_ty:?}"
                    ));
                }
            }
            StmtKind::If {
                condition,
                then_block,
                else_block,
            } => {
                let condition_ty = self.type_check_expr(condition)?;
                if condition_ty != Ty::Bool {
                    return Err(error!(
                        condition.node.span,
                        "Type Error: condition should be 'bool', but got {condition_ty:?}"
                    ));
                }
                self.type_check_stmt(then_block)?;
                if let Some(e) = else_block {
                    self.type_check_stmt(e)?;
                }
            }
            StmtKind::While { condition, body } => {
                let condition_ty = self.type_check_expr(condition)?;
                if condition_ty != Ty::Bool {
                    return Err(error!(
                        condition.node.span,
                        "Type Error: condition should be 'bool', but got {condition_ty:?}"
                    ));
                }
                self.type_check_stmt(body)?;
            }

            StmtKind::Return { expr } => {
                let Some(signature) = self.current_function.clone() else {
                    return Err(error!(stmt.node.span, "Return outside of a function"));
                };
                let expr_ty = self.type_check_expr(expr)?;
                if expr_ty != signature.return_ty {
                    return Err(error!(
                        stmt.node.span,
                        "Type Error: return type mismatch, expected {:?}, but found {expr_ty:?}",
                        signature.return_ty
                    ));
                }
            }
        }
        Ok(())
    }

    fn type_check_expr(&mut self, expr: &Expr) -> CompilerResult<Ty> {
        let ty = match &expr.kind {
            ExprKind::Literal(LiteralKind::Int(_)) => Ty::Int,
            ExprKind::Literal(LiteralKind::Float(_)) => Ty::Float,
            ExprKind::Literal(LiteralKind::String { .. }) => Ty::Int, // TODO: Add String type
            ExprKind::Literal(LiteralKind::Bool(_)) => Ty::Bool,
            ExprKind::Variable(ident) => {
                let local_var = self.symbol_table.lookup_var(ident)?;
                local_var.ty.clone()
            }
            ExprKind::ArrayIndex { expr, index } => {
                let index_ty = self.type_check_expr(index)?;
                if index_ty != Ty::Int {
                    return Err(error!(
                        index.node.span,
                        "Type Error: Array index must be Int"
                    ));
                }
                let expr_ty = self.type_check_expr(expr)?;
                let Ty::Array(inner, _) = expr_ty else {
                    return Err(error!(
                        expr.node.span,
                        "Type Error: Expecting an Array, found {expr_ty:?}"
                    ));
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
                    | BinOpKind::Gt => Ty::Bool,
                    BinOpKind::And | BinOpKind::Or => {
                        if left_ty != Ty::Bool {
                            return Err(error!(
                                left.node.span,
                                "Type Error: operand should be 'bool'",
                            ));
                        }
                        if right_ty != Ty::Bool {
                            return Err(error!(
                                right.node.span,
                                "Type Error: operand should be 'bool'",
                            ));
                        }
                        Ty::Bool
                    }
                    BinOpKind::Mod if left_ty == Ty::Float => {
                        return Err(error!(
                            expr.node.span,
                            "Type Error: '%' operator doesn't work on floats",
                        ));
                    }
                    _ => left_ty,
                }
            }
            ExprKind::Unary { operator, right } => {
                let right_ty = self.type_check_expr(right)?;
                if operator.kind == UnOpKind::Not && right_ty != Ty::Bool {
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
                        return Ok(Ty::Void);
                    }

                    let sig = self.symbol_table.lookup_function(ident)?;

                    if args.len() != sig.params.len() {
                        return Err(error!(
                            expr.node.span,
                            "Function called with incorrect number of arguments",
                        ));
                    }
                    for (i, arg) in args.iter().enumerate() {
                        let arg_ty = self.type_check_expr(arg)?;
                        let param_ty = &sig.params[i];
                        if arg_ty != *param_ty {
                            return Err(error!(
                                arg.node.span,
                                "Type Error: argument type mismatch",
                            ));
                        }
                    }
                    sig.return_ty.clone()
                } else {
                    return Err(error!(
                        callee.node.span,
                        "First class functions not supported",
                    ));
                }
            }
        };
        self.expression_types.insert(expr.node.id, ty.clone());
        Ok(ty)
    }
}
