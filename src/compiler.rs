use std::collections::{HashMap, VecDeque};

use anyhow::Result;
use thiserror::Error;
use wasm_encoder::{
    BlockType, CodeSection, ConstExpr, DataSection, EntityType, ExportKind, ExportSection,
    Function, FunctionSection, ImportSection, Instruction, MemoryType, TypeSection, ValType,
};

use crate::ast::{Expr, ExprKind, LiteralKind, Module, NodeId, Stmt, StmtKind};
use crate::lexer::{Span, Token, TokenKind};
use crate::parser::parse;

#[cfg(test)]
mod test;

#[derive(Clone, Copy)]
struct WasmStr {
    memory: u32,
    offset: u32,
    len: u32,
}

#[derive(Error, Debug)]
#[error("Compilation Error: {message} at {span:?}")]
pub struct CompileError {
    message: String,
    span: Span,
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum Ty {
    Int,
    Float,
    Bool,
}

impl Ty {
    // TODO: This should probably be at the parser level
    fn from_lexeme(lexeme: &str) -> Option<Ty> {
        match lexeme {
            "int" => Some(Ty::Int),
            "float" => Some(Ty::Float),
            "bool" => Some(Ty::Bool),
            _ => None,
        }
    }
}

#[derive(Copy, Clone, Debug)]
struct LocalVar {
    index: u32,
    ty: Ty,
}

struct SymbolTable<'src> {
    source: &'src str,
    environments: VecDeque<HashMap<String, LocalVar>>, // TODO: Use interned strings instead
    locals: HashMap<Token, LocalVar>,
}

impl<'src> SymbolTable<'src> {
    fn new(source: &'src str) -> Self {
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
            return Err(CompileError {
                message: format!("Variable '{name}' was declared outside of any scope"),
                span: name_token.span,
            }
            .into());
        };

        if env.contains_key(name) {
            return Err(CompileError {
                message: format!("Variable '{name}' was already declared in this scope"),
                span: name_token.span,
            }
            .into());
        }
        let ty_name = ty_token.span.as_str(self.source);
        let Some(ty) = Ty::from_lexeme(ty_name) else {
            return Err(CompileError {
                message: format!("Unknown type {ty_name}"),
                span: ty_token.span,
            }
            .into());
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
        Err(CompileError {
            message: format!("Undeclared variable '{name}'"),
            span: token.span,
        }
        .into())
    }

    fn lookup_var(&self, token: &Token) -> Result<LocalVar> {
        let name = token.span.as_str(self.source);
        self.locals
            .get(token)
            .ok_or(
                CompileError {
                    message: format!("Undeclared variable '{name}'"),
                    span: token.span,
                }
                .into(),
            )
            .copied()
    }

    fn begin_scope(&mut self) {
        self.environments.push_front(Default::default())
    }

    fn end_scope(&mut self) {
        self.environments.pop_front();
    }
}

struct Compiler<'src> {
    source: &'src str,
    strings: HashMap<Token, WasmStr>,
    symbol_table: SymbolTable<'src>,
    fn_indices: HashMap<&'static str, u32>,
    expression_types: HashMap<NodeId, Ty>,
    types: TypeSection,
    functions: FunctionSection,
    codes: CodeSection,
    data: DataSection,
    data_offset: u32,
    imports: ImportSection,
    exports: ExportSection,
}

impl<'src> Compiler<'src> {
    const MEM: u32 = 0;

    fn new(source: &'src str) -> Self {
        Compiler {
            source,
            strings: Default::default(),
            symbol_table: SymbolTable::new(source),
            fn_indices: Default::default(),
            expression_types: Default::default(),
            types: Default::default(),
            functions: Default::default(),
            codes: Default::default(),
            data: Default::default(),
            data_offset: Default::default(),
            imports: Default::default(),
            exports: Default::default(),
        }
    }

    fn error<T>(&self, msg: impl Into<String>, span: Span) -> Result<T> {
        Err(CompileError {
            message: msg.into(),
            span,
        }
        .into())
    }

    fn resolve(&mut self, statement: &Stmt) -> Result<()> {
        match &statement.kind {
            StmtKind::Block { statements } => {
                self.symbol_table.begin_scope();
                for statement in statements {
                    self.resolve(statement)?
                }
                self.symbol_table.end_scope();
            }
            StmtKind::Call { callee: _, args } => {
                for arg in args {
                    self.resolve_expression(arg)?;
                }
            }
            StmtKind::Declaration { name, ty, value } => {
                self.symbol_table.declare(name, ty)?;
                self.resolve_expression(value)?;
            }

            StmtKind::Assignment { name, value } => {
                self.symbol_table.resolve_var(name)?;
                self.resolve_expression(value)?;
            }

            StmtKind::If {
                condition,
                then_block,
                else_block,
            } => {
                self.resolve_expression(condition)?;
                self.resolve(then_block)?;
                else_block.as_ref().map(|b| self.resolve(b));
            }

            StmtKind::While { condition, body } => {
                self.resolve_expression(condition)?;
                self.resolve(body)?
            }
        }
        Ok(())
    }

    fn resolve_expression(&mut self, expr: &Expr) -> Result<()> {
        match &expr.kind {
            ExprKind::Literal(LiteralKind::String { token, value }) => {
                let wasm_str = WasmStr {
                    memory: Compiler::MEM,
                    offset: self.data_offset,
                    len: value.len() as u32,
                };
                self.data_offset += wasm_str.len;
                self.strings.insert(*token, wasm_str);
                self.data.active(
                    wasm_str.memory,
                    &ConstExpr::i32_const(wasm_str.offset as i32),
                    value.bytes(),
                );
            }
            ExprKind::Literal(_) => {}
            ExprKind::Variable { name } => self.symbol_table.resolve_var(name)?,
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

    fn type_check(&mut self, stmt: &Stmt) -> Result<()> {
        match &stmt.kind {
            StmtKind::Block { statements } => {
                for stmt in statements {
                    self.type_check(stmt)?
                }
            }
            StmtKind::Call { callee, args } => {
                let callee_name = callee.span.as_str(self.source);
                if args.len() != 1 {
                    return self.error(
                        format!("The '{callee_name}' function requires a single argument"),
                        stmt.node.span,
                    );
                }
                let arg_ty = self.type_check_expr(&args[0])?;
                match callee_name {
                    "print" => {} // TODO: Strings
                    "print_int" => {
                        if arg_ty != Ty::Int {
                            return self.error(
                                "Function 'print_int' requires an int as argument",
                                stmt.node.span,
                            );
                        }
                    }
                    "print_float" => {
                        if arg_ty != Ty::Float {
                            return self.error(
                                "Function 'print_float' requires an float as argument",
                                stmt.node.span,
                            );
                        }
                    }

                    _ => {
                        return self
                            .error(format!("Unknown function '{callee_name}'"), stmt.node.span)
                    } // TODO: duplicated error in compilation
                }
            }
            StmtKind::Declaration { name, value, .. } | StmtKind::Assignment { name, value } => {
                let initializer_ty = self.type_check_expr(value)?;
                let var_ty = self.symbol_table.lookup_var(name)?.ty;
                if initializer_ty != var_ty {
                    return self.error(
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
                    return self.error(
                        format!("Type Error: condition should be 'bool', but got {condition_ty:?}"),
                        condition.node.span,
                    );
                }
                self.type_check(then_block)?;
                if let Some(e) = else_block {
                    self.type_check(e)?;
                }
            }
            StmtKind::While { condition, body } => {
                let condition_ty = self.type_check_expr(condition)?;
                if condition_ty != Ty::Bool {
                    return self.error(
                        format!("Type Error: condition should be 'bool', but got {condition_ty:?}"),
                        condition.node.span,
                    );
                }
                self.type_check(body)?;
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
                    return self.error(
                        format!("Type Error: operator {:?} has incompatible types {left_ty:?} and {right_ty:?}", operator.kind),
                        expr.node.span,
                    );
                }

                if operator.kind == TokenKind::Percent && left_ty == Ty::Float {
                    return self.error(
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
                    return self.error("Type Error: operand should be 'bool'", left.node.span);
                }
                let right_ty = self.type_check_expr(right)?;
                if right_ty != Ty::Bool {
                    return self.error("Type Error: operand should be 'bool'", right.node.span);
                }
                Ty::Bool
            }
            ExprKind::Not { right } => {
                let right_ty = self.type_check_expr(right)?;
                if right_ty != Ty::Bool {
                    return self.error("Type Error: operand should be 'bool'", right.node.span);
                }
                Ty::Bool
            }
        };
        self.expression_types.insert(expr.node.id, ty);
        Ok(ty)
    }

    fn main(&mut self, module: &Module) -> Result<()> {
        let type_index = self.types.len();
        self.types.function(vec![], vec![]);
        let main_fn_index = self.imports.len() - 1;
        self.functions.function(type_index);
        let mut local_indices = self
            .symbol_table
            .locals
            .values()
            .copied()
            .collect::<Vec<_>>();
        local_indices.sort_by_key(|l| l.index);
        let locals = local_indices.iter().map(|l| match l.ty {
            Ty::Int | Ty::Bool => (1, ValType::I32),
            Ty::Float => (1, ValType::F64),
        });
        let mut main_function = Function::new(locals);
        self.statement(&mut main_function, &module.statement)?;
        main_function.instruction(&Instruction::End);
        self.codes.function(&main_function);
        self.exports
            .export("hello", ExportKind::Func, main_fn_index);
        Ok(())
    }

    fn statement(&mut self, func: &mut Function, stmt: &Stmt) -> Result<()> {
        match &stmt.kind {
            StmtKind::Block { statements } => {
                for statement in statements {
                    self.statement(func, statement)?;
                }
            }
            StmtKind::Call { callee, args, .. } => {
                let callee_name = callee.span.as_str(self.source);
                let Some(&callee) = self.fn_indices.get(callee_name) else {
                    return self.error(
                        format!("Function '{callee_name}' not found!"),
                        stmt.node.span,
                    );
                };

                match callee_name {
                    "print" => {
                        // NOTE Args are already checked in type check
                        if let ExprKind::Literal(LiteralKind::String { token, .. }) = args[0].kind {
                            let Some(was_str) = self.strings.get(&token) else {
                                return self.error("String constant not found", token.span);
                            };
                            func.instruction(&Instruction::I32Const(was_str.offset as i32));
                            func.instruction(&Instruction::I32Const(was_str.len as i32));
                            func.instruction(&Instruction::Call(callee));
                        } else {
                            return self.error("Incorrect arguments for 'print'!", stmt.node.span);
                        }
                    }
                    "print_int" | "print_float" => {
                        // NOTE Args are already checked in type check
                        self.expression(func, &args[0])?;
                        func.instruction(&Instruction::Call(callee));
                    }
                    _ => {
                        return self
                            .error(format!("Unknown function '{callee_name}'"), stmt.node.span)
                    }
                }
            }

            StmtKind::Declaration { name, value, .. } | StmtKind::Assignment { name, value } => {
                let local_var = self.symbol_table.lookup_var(name)?;
                self.expression(func, value)?; // TODO: Define what to do when declared var is used in initializer
                func.instruction(&Instruction::LocalSet(local_var.index));
            }

            StmtKind::If {
                condition,
                then_block,
                else_block,
            } => {
                self.expression(func, condition)?;
                func.instruction(&Instruction::If(BlockType::Empty));
                self.statement(func, then_block)?;
                if let Some(e) = else_block {
                    func.instruction(&Instruction::Else);
                    self.statement(func, e)?;
                }
                func.instruction(&Instruction::End);
            }

            StmtKind::While { condition, body } => {
                func.instruction(&Instruction::Loop(BlockType::Empty));
                self.expression(func, condition)?;
                func.instruction(&Instruction::If(BlockType::Empty));
                self.statement(func, body)?;
                func.instruction(&Instruction::Br(1)); // 1 refers to the loop instruction
                func.instruction(&Instruction::End); // End of if
                func.instruction(&Instruction::End); // End of loop
            }
        }
        Ok(())
    }

    fn expression(&mut self, func: &mut Function, expr: &Expr) -> Result<()> {
        match &expr.kind {
            ExprKind::Literal(LiteralKind::Int(value)) => {
                func.instruction(&Instruction::I32Const(*value));
            }
            ExprKind::Literal(LiteralKind::Bool(value)) => {
                if *value {
                    func.instruction(&Instruction::I32Const(1));
                } else {
                    func.instruction(&Instruction::I32Const(0));
                }
            }
            ExprKind::Literal(LiteralKind::Float(value)) => {
                func.instruction(&Instruction::F64Const(*value));
            }
            ExprKind::Literal(LiteralKind::String { .. }) => {
                todo!("Literal strings are not implemented")
            }
            ExprKind::Binary {
                left,
                right,
                operator,
            } => {
                self.expression(func, left)?;
                self.expression(func, right)?;

                let Some(&ty) = self.expression_types.get(&left.node.id) else {
                    return self.error("Fatal: Not type found for expression", left.node.span);
                };

                // TODO: Not deal with tokens here?
                let ins = match (operator.kind, ty) {
                    (TokenKind::EqualEqual, Ty::Int) => Instruction::I32Eq,
                    (TokenKind::EqualEqual, Ty::Float) => Instruction::F64Eq,

                    (TokenKind::BangEqual, Ty::Int) => Instruction::I32Ne,
                    (TokenKind::BangEqual, Ty::Float) => Instruction::F64Ne,

                    (TokenKind::Greater, Ty::Int) => Instruction::I32GtS,
                    (TokenKind::Greater, Ty::Float) => Instruction::F64Gt,

                    (TokenKind::GreaterEqual, Ty::Int) => Instruction::I32GeS,
                    (TokenKind::GreaterEqual, Ty::Float) => Instruction::F64Ge,

                    (TokenKind::Less, Ty::Int) => Instruction::I32LtS,
                    (TokenKind::Less, Ty::Float) => Instruction::F64Lt,

                    (TokenKind::LessEqual, Ty::Int) => Instruction::I32LeS,
                    (TokenKind::LessEqual, Ty::Float) => Instruction::F64Le,

                    (TokenKind::Plus, Ty::Int) => Instruction::I32Add,
                    (TokenKind::Plus, Ty::Float) => Instruction::I32Add,

                    (TokenKind::Minus, Ty::Int) => Instruction::I32Sub,
                    (TokenKind::Minus, Ty::Float) => Instruction::F64Sub,

                    (TokenKind::Star, Ty::Int) => Instruction::I32Mul,
                    (TokenKind::Star, Ty::Float) => Instruction::F64Mul,

                    (TokenKind::Slash, Ty::Int) => Instruction::I32DivS,
                    (TokenKind::Slash, Ty::Float) => Instruction::F64Div,

                    (TokenKind::Percent, Ty::Int) => Instruction::I32RemS,
                    _ => {
                        return self.error(
                            format!(
                                "Operator '{:?}' is not supported for type {ty:?}",
                                operator.kind
                            ),
                            operator.span,
                        )
                    }
                };
                func.instruction(&ins);
            }
            ExprKind::Or { left, right } => {
                self.expression(func, left)?;
                func.instruction(&Instruction::If(BlockType::Result(ValType::I32)));
                func.instruction(&Instruction::I32Const(1));
                func.instruction(&Instruction::Else);
                self.expression(func, right)?;
                func.instruction(&Instruction::End);
            }
            ExprKind::And { left, right } => {
                self.expression(func, left)?;
                func.instruction(&Instruction::If(BlockType::Result(ValType::I32)));
                self.expression(func, right)?;
                func.instruction(&Instruction::Else);
                func.instruction(&Instruction::I32Const(0));
                func.instruction(&Instruction::End);
            }
            ExprKind::Not { right } => {
                self.expression(func, right)?;
                func.instruction(&Instruction::If(BlockType::Result(ValType::I32)));
                func.instruction(&Instruction::I32Const(0));
                func.instruction(&Instruction::Else);
                func.instruction(&Instruction::I32Const(1));
                func.instruction(&Instruction::End);
            }
            ExprKind::Variable { name } => {
                let local_var = self.symbol_table.lookup_var(name)?;
                func.instruction(&Instruction::LocalGet(local_var.index));
            }
        }
        Ok(())
    }

    fn compile(&mut self, module: &Module) -> Result<Vec<u8>> {
        let print_idx = self.import_function("js", "print", &[ValType::I32, ValType::I32], &[]);
        self.fn_indices.insert("print", print_idx);
        let print_idx = self.import_function("js", "print_int", &[ValType::I32], &[]);
        self.fn_indices.insert("print_int", print_idx);
        let print_idx = self.import_function("js", "print_float", &[ValType::F64], &[]);
        self.fn_indices.insert("print_float", print_idx);
        self.import_memory();
        self.symbol_table.begin_scope();
        self.resolve(&module.statement)?;
        self.symbol_table.end_scope();
        self.type_check(&module.statement)?;
        self.main(module)?;

        let mut wasm_module = wasm_encoder::Module::new();

        wasm_module.section(&self.types);
        wasm_module.section(&self.imports);
        wasm_module.section(&self.functions);
        wasm_module.section(&self.exports);
        wasm_module.section(&self.codes);
        wasm_module.section(&self.data);

        Ok(wasm_module.finish())
    }

    fn import_function(
        &mut self,
        module: &str,
        name: &str,
        params: &[ValType],
        results: &[ValType],
    ) -> u32 {
        let type_idx = self.types.len();
        self.types
            .function(params.iter().copied(), results.iter().copied());
        let import_idx = self.imports.len();
        self.imports
            .import(module, name, EntityType::Function(type_idx));
        import_idx
    }

    fn import_memory(&mut self) {
        self.imports.import(
            "js",
            "mem",
            EntityType::Memory(MemoryType {
                minimum: 0,
                maximum: None,
                memory64: false,
                shared: false,
                page_size_log2: None,
            }),
        );
    }
}

pub fn compile(source: &str) -> Result<Vec<u8>> {
    let module = parse(source)?;
    let mut compiler = Compiler::new(source);
    compiler.compile(&module)
}
