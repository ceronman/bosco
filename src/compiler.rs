use std::collections::HashMap;
use std::rc::Rc;

use anyhow::{bail, Result};
use thiserror::Error;
use wasm_encoder::{
    BlockType, CodeSection, ConstExpr, DataSection, EntityType, ExportKind, ExportSection,
    FunctionSection, ImportSection, Instruction, MemorySection, MemoryType, TypeSection, ValType,
};

use crate::ast;
use crate::ast::{
    AssignTargetKind, BinOpKind, Expr, ExprKind, Function, ItemKind, LiteralKind, Module, NodeId,
    Stmt, StmtKind, Symbol, TypeParam, UnOpKind,
};
use crate::compiler::resolution::{FnSignature, SymbolTable};
use crate::lexer::Span;
use crate::parser::parse;

mod resolution;
#[cfg(test)]
mod test;
mod typecheck;

#[derive(Clone, Copy)]
struct WasmStr {
    memory: u32,
    offset: u32,
    len: u32,
}

#[derive(Error, Debug)]
#[error("Compilation Error: {msg} at {span:?}")]
pub struct CompileError {
    msg: String,
    span: Span,
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub enum Ty {
    Void,
    Int,
    Float,
    Bool,
    Array(Rc<Ty>, u32),
}

impl Ty {
    fn from_ast(ast_ty: &ast::Type) -> Result<Ty> {
        // TODO: check no type parameters for primitives
        let name = ast_ty.name.symbol.as_str();
        match name {
            "void" => Ok(Ty::Void),
            "int" => Ok(Ty::Int),
            "float" => Ok(Ty::Float),
            "bool" => Ok(Ty::Bool),
            "Array" => {
                let mut params = ast_ty.params.iter();
                let Some(TypeParam::Type(inner)) = params.next() else {
                    return compile_error(
                        "Array requires a valid inner type parameter",
                        ast_ty.node.span,
                    );
                };
                let Some(TypeParam::Const(size)) = params.next() else {
                    return compile_error(
                        "Array requires a valid size type parameter",
                        ast_ty.node.span,
                    );
                };
                let inner = Ty::from_ast(inner)?;
                Ok(Ty::Array(Rc::from(inner), *size))
            }
            _ => compile_error(format!("Unknown type {name}"), ast_ty.node.span),
        }
    }

    fn as_wasm(&self) -> Result<ValType> {
        match self {
            Ty::Int | Ty::Bool | Ty::Array(_, _) => Ok(ValType::I32),
            Ty::Float => Ok(ValType::F64),
            _ => bail!("{self:?} type does not have a wasm equivalent"),
        }
    }
}

#[derive(Default)]
struct Counter(u32);

impl Counter {
    fn next(&mut self) -> u32 {
        let current = self.0;
        self.0 += 1;
        current
    }
}

#[derive(Default)]
struct Compiler {
    strings: HashMap<NodeId, WasmStr>,
    symbol_table: SymbolTable,
    expression_types: HashMap<NodeId, Ty>,
    current_function: Option<Rc<FnSignature>>,
    types: TypeSection,
    functions: FunctionSection,
    memories: MemorySection,
    codes: CodeSection,
    data: DataSection,
    data_offset: u32,
    imports: ImportSection,
    exports: ExportSection,
}

impl Compiler {
    const MEM: u32 = 0;

    fn function(&mut self, function: &Function) -> Result<()> {
        // Declare type
        let mut params = Vec::new();
        for param in &function.params {
            let ty = Ty::from_ast(&param.ty)?;
            params.push(ty.as_wasm()?)
        }
        let returns: &[ValType] = if let Some(return_ty) = &function.return_ty {
            &[Ty::from_ast(return_ty)?.as_wasm()?]
        } else {
            &[]
        };
        let type_index = self.types.len();
        self.types.function(params, returns.iter().copied());
        self.functions.function(type_index);

        let signature = self.symbol_table.lookup_function(&function.name)?;

        let locals = signature
            .locals
            .iter()
            .map(Ty::as_wasm)
            .collect::<Result<Vec<_>>>()?
            .into_iter()
            .map(|t| (1, t));
        let mut wasm_function = wasm_encoder::Function::new(locals);
        self.statement(&mut wasm_function, &function.body)?;
        wasm_function.instruction(&Instruction::End);
        self.codes.function(&wasm_function);

        // Export
        if function.exported {
            self.exports.export(
                function.name.symbol.as_str(),
                ExportKind::Func,
                signature.index,
            );
        }
        Ok(())
    }

    fn module(&mut self, module: &Module) -> Result<()> {
        for item in &module.items {
            match &item.kind {
                ItemKind::Function(function) => {
                    self.function(function)?;
                }
            }
        }
        Ok(())
    }

    fn statement(&mut self, func: &mut wasm_encoder::Function, stmt: &Stmt) -> Result<()> {
        match &stmt.kind {
            StmtKind::Block { statements } => {
                for statement in statements {
                    self.statement(func, statement)?;
                }
            }
            StmtKind::ExprStmt(expr) => {
                self.expression(func, expr)?;
                // TODO: Fix case where expression leaves stuff on the stack
                // func.instruction(&Instruction::Drop);
            }

            StmtKind::Declaration { name, value, .. } => {
                if let Some(value) = value {
                    let local_var = self.symbol_table.lookup_var(name)?;
                    self.expression(func, value)?; // TODO: Define what to do when declared var is used in initializer
                    func.instruction(&Instruction::LocalSet(local_var.index));
                }
            }

            StmtKind::Assignment { target, value } => {
                let local_var = match &target.kind {
                    AssignTargetKind::Variable(name) => self.symbol_table.lookup_var(name)?,
                    AssignTargetKind::Array { .. } => {
                        return compile_error("Arrays are not suported yet", stmt.node.span)
                    }
                };
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

            StmtKind::Return { expr } => {
                self.expression(func, expr)?; // TODO: Check no more statements after last return
            }
        }
        Ok(())
    }

    fn expression(&mut self, func: &mut wasm_encoder::Function, expr: &Expr) -> Result<()> {
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
            ExprKind::Literal(LiteralKind::String(symbol)) => {
                let wasm_str = WasmStr {
                    memory: Compiler::MEM,
                    offset: self.data_offset,
                    len: symbol.as_str().len() as u32,
                };
                self.data_offset += wasm_str.len;
                self.strings.insert(expr.node.id, wasm_str);
                self.data.active(
                    wasm_str.memory,
                    &ConstExpr::i32_const(wasm_str.offset as i32),
                    symbol.as_str().bytes(),
                );
            }
            ExprKind::Binary {
                left,
                right,
                operator,
            } => {
                match &operator.kind {
                    BinOpKind::And => {
                        self.expression(func, left)?;
                        func.instruction(&Instruction::If(BlockType::Result(ValType::I32)));
                        self.expression(func, right)?;
                        func.instruction(&Instruction::Else);
                        func.instruction(&Instruction::I32Const(0));
                        func.instruction(&Instruction::End);
                        return Ok(());
                    }
                    BinOpKind::Or => {
                        self.expression(func, left)?;
                        func.instruction(&Instruction::If(BlockType::Result(ValType::I32)));
                        func.instruction(&Instruction::I32Const(1));
                        func.instruction(&Instruction::Else);
                        self.expression(func, right)?;
                        func.instruction(&Instruction::End);
                        return Ok(());
                    }
                    _ => {}
                }

                self.expression(func, left)?;
                self.expression(func, right)?;

                let Some(ty) = self.expression_types.get(&left.node.id) else {
                    return compile_error("Fatal: Not type found for expression", left.node.span);
                };

                match (&operator.kind, ty) {
                    (BinOpKind::Eq, Ty::Int) => func.instruction(&Instruction::I32Eq),
                    (BinOpKind::Eq, Ty::Float) => func.instruction(&Instruction::F64Eq),

                    (BinOpKind::Ne, Ty::Int) => func.instruction(&Instruction::I32Ne),
                    (BinOpKind::Ne, Ty::Float) => func.instruction(&Instruction::F64Ne),

                    (BinOpKind::Gt, Ty::Int) => func.instruction(&Instruction::I32GtS),
                    (BinOpKind::Gt, Ty::Float) => func.instruction(&Instruction::F64Gt),

                    (BinOpKind::Ge, Ty::Int) => func.instruction(&Instruction::I32GeS),
                    (BinOpKind::Ge, Ty::Float) => func.instruction(&Instruction::F64Ge),

                    (BinOpKind::Lt, Ty::Int) => func.instruction(&Instruction::I32LtS),
                    (BinOpKind::Lt, Ty::Float) => func.instruction(&Instruction::F64Lt),

                    (BinOpKind::Le, Ty::Int) => func.instruction(&Instruction::I32LeS),
                    (BinOpKind::Le, Ty::Float) => func.instruction(&Instruction::F64Le),

                    (BinOpKind::Add, Ty::Int) => func.instruction(&Instruction::I32Add),
                    (BinOpKind::Add, Ty::Float) => func.instruction(&Instruction::I32Add),

                    (BinOpKind::Sub, Ty::Int) => func.instruction(&Instruction::I32Sub),
                    (BinOpKind::Sub, Ty::Float) => func.instruction(&Instruction::F64Sub),

                    (BinOpKind::Mul, Ty::Int) => func.instruction(&Instruction::I32Mul),
                    (BinOpKind::Mul, Ty::Float) => func.instruction(&Instruction::F64Mul),

                    (BinOpKind::Div, Ty::Int) => func.instruction(&Instruction::I32DivS),
                    (BinOpKind::Div, Ty::Float) => func.instruction(&Instruction::F64Div),

                    (BinOpKind::Mod, Ty::Int) => func.instruction(&Instruction::I32RemS),

                    _ => {
                        return compile_error(
                            format!(
                                "Operator '{:?}' is not supported for type {ty:?}",
                                operator.kind
                            ),
                            operator.node.span,
                        )
                    }
                };
            }

            ExprKind::Unary { operator, right } => match operator.kind {
                UnOpKind::Not => {
                    self.expression(func, right)?;
                    func.instruction(&Instruction::If(BlockType::Result(ValType::I32)));
                    func.instruction(&Instruction::I32Const(0));
                    func.instruction(&Instruction::Else);
                    func.instruction(&Instruction::I32Const(1));
                    func.instruction(&Instruction::End);
                }
                UnOpKind::Neg => {
                    let Some(ty) = self.expression_types.get(&right.node.id) else {
                        return compile_error(
                            "Fatal: Not type found for expression",
                            right.node.span,
                        );
                    };

                    match ty {
                        Ty::Float => {
                            self.expression(func, right)?;
                            func.instruction(&Instruction::F64Neg);
                        }
                        Ty::Int => {
                            func.instruction(&Instruction::I32Const(0));
                            self.expression(func, right)?;
                            func.instruction(&Instruction::I32Sub);
                        }

                        _ => {
                            return compile_error(
                                format!(
                                    "Operator '{:?}' is not supported for type {ty:?}",
                                    operator.kind
                                ),
                                operator.node.span,
                            )
                        }
                    }
                }
            },
            ExprKind::Variable(ident) => {
                let local_var = self.symbol_table.lookup_var(ident)?;
                func.instruction(&Instruction::LocalGet(local_var.index));
            }
            ExprKind::ArrayIndex { .. } => {
                return compile_error("Unsupported array expr", expr.node.span)
            }
            ExprKind::Call { callee, args } => {
                let name = match &callee.kind {
                    ExprKind::Variable(ident) => ident,
                    _ => {
                        return compile_error(
                            "First class functions are not supported",
                            callee.node.span,
                        )
                    }
                };

                let signature = self.symbol_table.lookup_function(name)?;
                let arg = &args[0];
                // TODO: Hack!
                if name.symbol.as_str() == "print" {
                    return if let ExprKind::Literal(LiteralKind::String(_)) = &arg.kind {
                        self.expression(func, arg)?; // Needed to add the string value to data
                        let Some(was_str) = self.strings.get(&arg.node.id) else {
                            return compile_error("String constant not found", arg.node.span);
                        };
                        func.instruction(&Instruction::I32Const(was_str.offset as i32));
                        func.instruction(&Instruction::I32Const(was_str.len as i32));
                        func.instruction(&Instruction::Call(signature.index));
                        Ok(())
                    } else {
                        compile_error("Incorrect arguments for 'print'!", expr.node.span)
                    };
                }

                for arg in args {
                    self.expression(func, arg)?;
                }

                func.instruction(&Instruction::Call(signature.index));
            }
        }
        Ok(())
    }

    fn import_functions(&mut self) -> Result<()> {
        self.import_function("js", "print", &[Ty::Int, Ty::Int], Ty::Void)?;
        self.import_function("js", "print_int", &[Ty::Int], Ty::Void)?;
        self.import_function("js", "print_float", &[Ty::Float], Ty::Void)
    }

    fn import_function(
        &mut self,
        module: &'static str,
        name: &'static str,
        params: &[Ty],
        return_ty: Ty,
    ) -> Result<()> {
        let type_idx = self.types.len();
        let wasm_params = params.iter().map(Ty::as_wasm).collect::<Result<Vec<_>>>()?;
        let returns: &[ValType] = if return_ty == Ty::Void {
            &[]
        } else {
            &[return_ty.as_wasm()?]
        };
        self.types.function(wasm_params, returns.iter().copied());
        self.imports
            .import(module, name, EntityType::Function(type_idx));
        self.symbol_table
            .import_function(Symbol::from(name), params, return_ty)?;
        Ok(())
    }

    fn export_memory(&mut self) {
        let memory = MemoryType {
            minimum: 16, // TODO: temporary size
            maximum: None,
            memory64: false,
            shared: false,
            page_size_log2: None,
        };
        self.memories.memory(memory);
        self.exports.export("memory", ExportKind::Memory, 0);
    }

    fn encode_wasm(&mut self) -> Result<Vec<u8>> {
        let mut wasm_module = wasm_encoder::Module::new();
        wasm_module.section(&self.types);
        wasm_module.section(&self.imports);
        wasm_module.section(&self.functions);
        wasm_module.section(&self.memories);
        wasm_module.section(&self.exports);
        wasm_module.section(&self.codes);
        wasm_module.section(&self.data);
        Ok(wasm_module.finish())
    }

    fn compile(&mut self, module: &Module) -> Result<Vec<u8>> {
        self.import_functions()?;
        self.export_memory();
        self.symbol_table.resolve(module)?;
        self.type_check(module)?;
        self.module(module)?;
        self.encode_wasm()
    }
}

fn compile_error<T>(msg: impl Into<String>, span: Span) -> Result<T> {
    Err(CompileError {
        msg: msg.into(),
        span,
    }
    .into())
}

pub fn compile(source: &str) -> Result<Vec<u8>> {
    let module = parse(source)?;
    let mut compiler = Compiler::default();
    compiler.compile(&module)
}
