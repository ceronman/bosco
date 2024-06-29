use std::collections::HashMap;

use anyhow::Result;
use thiserror::Error;
use wasm_encoder::{
    BlockType, CodeSection, ConstExpr, DataSection, EntityType, ExportKind, ExportSection,
    FunctionSection, ImportSection, Instruction, MemoryType, TypeSection, ValType,
};

use crate::ast::{Expr, ExprKind, Function, ItemKind, LiteralKind, Module, NodeId, Stmt, StmtKind};
use crate::compiler::resolution::SymbolTable;
use crate::lexer::{Span, Token, TokenKind};
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

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum Ty {
    Void,
    Int,
    Float,
    Bool,
}

impl Ty {
    // TODO: This should probably be at the parser level
    fn from_lexeme(token: &Token, source: &str) -> Result<Ty> {
        let lexeme = token.span.as_str(source);
        match lexeme {
            "void" => Ok(Ty::Void),
            "int" => Ok(Ty::Int),
            "float" => Ok(Ty::Float),
            "bool" => Ok(Ty::Bool),
            _ => compile_error(format!("Unknown type {lexeme}"), token.span),
        }
    }

    fn from_wasm(wasm_ty: &ValType) -> Ty {
        match wasm_ty {
            ValType::I32 => Ty::Int,
            ValType::I64 => todo!(),
            ValType::F32 => todo!(),
            ValType::F64 => Ty::Float,
            ValType::V128 => todo!(),
            ValType::Ref(_) => todo!(),
        }
    }

    fn as_wasm(&self) -> ValType {
        match self {
            Ty::Void => todo!(),
            Ty::Int => ValType::I32,
            Ty::Float => ValType::F64,
            Ty::Bool => ValType::I32,
        }
    }
}

struct Counter(u32);

impl Counter {
    fn next(&mut self) -> u32 {
        let current = self.0;
        self.0 += 1;
        current
    }

    fn reset(&mut self) {
        self.0 = 0;
    }
}

struct Compiler<'src> {
    source: &'src str,
    strings: HashMap<Token, WasmStr>,
    symbol_table: SymbolTable<'src>,
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

    fn function(&mut self, function: &Function) -> Result<()> {
        // Declare type
        let mut params = Vec::new();
        for param in &function.params {
            let ty = Ty::from_lexeme(&param.ty, self.source)?;
            params.push(ty.as_wasm())
        }
        let returns: &[ValType] = if let Some(return_ty) = function.return_ty {
            &[Ty::from_lexeme(&return_ty, self.source)?.as_wasm()]
        } else {
            &[]
        };
        let type_index = self.types.len();
        self.types.function(params, returns.iter().copied());
        self.functions.function(type_index);

        // Type check
        self.type_check_function(function)?; // TODO: Move outside

        let name = function.name.span.as_str(self.source);
        let Some(signature) = self.symbol_table.lookup_function(name) else {
            return compile_error("Unresolved function", function.name.span);
        };

        let locals = signature.local_vars.iter().map(|ty| (1, ty.as_wasm()));
        let mut wasm_function = wasm_encoder::Function::new(locals);
        self.statement(&mut wasm_function, &function.body)?;
        wasm_function.instruction(&Instruction::End);
        self.codes.function(&wasm_function);

        // Export
        if function.exported {
            self.exports.export(name, ExportKind::Func, signature.index);
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
                // func.instruction(&Instruction::Drop);
            }

            // StmtKind::Call { callee, args, .. } => {
            //     let callee_name = callee.span.as_str(self.source);
            //     let Some(&callee) = self.fn_indices.get(callee_name) else {
            //         return compile_error(
            //             format!("Function '{callee_name}' not found!"),
            //             stmt.node.span,
            //         );
            //     };
            //
            //     match callee_name {
            //         "print" => {
            //             // NOTE Args are already checked in type check
            //             self.expression(func, &args[0])?; // Needed to add the string value
            //             if let ExprKind::Literal(LiteralKind::String { token, .. }) = args[0].kind {
            //                 let Some(was_str) = self.strings.get(&token) else {
            //                     return compile_error("String constant not found", token.span);
            //                 };
            //                 func.instruction(&Instruction::I32Const(was_str.offset as i32));
            //                 func.instruction(&Instruction::I32Const(was_str.len as i32));
            //                 func.instruction(&Instruction::Call(callee));
            //             } else {
            //                 return compile_error(
            //                     "Incorrect arguments for 'print'!",
            //                     stmt.node.span,
            //                 );
            //             }
            //         }
            //         "print_int" | "print_float" => {
            //             // NOTE Args are already checked in type check
            //             self.expression(func, &args[0])?;
            //             func.instruction(&Instruction::Call(callee));
            //         }
            //         _ => {
            //             return compile_error(
            //                 format!("Unknown function '{callee_name}'"),
            //                 stmt.node.span,
            //             )
            //         }
            //     }
            // }
            StmtKind::Declaration { name, value, .. } => {
                if let Some(value) = value {
                    let local_var = self.symbol_table.lookup_var(name)?;
                    self.expression(func, value)?; // TODO: Define what to do when declared var is used in initializer
                    func.instruction(&Instruction::LocalSet(local_var.index));
                }
            }

            StmtKind::Assignment { name, value } => {
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
            ExprKind::Binary {
                left,
                right,
                operator,
            } => {
                self.expression(func, left)?;
                self.expression(func, right)?;

                let Some(&ty) = self.expression_types.get(&left.node.id) else {
                    return compile_error("Fatal: Not type found for expression", left.node.span);
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
                        return compile_error(
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

            ExprKind::Call { callee, args } => {
                let name = match callee.kind {
                    ExprKind::Variable { name } => name.span.as_str(self.source),
                    _ => {
                        return compile_error(
                            "First class functions are not supported",
                            callee.node.span,
                        )
                    }
                };

                let Some(signature) = self.symbol_table.lookup_function(name) else {
                    return compile_error("Unresolved function", expr.node.span);
                };

                // TODO: Hack!
                if name == "print" {
                    if let ExprKind::Literal(LiteralKind::String { token, .. }) = args[0].kind {
                        self.expression(func, &args[0])?; // Needed to add the string value to data
                        let Some(was_str) = self.strings.get(&token) else {
                            return compile_error("String constant not found", token.span);
                        };
                        func.instruction(&Instruction::I32Const(was_str.offset as i32));
                        func.instruction(&Instruction::I32Const(was_str.len as i32));
                        func.instruction(&Instruction::Call(signature.index));
                        return Ok(());
                    } else {
                        return compile_error("Incorrect arguments for 'print'!", expr.node.span);
                    }
                }

                for arg in args {
                    self.expression(func, arg)?;
                }

                func.instruction(&Instruction::Call(signature.index));
            }
        }
        Ok(())
    }

    fn import_functions(&mut self) {
        self.import_function("js", "print", &[ValType::I32, ValType::I32], &[]);
        self.import_function("js", "print_int", &[ValType::I32], &[]);
        self.import_function("js", "print_float", &[ValType::F64], &[]);
    }

    fn import_function(
        &mut self,
        module: &'static str,
        name: &'static str,
        params: &[ValType],
        results: &[ValType],
    ) {
        let type_idx = self.types.len();
        self.types
            .function(params.iter().copied(), results.iter().copied());
        self.imports
            .import(module, name, EntityType::Function(type_idx));
        self.symbol_table.import_function(
            name,
            params.iter().map(Ty::from_wasm).collect(),
            match results.len() {
                0 => Ty::Void,
                1 => Ty::from_wasm(&results[0]),
                _ => todo!(),
            },
        );
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

    fn encode_wasm(&mut self) -> Result<Vec<u8>> {
        let mut wasm_module = wasm_encoder::Module::new();
        wasm_module.section(&self.types);
        wasm_module.section(&self.imports);
        wasm_module.section(&self.functions);
        wasm_module.section(&self.exports);
        wasm_module.section(&self.codes);
        wasm_module.section(&self.data);
        Ok(wasm_module.finish())
    }

    fn compile(&mut self, module: &Module) -> Result<Vec<u8>> {
        self.import_functions();
        self.import_memory();
        self.symbol_table.resolve(module)?;
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
    let mut compiler = Compiler::new(source);
    compiler.compile(&module)
}
