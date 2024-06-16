use anyhow::Result;
use std::collections::HashMap;
use thiserror::Error;

use crate::ast::{Expression, Literal, Module, Statement};
use wasm_encoder::ValType::I32;
use wasm_encoder::{
    BlockType, CodeSection, ConstExpr, DataSection, EntityType, ExportKind, ExportSection,
    Function, FunctionSection, ImportSection, Instruction, MemoryType, TypeSection, ValType,
};

use crate::lexer::{Token, TokenKind};
use crate::parser::{parse, ParseError};

#[cfg(test)]
mod test;

#[derive(Clone, Copy)]
struct WasmStr {
    memory: u32,
    offset: u32,
    len: u32,
}

#[derive(Error, Debug)]
pub enum CompileError {
    #[error("{0}")]
    ParseError(ParseError),
    #[error("Compilation error: {0}")]
    CompilationError(String),
}

impl From<ParseError> for CompileError {
    fn from(value: ParseError) -> Self {
        CompileError::ParseError(value)
    }
}

struct Compiler<'src> {
    source: &'src str,
    strings: HashMap<Token, WasmStr>,
    locals: HashMap<&'src str, (u32, ValType)>,
    fn_indices: HashMap<&'static str, u32>,
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
            locals: Default::default(),
            fn_indices: Default::default(),
            types: Default::default(),
            functions: Default::default(),
            codes: Default::default(),
            data: Default::default(),
            data_offset: Default::default(),
            imports: Default::default(),
            exports: Default::default(),
        }
    }

    fn maybe_declare_string(&mut self, expression: &Expression) {
        if let Expression::Literal(Literal::String { token, value }) = expression {
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
    }

    fn error<T>(&self, msg: &str) -> Result<T> {
        Err(CompileError::CompilationError(msg.to_string()).into())
    }

    fn resolve(&mut self, statements: &[Statement]) -> Result<()> {
        for statements in statements {
            match statements {
                Statement::Call { callee: _, args } => {
                    for arg in args {
                        self.maybe_declare_string(arg);
                    }
                }
                Statement::Declaration { name, ty, .. } => {
                    let name = name.lexeme(self.source);
                    let ty_lexeme = ty.lexeme(self.source);
                    let ty = match ty_lexeme {
                        "i32" => ValType::I32,
                        "i64" => ValType::I64,
                        "f32" => ValType::F32,
                        "f64" => ValType::F32,
                        _ => return self.error(&format!("Unsupported type {ty_lexeme}!")),
                    };
                    let local_idx = self.locals.len();
                    let entry = (local_idx as u32, ty);
                    self.locals.insert(name, entry);
                }

                Statement::Assignment { .. } => {} // TODO: Complete

                Statement::If {
                    then_block,
                    else_block,
                    ..
                } => {
                    self.resolve(then_block)?;
                    self.resolve(else_block)?;
                }

                Statement::While { body, .. } => self.resolve(body)?,
            }
        }
        Ok(())
    }

    fn main(&mut self, module: &Module) -> Result<()> {
        let type_index = self.types.len();
        self.types.function(vec![], vec![]);
        let main_fn_index = self.imports.len() - 1;
        self.functions.function(type_index);
        let mut locals = self.locals.values().copied().collect::<Vec<_>>();
        locals.sort();
        let mut main_function = Function::new(locals.iter().map(|(_i, ty)| (1, *ty)));
        self.statements(&mut main_function, &module.statements)?;
        main_function.instruction(&Instruction::End);
        self.codes.function(&main_function);
        self.exports
            .export("hello", ExportKind::Func, main_fn_index);
        Ok(())
    }

    fn statements(&mut self, func: &mut Function, statements: &[Statement]) -> Result<()> {
        for stmt in statements {
            match stmt {
                Statement::Call { callee, args, .. } => {
                    let callee_name = callee.lexeme(self.source);
                    let Some(&callee) = self.fn_indices.get(callee_name) else {
                        return self.error(&format!("Function '{callee_name}' not found!"));
                    };

                    match callee_name {
                        "print" => match args[..] {
                            [Expression::Literal(Literal::String { token, .. })] => {
                                let Some(was_str) = self.strings.get(&token) else {
                                    return self.error("Trying to print a non-existing string!");
                                };
                                func.instruction(&Instruction::I32Const(was_str.offset as i32));
                                func.instruction(&Instruction::I32Const(was_str.len as i32));
                                func.instruction(&Instruction::Call(callee));
                            }
                            _ => return self.error("Incorrect arguments for print!"),
                        },
                        "print_num" => {
                            if args.len() != 1 {
                                return self.error("Incorrect number of arguments for print_num!");
                            }
                            self.expression(func, &args[0])?;
                            func.instruction(&Instruction::Call(callee));
                        }
                        _ => return self.error(&format!("Unknown function {callee_name}")),
                    }
                }
                Statement::Declaration { name, value, .. }
                | Statement::Assignment { name, value } => {
                    let name = name.lexeme(self.source);
                    let Some(&(local_idx, _ty)) = self.locals.get(name) else {
                        return self.error("Undeclared variable");
                    };
                    self.expression(func, value)?;
                    func.instruction(&Instruction::LocalSet(local_idx));
                }

                Statement::If {
                    condition,
                    then_block,
                    else_block,
                } => {
                    self.expression(func, condition)?;
                    func.instruction(&Instruction::If(BlockType::Empty));
                    self.statements(func, then_block)?;
                    if !else_block.is_empty() {
                        func.instruction(&Instruction::Else);
                        self.statements(func, else_block)?;
                    }
                    func.instruction(&Instruction::End);
                }

                Statement::While { condition, body } => {
                    func.instruction(&Instruction::Loop(BlockType::Empty));
                    self.expression(func, condition)?;
                    func.instruction(&Instruction::If(BlockType::Empty));
                    self.statements(func, body)?;
                    func.instruction(&Instruction::Br(1)); // 1 refers to the loop instruction
                    func.instruction(&Instruction::End); // End of if
                    func.instruction(&Instruction::End); // End of loop
                }
            }
        }
        Ok(())
    }

    fn expression(&mut self, func: &mut Function, expr: &Expression) -> Result<()> {
        match expr {
            Expression::Literal(Literal::Number(value)) => {
                func.instruction(&Instruction::I32Const(*value));
            }
            Expression::Literal(Literal::String { .. }) => {
                todo!("Literal strings are not implemented")
            }
            Expression::Binary {
                left,
                right,
                operator,
            } => {
                self.expression(func, left)?;
                self.expression(func, right)?;

                // TODO: Not deal with tokens here?
                // TODO: Types!
                let ins = match operator.kind {
                    TokenKind::EqualEqual => Instruction::I32Eq,
                    TokenKind::BangEqual => Instruction::I32Ne,
                    TokenKind::Greater => Instruction::I32GtS,
                    TokenKind::GreaterEqual => Instruction::I32GeS,
                    TokenKind::Less => Instruction::I32LtS,
                    TokenKind::LessEqual => Instruction::I32LeS,
                    TokenKind::Plus => Instruction::I32Add,
                    TokenKind::Minus => Instruction::I32Sub,
                    TokenKind::Star => Instruction::I32Mul,
                    TokenKind::Slash => Instruction::I32DivS,
                    TokenKind::Percent => Instruction::I32RemS,
                    _ => return self.error(&format!("Unsupported operant {:?}", operator.kind)),
                };
                func.instruction(&ins);
            }
            Expression::Or { left, right } => {
                self.expression(func, left)?;
                func.instruction(&Instruction::If(BlockType::Result(I32)));
                func.instruction(&Instruction::I32Const(1));
                func.instruction(&Instruction::Else);
                self.expression(func, right)?;
                func.instruction(&Instruction::End);
            }
            Expression::And { left, right } => {
                self.expression(func, left)?;
                func.instruction(&Instruction::If(BlockType::Result(I32)));
                self.expression(func, right)?;
                func.instruction(&Instruction::Else);
                func.instruction(&Instruction::I32Const(0));
                func.instruction(&Instruction::End);
            }
            Expression::Not { right } => {
                self.expression(func, right)?;
                func.instruction(&Instruction::If(BlockType::Result(I32)));
                func.instruction(&Instruction::I32Const(0));
                func.instruction(&Instruction::Else);
                func.instruction(&Instruction::I32Const(1));
                func.instruction(&Instruction::End);
            }
            Expression::Variable { name } => {
                let name = name.lexeme(self.source);
                let Some((index, _ty)) = self.locals.get(&name) else {
                    return self.error("Trying to get non-existent local");
                };
                func.instruction(&Instruction::LocalGet(*index));
            }
        }
        Ok(())
    }

    fn compile(&mut self, module: &Module) -> Result<Vec<u8>> {
        let print_idx = self.import_function("js", "print", &[ValType::I32, ValType::I32], &[]);
        self.fn_indices.insert("print", print_idx);
        let print_idx = self.import_function("js", "print_num", &[ValType::I32], &[]);
        self.fn_indices.insert("print_num", print_idx);
        self.import_memory();
        self.resolve(&module.statements)?;
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
