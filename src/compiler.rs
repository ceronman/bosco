use anyhow::Result;
use std::collections::{HashMap, VecDeque};
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
    CompilationError(String), // TODO: Add proper positions to the errors
}

impl From<ParseError> for CompileError {
    fn from(value: ParseError) -> Self {
        CompileError::ParseError(value)
    }
}

struct SymbolTable<'src> {
    source: &'src str,
    environments: VecDeque<HashMap<String, u32>>, // TODO: Use interned strings instead
    locals: HashMap<Token, u32>,
}

impl<'src> SymbolTable<'src> {
    fn new(source: &'src str) -> Self {
        SymbolTable {
            source,
            environments: Default::default(),
            locals: Default::default(),
        }
    }

    fn declare(&mut self, token: Token) -> Result<u32> {
        let index: u32 = self.locals.len().try_into()?;
        let name = token.lexeme(self.source);
        let Some(env) = self.environments.front_mut() else {
            return Err(CompileError::CompilationError("There are no scopes".into()).into());
        };

        if env.contains_key(name) {
            return Err(CompileError::CompilationError(format!(
                "Variable {name} is already declared!"
            ))
            .into());
        }
        env.insert(name.into(), index);
        Ok(index)
    }

    fn resolve_var(&mut self, token: Token) -> Result<()> {
        let name = token.lexeme(self.source);
        for env in &self.environments {
            if let Some(&index) = env.get(name) {
                self.locals.insert(token, index);
                return Ok(());
            }
        }
        Err(CompileError::CompilationError(format!("Unable to resolve variable {name}")).into())
    }

    fn lookup_var(&self, token: Token) -> Result<u32> {
        let name = token.lexeme(self.source);
        self.locals
            .get(&token)
            .ok_or(CompileError::CompilationError(format!("Undeclared variable {name}")).into())
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
            types: Default::default(),
            functions: Default::default(),
            codes: Default::default(),
            data: Default::default(),
            data_offset: Default::default(),
            imports: Default::default(),
            exports: Default::default(),
        }
    }

    fn error<T>(&self, msg: &str) -> Result<T> {
        Err(CompileError::CompilationError(msg.to_string()).into())
    }

    fn resolve(&mut self, statement: &Statement) -> Result<()> {
        match statement {
            Statement::Block { statements } => {
                self.symbol_table.begin_scope();
                for statement in statements {
                    self.resolve(statement)?
                }
                self.symbol_table.end_scope();
            }
            Statement::Call { callee: _, args } => {
                for arg in args {
                    self.resolve_expression(arg)?;
                }
            }
            Statement::Declaration {
                name,
                ty: _ty,
                value,
            } => {
                self.symbol_table.declare(*name)?;
                self.symbol_table.resolve_var(*name)?;
                self.resolve_expression(value)?;
            }

            Statement::Assignment { name, value } => {
                self.symbol_table.resolve_var(*name)?;
                self.resolve_expression(value)?;
            }

            Statement::If {
                condition,
                then_block,
                else_block,
            } => {
                self.resolve_expression(condition)?;
                self.resolve(then_block)?;
                else_block.as_ref().map(|b| self.resolve(b));
            }

            Statement::While { condition, body } => {
                self.resolve_expression(condition)?;
                self.resolve(body)?
            }
        }
        Ok(())
    }

    fn resolve_expression(&mut self, expr: &Expression) -> Result<()> {
        match expr {
            Expression::Literal(Literal::String { token, value }) => {
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
            Expression::Literal(_) => {}
            Expression::Variable { name } => self.symbol_table.resolve_var(*name)?,
            Expression::Binary { left, right, .. }
            | Expression::Or { left, right, .. }
            | Expression::And { left, right, .. } => {
                self.resolve_expression(left)?;
                self.resolve_expression(right)?;
            }
            Expression::Not { right } => self.resolve_expression(right)?,
        }
        Ok(())
    }

    fn main(&mut self, module: &Module) -> Result<()> {
        let type_index = self.types.len();
        self.types.function(vec![], vec![]);
        let main_fn_index = self.imports.len() - 1;
        self.functions.function(type_index);
        let num_locals: u32 = self.symbol_table.locals.len().try_into()?;
        let mut main_function = Function::new([(num_locals, ValType::I32)]);
        self.statement(&mut main_function, &module.statement)?;
        main_function.instruction(&Instruction::End);
        self.codes.function(&main_function);
        self.exports
            .export("hello", ExportKind::Func, main_fn_index);
        Ok(())
    }

    fn statement(&mut self, func: &mut Function, statement: &Statement) -> Result<()> {
        match statement {
            Statement::Block { statements } => {
                for statement in statements {
                    self.statement(func, statement)?;
                }
            }
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

            Statement::Declaration { name, value, .. } | Statement::Assignment { name, value } => {
                let local_idx = self.symbol_table.lookup_var(*name)?;
                self.expression(func, value)?; // TODO: Define what to do when declared var is used in initializer
                func.instruction(&Instruction::LocalSet(local_idx));
            }

            Statement::If {
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

            Statement::While { condition, body } => {
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
                let index = self.symbol_table.lookup_var(*name)?;
                func.instruction(&Instruction::LocalGet(index));
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
        self.symbol_table.begin_scope();
        self.resolve(&module.statement)?;
        self.symbol_table.end_scope();
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