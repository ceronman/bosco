use std::collections::HashMap;
use std::rc::Rc;

use wasm_encoder::{
    BlockType, CodeSection, ConstExpr, DataSection, EntityType, ExportKind, ExportSection,
    FunctionSection, ImportSection, Instruction, MemArg, MemorySection, MemoryType, TypeSection,
    ValType,
};

use crate::ast::{BinOpKind, Expr, ExprKind, Function, Identifier, ItemKind, LiteralKind, Module, NodeId, Stmt, StmtKind, Symbol, UnOpKind};
use crate::compiler::resolution::{Address, FnSignature, SymbolTable};
use crate::compiler::resolver::Resolver;
use crate::error::{error, CompilerResult};
use crate::lexer::Span;
use crate::parser::parse;

mod resolution;
#[cfg(test)]
mod test;
mod typecheck;
mod resolver;

#[derive(Clone, Copy)]
struct WasmStr {
    memory: u32,
    offset: u32,
    len: u32,
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub enum Ty {
    Void,
    Int,
    Float,
    Bool,
    Array(Rc<Ty>, u32),
    Record(Vec<Field>),
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub struct Field {
    name: Symbol,
    ty: Rc<Ty>,
}

impl Ty {
    fn size(&self) -> u32 {
        match self {
            Ty::Void => 0,
            Ty::Int => 4,
            Ty::Float => 8,
            Ty::Bool => 1,
            Ty::Array(inner, length) => inner.size() * length,
            Ty::Record(fields) => fields.iter().map(|f| f.ty.size()).sum(),
        }
    }

    fn as_wasm(&self) -> CompilerResult<ValType> {
        match self {
            Ty::Int | Ty::Bool | Ty::Array(_, _) | Ty::Record(_) => Ok(ValType::I32), // TODO: specify
            Ty::Float => Ok(ValType::F64),
            _ => Err(error!(
                Span(0, 0),
                "{self:?} type does not have a wasm equivalent"
            )),
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

    fn function(&mut self, function: &Function) -> CompilerResult<()> {
        // Declare type
        let mut params = Vec::new();
        for param in &function.params {
            let ty = self.symbol_table.lookup_type(&param.ty)?;
            params.push(ty.as_wasm()?)
        }
        let returns: &[ValType] = if let Some(return_ty) = &function.return_ty {
            &[self.symbol_table.lookup_type(&return_ty)?.as_wasm()?]
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
            .collect::<CompilerResult<Vec<_>>>()?
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

    fn module(&mut self, module: &Module) -> CompilerResult<()> {
        for item in &module.items {
            match &item.kind {
                ItemKind::Function(function) => {
                    self.function(function)?;
                }

                ItemKind::Record(_) => {}
            }
        }
        Ok(())
    }

    fn statement(&mut self, func: &mut wasm_encoder::Function, stmt: &Stmt) -> CompilerResult<()> {
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
                    match local_var.address {
                        Address::Var(index) => {
                            func.instruction(&Instruction::LocalSet(index));
                        }
                        Address::Mem(_) => {}
                        Address::None => {}
                    }
                }
            }

            StmtKind::Assignment { target, value } => match &target.kind {
                ExprKind::Variable(name) => {
                    let local = self.symbol_table.lookup_var(name)?;
                    let Address::Var(index) = local.address else {
                        return Err(error!(
                            name.node.span,
                            "Panic: invalid address for variable",
                        ));
                    };
                    self.expression(func, value)?;
                    func.instruction(&Instruction::LocalSet(index));
                }
                ExprKind::ArrayIndex { .. } | ExprKind::FieldAccess { .. } => {
                    self.push_address(func, target)?;
                    self.expression(func, value)?;

                    let instruction = match self.expression_types.get(&value.node.id) {
                        // TODO: support this via polymorphism
                        Some(Ty::Int) => Instruction::I32Store(MemArg {
                            offset: 0,
                            align: 2,
                            memory_index: 0,
                        }),
                        Some(Ty::Float) => Instruction::F64Store(MemArg {
                            offset: 0,
                            align: 3,
                            memory_index: 0,
                        }),
                        Some(Ty::Bool) => Instruction::I32Store8(MemArg {
                            offset: 0,
                            align: 0,
                            memory_index: 0,
                        }),
                        _ => {
                            return Err(error!(value.node.span, "Can't store expression in Array",))
                        }
                    };
                    func.instruction(&instruction);
                }
                ExprKind::FieldAccess { expr, field } => {
                }
                _ => {
                    return Err(error!(
                        stmt.node.span,
                        "Unsupported left side of assignment"
                    ))
                }
            },

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

    fn push_address(
        &mut self,
        func: &mut wasm_encoder::Function,
        target: &Expr,
    ) -> CompilerResult<Ty> {
        match &target.kind {
            ExprKind::Variable(name) => {
                let local = self.symbol_table.lookup_var(name)?;
                let Address::Mem(addr) = local.address else {
                    return Err(error!(
                        name.node.span,
                        "Panic: invalid address for variable"
                    ));
                };
                func.instruction(&Instruction::I32Const(addr as i32));
                Ok(local.ty.clone())
            }
            ExprKind::ArrayIndex { expr, index } => {
                let ty = self.push_address(func, expr)?;
                // TODO: Check bounds
                let Ty::Array(inner, _size) = ty else {
                    return Err(error!(
                        expr.node.span,
                        "Panic: trying to index something that is not an array",
                    ));
                };
                self.expression(func, index)?;
                func.instruction(&Instruction::I32Const(inner.size() as i32));
                func.instruction(&Instruction::I32Mul);
                func.instruction(&Instruction::I32Add);
                Ok((*inner).clone())
            }

            ExprKind::FieldAccess { expr, field } => {
                let ty = self.push_address(func, expr)?;
                let Ty::Record(fields) = ty.clone() else {
                    return Err(error!(
                        field.node.span,
                        "Panic: trying to get a field of something that is not a record",
                    ));
                };
                let mut offset = 0;
                let mut field_ty= None;
                for f in &fields {
                    if f.name == field.symbol {
                        field_ty = Some(f.ty.clone());
                        break
                    }
                    offset += f.ty.size()
                }
                let Some(field_ty) = field_ty else {
                    return Err(error!(
                        field.node.span,
                        "Panic: field not found",
                    ));
                };
                func.instruction(&Instruction::I32Const(offset as i32));
                func.instruction(&Instruction::I32Add);
                Ok((*field_ty).clone())
            }

            _ => todo!(),
        }
    }

    fn expression(&mut self, func: &mut wasm_encoder::Function, expr: &Expr) -> CompilerResult<()> {
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
                    return Err(error!(
                        left.node.span,
                        "Fatal: Not type found for expression"
                    ));
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
                    (BinOpKind::Add, Ty::Float) => func.instruction(&Instruction::F64Add),

                    (BinOpKind::Sub, Ty::Int) => func.instruction(&Instruction::I32Sub),
                    (BinOpKind::Sub, Ty::Float) => func.instruction(&Instruction::F64Sub),

                    (BinOpKind::Mul, Ty::Int) => func.instruction(&Instruction::I32Mul),
                    (BinOpKind::Mul, Ty::Float) => func.instruction(&Instruction::F64Mul),

                    (BinOpKind::Div, Ty::Int) => func.instruction(&Instruction::I32DivS),
                    (BinOpKind::Div, Ty::Float) => func.instruction(&Instruction::F64Div),

                    (BinOpKind::Mod, Ty::Int) => func.instruction(&Instruction::I32RemS),

                    _ => {
                        return Err(error!(
                            operator.node.span,
                            "Operator '{:?}' is not supported for type {ty:?}", operator.kind
                        ))
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
                        return Err(error!(
                            right.node.span,
                            "Fatal: Not type found for expression",
                        ));
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
                            return Err(error!(
                                operator.node.span,
                                "Operator '{:?}' is not supported for type {ty:?}", operator.kind
                            ))
                        }
                    }
                }
            },

            ExprKind::Variable(ident) => {
                let local_var = self.symbol_table.lookup_var(ident)?;
                match local_var.address {
                    Address::Var(index) => {
                        func.instruction(&Instruction::LocalGet(index));
                    }
                    Address::Mem(addr) => {
                        func.instruction(&Instruction::I32Const(addr as i32));
                    }
                    Address::None => {}
                }
            }

            ExprKind::ArrayIndex { .. } | ExprKind::FieldAccess { ..} => {
                let inner = self.push_address(func, expr)?;
                let load_instruction = match inner {
                    Ty::Int => Instruction::I32Load(MemArg {
                        offset: 0,
                        align: 2,
                        memory_index: 0,
                    }),
                    Ty::Float => Instruction::F64Load(MemArg {
                        offset: 0,
                        align: 3,
                        memory_index: 0,
                    }),
                    Ty::Bool => Instruction::I32Load8S(MemArg {
                        offset: 0,
                        align: 0,
                        memory_index: 0,
                    }),
                    _ => return Err(error!(expr.node.span, "Unsupported type of array")),
                };
                func.instruction(&load_instruction);
            }

            ExprKind::Call { callee, args } => {
                let name = match &callee.kind {
                    ExprKind::Variable(ident) => ident,
                    _ => {
                        return Err(error!(
                            callee.node.span,
                            "First class functions are not supported",
                        ))
                    }
                };

                let signature = self.symbol_table.lookup_function(name)?;
                let arg = &args[0];
                // TODO: Hack!
                if name.symbol.as_str() == "print" {
                    return if let ExprKind::Literal(LiteralKind::String(_)) = &arg.kind {
                        self.expression(func, arg)?; // Needed to add the string value to data
                        let Some(was_str) = self.strings.get(&arg.node.id) else {
                            return Err(error!(arg.node.span, "String constant not found"));
                        };
                        func.instruction(&Instruction::I32Const(was_str.offset as i32));
                        func.instruction(&Instruction::I32Const(was_str.len as i32));
                        func.instruction(&Instruction::Call(signature.index));
                        Ok(())
                    } else {
                        Err(error!(expr.node.span, "Incorrect arguments for 'print'!"))
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

    fn import_functions(&mut self) -> CompilerResult<()> {
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
    ) -> CompilerResult<()> {
        let type_idx = self.types.len();
        let wasm_params = params
            .iter()
            .map(Ty::as_wasm)
            .collect::<CompilerResult<Vec<_>>>()?;
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

    fn encode_wasm(&mut self) -> CompilerResult<Vec<u8>> {
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

    fn compile(&mut self, module: &Module) -> CompilerResult<Vec<u8>> {
        let mut resolver = Resolver::default();
        resolver.resolve(module)?;
        self.import_functions()?;
        self.export_memory();
        self.symbol_table.resolve(module)?;
        self.type_check(module)?;
        self.module(module)?;
        self.encode_wasm()
    }
}

pub fn compile(source: &str) -> CompilerResult<Vec<u8>> {
    let module = parse(source)?;
    let mut compiler = Compiler::default();
    compiler.compile(&module)
}
