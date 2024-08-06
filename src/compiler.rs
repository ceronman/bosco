use std::collections::HashMap;

use wasm_encoder::{
    BlockType, CodeSection, ConstExpr, DataSection, EntityType, ExportKind, ExportSection,
    FunctionSection, ImportSection, Instruction, MemArg, MemorySection, MemoryType, TypeSection,
    ValType,
};

use crate::ast;
use crate::ast::{
    BinOpKind, Expr, ExprKind, ItemKind, LiteralKind, Module, NodeId, Stmt, StmtKind, UnOpKind,
};
use crate::resolver::{resolve, DeclarationId, DeclarationKind, Resolution};
use crate::error::{error, CompilerResult};
use crate::lexer::Span;
use crate::parser::parse;
use crate::types::Type;

#[cfg(test)]
mod test;

#[derive(Clone, Copy)]
struct WasmStr {
    memory: u32,
    offset: u32,
    len: u32,
}

#[derive(Debug)]
pub enum Address {
    None,
    Var(u32),
    Mem(u32),
    Fn(u32),
}

impl Type {
    fn size(&self) -> u32 {
        match self {
            Type::Void => 0,
            Type::Int => 4,
            Type::Float => 8,
            Type::Bool => 1,
            Type::Array { inner, size } => inner.size() * size,
            Type::Record { fields } => fields.iter().map(|f| f.ty.size()).sum(),
            Type::Function { .. } => todo!(),
        }
    }

    fn as_wasm(&self) -> CompilerResult<ValType> {
        match self {
            Type::Int | Type::Bool | Type::Array { .. } | Type::Record { .. } => Ok(ValType::I32), // TODO: specify
            Type::Float => Ok(ValType::F64),
            _ => Err(error!(
                Span(0, 0),
                "{self:?} type does not have a wasm equivalent"
            )),
        }
    }
}

#[derive(Default)]
struct Compiler {
    res: Resolution,

    addresses: HashMap<DeclarationId, Address>,
    strings: HashMap<NodeId, WasmStr>,
    stack_pointer: u32,

    // TODO: Extract into an encoder struct
    type_section: TypeSection,
    function_section: FunctionSection,
    memory_section: MemorySection,
    code_section: CodeSection,
    data_section: DataSection,
    data_offset: u32,
    import_section: ImportSection,
    export_section: ExportSection,
}

impl Compiler {
    const MEM: u32 = 0;

    fn calculate_addresses(&mut self) {
        let mut fn_index = 0;
        let mut local_indices = HashMap::new();
        for decl in &self.res.declarations {
            let address = match decl.kind {
                DeclarationKind::Local(fn_id) => match decl.ty {
                    Type::Void => Address::None,
                    Type::Int | Type::Float | Type::Bool => {
                        let index = local_indices
                            .entry(fn_id)
                            .and_modify(|count| *count += 1)
                            .or_insert(0);
                        Address::Var(*index)
                    }
                    Type::Array { .. } | Type::Record { .. } | Type::Function { .. } => {
                        let pointer = self.stack_pointer;
                        self.stack_pointer += decl.ty.size();
                        Address::Mem(pointer)
                    }
                },
                DeclarationKind::Function => {
                    let a = Address::Fn(fn_index);
                    fn_index += 1;
                    a
                }
                DeclarationKind::Type => continue,
            };
            self.addresses.insert(decl.id, address);
        }
    }

    fn module(&mut self, module: &Module) -> CompilerResult<()> {
        for item in &module.items {
            if let ItemKind::Function(function) = &item.kind {
                self.function(function)?;
            }
        }
        Ok(())
    }

    fn function(&mut self, f: &ast::Function) -> CompilerResult<()> {
        let func_id = *self.res.uses.get(&f.name.node.id).unwrap();
        let func_decl = &self.res.declarations[func_id as usize];
        let Type::Function(signature) = &func_decl.ty else {
            unreachable!()
        };
        let params = signature
            .params
            .iter()
            .map(|p| p.as_wasm())
            .collect::<CompilerResult<Vec<ValType>>>()?;
        let returns: &[ValType] = if *signature.return_ty == Type::Void {
            &[]
        } else {
            &[signature.return_ty.as_wasm()?]
        };
        let type_index = self.type_section.len();
        self.type_section.function(params, returns.iter().copied());
        self.function_section.function(type_index);

        let locals = self
            .res
            .declarations
            .iter()
            .filter(|d| {
                if let DeclarationKind::Local(f) = d.kind {
                    f == func_decl.id
                } else {
                    false
                }
            })
            .map(|d| d.ty.as_wasm().map(|w| (1, w)))
            .collect::<CompilerResult<Vec<(u32, ValType)>>>()?;

        // Export
        if f.exported {
            let Some(Address::Fn(index)) = self.addresses.get(&func_decl.id) else {
                unreachable!()
            };
            self.export_section
                .export(f.name.symbol.as_str(), ExportKind::Func, *index);
        }

        let mut wasm_func = wasm_encoder::Function::new(locals);
        self.statement(&mut wasm_func, &f.body)?;
        wasm_func.instruction(&Instruction::End);
        self.code_section.function(&wasm_func);

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
                    self.expression(func, value)?; // TODO: Define what to do when declared var is used in initializer
                    let Some(decl) = self.res.uses.get(&name.node.id) else {
                        return Err(error!(name.node.span, "No mem found"));
                    };
                    let address = self.addresses.get(decl).unwrap();
                    match address {
                        Address::Var(index) => {
                            func.instruction(&Instruction::LocalSet(*index));
                        }
                        _ => todo!(),
                    }
                }
            }

            StmtKind::Assignment { target, value } => match &target.kind {
                ExprKind::Variable(name) => {
                    let decl = self.res.uses.get(&name.node.id).unwrap();
                    let address = self.addresses.get(decl).unwrap();
                    let Address::Var(index) = *address else {
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

                    let instruction = match self.res.node_types.get(&value.node.id) {
                        // TODO: support this via polymorphism
                        Some(Type::Int) => Instruction::I32Store(MemArg {
                            offset: 0,
                            align: 2,
                            memory_index: 0,
                        }),
                        Some(Type::Float) => Instruction::F64Store(MemArg {
                            offset: 0,
                            align: 3,
                            memory_index: 0,
                        }),
                        Some(Type::Bool) => Instruction::I32Store8(MemArg {
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
    ) -> CompilerResult<Type> {
        match &target.kind {
            ExprKind::Variable(name) => {
                let decl = self.res.uses.get(&name.node.id).unwrap();
                let address = self.addresses.get(&decl).unwrap();
                let Address::Mem(addr) = *address else {
                    return Err(error!(
                        name.node.span,
                        "Panic: invalid address for variable"
                    ));
                };
                func.instruction(&Instruction::I32Const(addr as i32));
                let decl_id = *self.res.uses.get(&name.node.id).expect("local not found");
                let ty = self.res.declarations[decl_id as usize].ty.clone();
                Ok(ty)
            }
            ExprKind::ArrayIndex { expr, index } => {
                let ty = self.push_address(func, expr)?;
                // TODO: Check bounds
                let Type::Array { inner, .. } = ty else {
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
                let Type::Record { fields } = ty.clone() else {
                    return Err(error!(
                        field.node.span,
                        "Panic: trying to get a field of something that is not a record",
                    ));
                };
                let mut offset = 0;
                let mut field_ty = None;
                for f in fields.iter() {
                    if f.name == field.symbol {
                        field_ty = Some(f.ty.clone());
                        break;
                    }
                    offset += f.ty.size()
                }
                let Some(field_ty) = field_ty else {
                    return Err(error!(field.node.span, "Panic: field not found",));
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
                self.data_section.active(
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

                let Some(ty) = self.res.node_types.get(&left.node.id) else {
                    return Err(error!(
                        left.node.span,
                        "Fatal: Not type found for expression"
                    ));
                };

                match (&operator.kind, ty) {
                    (BinOpKind::Eq, Type::Int) => func.instruction(&Instruction::I32Eq),
                    (BinOpKind::Eq, Type::Float) => func.instruction(&Instruction::F64Eq),

                    (BinOpKind::Ne, Type::Int) => func.instruction(&Instruction::I32Ne),
                    (BinOpKind::Ne, Type::Float) => func.instruction(&Instruction::F64Ne),

                    (BinOpKind::Gt, Type::Int) => func.instruction(&Instruction::I32GtS),
                    (BinOpKind::Gt, Type::Float) => func.instruction(&Instruction::F64Gt),

                    (BinOpKind::Ge, Type::Int) => func.instruction(&Instruction::I32GeS),
                    (BinOpKind::Ge, Type::Float) => func.instruction(&Instruction::F64Ge),

                    (BinOpKind::Lt, Type::Int) => func.instruction(&Instruction::I32LtS),
                    (BinOpKind::Lt, Type::Float) => func.instruction(&Instruction::F64Lt),

                    (BinOpKind::Le, Type::Int) => func.instruction(&Instruction::I32LeS),
                    (BinOpKind::Le, Type::Float) => func.instruction(&Instruction::F64Le),

                    (BinOpKind::Add, Type::Int) => func.instruction(&Instruction::I32Add),
                    (BinOpKind::Add, Type::Float) => func.instruction(&Instruction::F64Add),

                    (BinOpKind::Sub, Type::Int) => func.instruction(&Instruction::I32Sub),
                    (BinOpKind::Sub, Type::Float) => func.instruction(&Instruction::F64Sub),

                    (BinOpKind::Mul, Type::Int) => func.instruction(&Instruction::I32Mul),
                    (BinOpKind::Mul, Type::Float) => func.instruction(&Instruction::F64Mul),

                    (BinOpKind::Div, Type::Int) => func.instruction(&Instruction::I32DivS),
                    (BinOpKind::Div, Type::Float) => func.instruction(&Instruction::F64Div),

                    (BinOpKind::Mod, Type::Int) => func.instruction(&Instruction::I32RemS),

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
                    let Some(ty) = self.res.node_types.get(&right.node.id) else {
                        return Err(error!(
                            right.node.span,
                            "Fatal: Not type found for expression",
                        ));
                    };

                    match ty {
                        Type::Float => {
                            self.expression(func, right)?;
                            func.instruction(&Instruction::F64Neg);
                        }
                        Type::Int => {
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
                let local = self.res.uses.get(&ident.node.id).unwrap();
                let address = self.addresses.get(&local).unwrap();
                match address {
                    Address::Var(index) => {
                        func.instruction(&Instruction::LocalGet(*index));
                    }
                    _ => todo!(),
                }
            }

            ExprKind::ArrayIndex { .. } | ExprKind::FieldAccess { .. } => {
                let inner = self.push_address(func, expr)?;
                let load_instruction = match inner {
                    Type::Int => Instruction::I32Load(MemArg {
                        offset: 0,
                        align: 2,
                        memory_index: 0,
                    }),
                    Type::Float => Instruction::F64Load(MemArg {
                        offset: 0,
                        align: 3,
                        memory_index: 0,
                    }),
                    Type::Bool => Instruction::I32Load8S(MemArg {
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
                let arg = &args[0];

                let decl = self.res.uses.get(&name.node.id).unwrap();
                let addr = self.addresses.get(&decl).unwrap();
                let Address::Fn(index) = *addr else {
                    unreachable!()
                };

                // TODO: Hack!
                if name.symbol.as_str() == "print" {
                    return if let ExprKind::Literal(LiteralKind::String(_)) = &arg.kind {
                        self.expression(func, arg)?; // Needed to add the string value to data
                        let Some(was_str) = self.strings.get(&arg.node.id) else {
                            return Err(error!(arg.node.span, "String constant not found"));
                        };
                        func.instruction(&Instruction::I32Const(was_str.offset as i32));
                        func.instruction(&Instruction::I32Const(was_str.len as i32));
                        func.instruction(&Instruction::Call(index)); // FIXME!
                        Ok(())
                    } else {
                        Err(error!(expr.node.span, "Incorrect arguments for 'print'!"))
                    };
                }

                for arg in args {
                    self.expression(func, arg)?;
                }

                func.instruction(&Instruction::Call(index)); // Fixme
            }
        }
        Ok(())
    }

    fn import_functions(&mut self) -> CompilerResult<()> {
        self.import_function("js", "print", &[Type::Int, Type::Int], Type::Void)?;
        self.import_function("js", "print_int", &[Type::Int], Type::Void)?;
        self.import_function("js", "print_float", &[Type::Float], Type::Void)
    }

    fn import_function(
        &mut self,
        module: &'static str,
        name: &'static str,
        params: &[Type],
        return_ty: Type,
    ) -> CompilerResult<()> {
        let type_idx = self.type_section.len();
        let wasm_params = params
            .iter()
            .map(Type::as_wasm)
            .collect::<CompilerResult<Vec<_>>>()?;
        let returns: &[ValType] = if return_ty == Type::Void {
            &[]
        } else {
            &[return_ty.as_wasm()?]
        };
        self.type_section
            .function(wasm_params, returns.iter().copied());
        self.import_section
            .import(module, name, EntityType::Function(type_idx));
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
        self.memory_section.memory(memory);
        self.export_section.export("memory", ExportKind::Memory, 0);
    }

    fn encode_wasm(&mut self) -> CompilerResult<Vec<u8>> {
        let mut wasm_module = wasm_encoder::Module::new();
        wasm_module.section(&self.type_section);
        wasm_module.section(&self.import_section);
        wasm_module.section(&self.function_section);
        wasm_module.section(&self.memory_section);
        wasm_module.section(&self.export_section);
        wasm_module.section(&self.code_section);
        wasm_module.section(&self.data_section);
        Ok(wasm_module.finish())
    }

    fn compile(&mut self, module: &Module) -> CompilerResult<Vec<u8>> {
        self.calculate_addresses();
        self.import_functions()?;
        self.export_memory();
        self.module(module)?;
        self.encode_wasm()
    }
}

pub fn compile(source: &str) -> CompilerResult<Vec<u8>> {
    let module = parse(source)?;
    let resolution = resolve(&module)?;
    let mut compiler = Compiler {
        res: resolution,
        addresses: Default::default(),
        strings: Default::default(),
        stack_pointer: 0,
        type_section: Default::default(),
        function_section: Default::default(),
        memory_section: Default::default(),
        code_section: Default::default(),
        data_section: Default::default(),
        data_offset: 0,
        import_section: Default::default(),
        export_section: Default::default(),
    };
    compiler.compile(&module)
}
