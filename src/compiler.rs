use std::collections::HashMap;

use crate::ast;
use crate::ast::{
    BinOpKind, Expr, ExprKind, Identifier, ItemKind, LiteralKind, Module, Node, NodeId, Stmt,
    StmtKind, UnOpKind,
};
use crate::error::{error, CompilerResult};
use crate::lexer::Span;
use crate::parser::parse;
use crate::resolver::{resolve, Declaration, DeclarationId, DeclarationKind, Resolution};
use crate::types::Type;
use wasm_encoder::{
    BlockType, CodeSection, ConstExpr, DataSection, EntityType, ExportKind, ExportSection,
    FunctionSection, GlobalSection, GlobalType, ImportSection, Instruction, MemArg, MemorySection,
    MemoryType, TypeSection, ValType,
};

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
    Stack(u32),
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

enum MemOp {
    Local(u32),
    Mem(Type),
}

#[derive(Default)]
struct Compiler {
    res: Resolution,

    addresses: HashMap<DeclarationId, Address>,
    strings: HashMap<NodeId, WasmStr>,

    // TODO: Extract into an encoder struct
    type_section: TypeSection,
    function_section: FunctionSection,
    memory_section: MemorySection,
    global_section: GlobalSection,
    code_section: CodeSection,
    data_section: DataSection,
    data_offset: u32,
    import_section: ImportSection,
    export_section: ExportSection,
}

const MEM: u32 = 0;
const PAGE_SIZE: u32 = 2u32.pow(16);
const STACK_NUM_PAGES: u32 = 16;
const STACK_SIZE: u32 = PAGE_SIZE * STACK_NUM_PAGES;

impl Compiler {
    fn calculate_addresses(&mut self) {
        let mut fn_index = 0;
        let mut local_indices = HashMap::new();
        for decl in &self.res.declarations {
            let address = match decl.kind {
                DeclarationKind::Local(fn_id) => {
                    let index = *local_indices
                        .entry(fn_id)
                        .and_modify(|count| *count += 1)
                        .or_insert(0u32);

                    match decl.ty {
                        Type::Void => Address::None,
                        Type::Int | Type::Float | Type::Bool => Address::Var(index),
                        Type::Array { .. } | Type::Record { .. } | Type::Function { .. } => {
                            Address::Stack(index)
                        }
                    }
                }
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

    fn lookup_decl(&self, ident: &Identifier) -> CompilerResult<&Declaration> {
        let decl_id =
            self.res.uses.get(&ident.node.id).copied().ok_or_else(|| {
                error!(ident.node.span, "Unknown declaration of {}", ident.symbol)
            })?;
        self.res
            .declarations
            .get(decl_id as usize)
            .ok_or_else(|| error!(ident.node.span, "Declaration does not exist"))
    }

    fn lookup_addr(&self, ident: &Identifier) -> CompilerResult<&Address> {
        let decl = self.lookup_decl(ident)?;
        self.addresses
            .get(&decl.id)
            .ok_or_else(|| error!(ident.node.span, "Unknown memory of {}", ident.symbol))
    }

    fn lookup_type(&self, node: Node) -> CompilerResult<Type> {
        self.res
            .node_types
            .get(&node.id)
            .cloned()
            .ok_or_else(|| error!(node.span, "Unknown type of node"))
    }

    fn lookup_function_locals(&self, decl_id: DeclarationId) -> impl Iterator<Item = &Declaration> {
        self.res.declarations.iter().filter(move |d| {
            if let DeclarationKind::Local(f) = d.kind {
                f == decl_id
            } else {
                false
            }
        })
    }

    fn module(&mut self, module: &Module) -> CompilerResult<()> {
        for item in module.items.iter() {
            if let ItemKind::Function(function) = &item.kind {
                self.function(function)?;
            }
        }
        Ok(())
    }

    fn function(&mut self, f: &ast::Function) -> CompilerResult<()> {
        let func_decl = self.lookup_decl(&f.name)?;
        let func_id = func_decl.id;
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

        let mut locals = Vec::new();
        let mut stack_locals = Vec::new();
        let mut stack_size = 0;
        let mut var_count = 0;
        for (i, decl) in self.lookup_function_locals(func_id).enumerate() {
            if let Address::Stack(index) = self.addresses.get(&decl.id).unwrap() {
                stack_locals.push((*index, stack_size, decl.ty.size()));
                stack_size += decl.ty.size();
            }
            if i >= params.len() {
                locals.push((1, decl.ty.as_wasm()?));
            }
            var_count += 1;
        }

        let mut stack_frame_var: u32 = 0;
        let mut stack_pointer_var: u32 = 0;
        if stack_size > 0 {
            stack_frame_var = var_count;
            locals.push((1, ValType::I32));
            var_count += 1;
            stack_pointer_var = var_count;
            locals.push((1, ValType::I32))
        }

        let mut wasm_func = wasm_encoder::Function::new(locals);

        if stack_size > 0 {
            // Create space on the stack for the function if needed
            // stack_frame = stack_pointer
            // stack_frame -= function size
            wasm_func.instruction(&Instruction::GlobalGet(0)); // TODO: assign constant or variable to stack pointer
            wasm_func.instruction(&Instruction::LocalTee(stack_frame_var));
            wasm_func.instruction(&Instruction::I32Const(stack_size as i32));
            wasm_func.instruction(&Instruction::I32Sub);
            wasm_func.instruction(&Instruction::LocalTee(stack_pointer_var));
            wasm_func.instruction(&Instruction::GlobalSet(0));

            for (var, offset, size) in stack_locals {
                if (var as usize) < params.len() {
                    wasm_func.instruction(&Instruction::LocalGet(stack_pointer_var));
                    wasm_func.instruction(&Instruction::I32Const(offset as i32));
                    wasm_func.instruction(&Instruction::I32Add); // destination
                    wasm_func.instruction(&Instruction::LocalGet(var)); // source
                    wasm_func.instruction(&Instruction::I32Const(size as i32)); // size
                    wasm_func.instruction(&Instruction::MemoryCopy {
                        src_mem: 0,
                        dst_mem: 0,
                    });

                    wasm_func.instruction(&Instruction::LocalGet(stack_pointer_var));
                    wasm_func.instruction(&Instruction::I32Const(offset as i32));
                    wasm_func.instruction(&Instruction::I32Add);
                    wasm_func.instruction(&Instruction::LocalSet(var));
                } else {
                    wasm_func.instruction(&Instruction::LocalGet(stack_pointer_var));
                    wasm_func.instruction(&Instruction::I32Const(offset as i32));
                    wasm_func.instruction(&Instruction::I32Add);
                    wasm_func.instruction(&Instruction::LocalSet(var));
                }
            }
        }

        self.statement(&mut wasm_func, &f.body)?;

        if stack_size > 0 {
            // Restore the stack frame at the end of the function if it's necessary
            // stack_frame = stack_pointer
            wasm_func.instruction(&Instruction::LocalGet(stack_frame_var));
            wasm_func.instruction(&Instruction::GlobalSet(0));
        }

        wasm_func.instruction(&Instruction::End);

        let type_index = self.type_section.len();
        self.type_section
            .function(params.iter().copied(), returns.iter().copied());
        self.function_section.function(type_index);
        self.code_section.function(&wasm_func);

        // Export
        if f.exported {
            let Address::Fn(index) = self.lookup_addr(&f.name)? else {
                unreachable!()
            };
            self.export_section
                .export(f.name.symbol.as_str(), ExportKind::Func, *index);
        }

        Ok(())
    }

    fn statement(&mut self, func: &mut wasm_encoder::Function, stmt: &Stmt) -> CompilerResult<()> {
        match &stmt.kind {
            StmtKind::Block { statements } => {
                for statement in statements.iter() {
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
                    // TODO: Define what to do when declared var is used in initializer
                    match *self.lookup_addr(name)? {
                        Address::Var(index) => {
                            self.expression(func, value)?;
                            func.instruction(&Instruction::LocalSet(index));
                        }
                        Address::Stack(index) => {
                            func.instruction(&Instruction::LocalGet(index)); // destination
                            let ty = self.lookup_decl(name)?.ty.clone();
                            self.expression(func, value)?; // source
                            func.instruction(&Instruction::I32Const(ty.size() as i32)); // size
                            func.instruction(&Instruction::MemoryCopy {
                                src_mem: 0,
                                dst_mem: 0,
                            });
                        }
                        _ => todo!(),
                    }
                }
            }

            StmtKind::Assignment { target, value } => match &target.kind {
                ExprKind::Variable(_)
                | ExprKind::ArrayIndex { .. }
                | ExprKind::FieldAccess { .. } => {
                    let mem_op = self.push_address(func, target)?; // destination
                    self.expression(func, value)?; // source

                    match mem_op {
                        MemOp::Local(index) => {
                            func.instruction(&Instruction::LocalSet(index));
                        }

                        // TODO: support this via polymorphism?
                        MemOp::Mem(Type::Int) => {
                            func.instruction(&Instruction::I32Store(MemArg {
                                offset: 0,
                                align: 2,
                                memory_index: 0,
                            }));
                        }

                        MemOp::Mem(Type::Float) => {
                            func.instruction(&Instruction::F64Store(MemArg {
                                offset: 0,
                                align: 3,
                                memory_index: 0,
                            }));
                        }

                        MemOp::Mem(Type::Bool) => {
                            func.instruction(&Instruction::I32Store8(MemArg {
                                offset: 0,
                                align: 0,
                                memory_index: 0,
                            }));
                        }

                        MemOp::Mem(ty) => {
                            func.instruction(&Instruction::I32Const(ty.size() as i32)); // size
                            func.instruction(&Instruction::MemoryCopy {
                                src_mem: 0,
                                dst_mem: 0,
                            });
                        }
                    };
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
                self.expression(func, expr)?;
                func.instruction(&Instruction::Return);
            }
        }
        Ok(())
    }

    fn push_address(
        &mut self,
        func: &mut wasm_encoder::Function,
        target: &Expr,
    ) -> CompilerResult<MemOp> {
        match &target.kind {
            ExprKind::Variable(name) => match *self.lookup_addr(name)? {
                Address::Var(index) => Ok(MemOp::Local(index)),
                Address::Stack(index) => {
                    func.instruction(&Instruction::LocalGet(index));
                    self.lookup_type(name.node).map(MemOp::Mem)
                }
                _ => todo!(),
            },
            ExprKind::ArrayIndex { expr, index } => {
                let ty = self.push_address(func, expr)?;
                // TODO: Check bounds
                let MemOp::Mem(Type::Array { inner, .. }) = ty else {
                    return Err(error!(
                        expr.node.span,
                        "Panic: trying to index something that is not an array",
                    ));
                };
                self.expression(func, index)?;
                func.instruction(&Instruction::I32Const(inner.size() as i32));
                func.instruction(&Instruction::I32Mul);
                func.instruction(&Instruction::I32Add);
                Ok(MemOp::Mem((*inner).clone()))
            }

            ExprKind::FieldAccess { expr, field } => {
                let ty = self.push_address(func, expr)?;
                let MemOp::Mem(Type::Record { fields }) = ty else {
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
                Ok(MemOp::Mem((*field_ty).clone()))
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
                    memory: MEM,
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

                let ty = self.lookup_type(left.node)?;

                match (&operator.kind, &ty) {
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
                        // TODO: Remove all uses of :? in error formatting
                        return Err(error!(
                            operator.node.span,
                            "Operator '{:?}' is not supported for type {ty:?}", operator.kind
                        ));
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
                    let ty = self.lookup_type(right.node)?;
                    match &ty {
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

            ExprKind::Variable(_) | ExprKind::ArrayIndex { .. } | ExprKind::FieldAccess { .. } => {
                match self.push_address(func, expr)? {
                    MemOp::Mem(Type::Int) => {
                        func.instruction(&Instruction::I32Load(MemArg {
                            offset: 0,
                            align: 2,
                            memory_index: 0,
                        }));
                    }
                    MemOp::Mem(Type::Float) => {
                        func.instruction(&Instruction::F64Load(MemArg {
                            offset: 0,
                            align: 3,
                            memory_index: 0,
                        }));
                    }
                    MemOp::Mem(Type::Bool) => {
                        func.instruction(&Instruction::I32Load8S(MemArg {
                            offset: 0,
                            align: 0,
                            memory_index: 0,
                        }));
                    }
                    MemOp::Local(index) => {
                        func.instruction(&Instruction::LocalGet(index));
                    }
                    _ => {}
                };
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

                let Address::Fn(index) = *self.lookup_addr(name)? else {
                    // TODO: remove all unreachables?
                    unreachable!()
                };

                // TODO: Hack!
                if name.symbol.as_str() == "print" {
                    let arg = &args[0];
                    return if let ExprKind::Literal(LiteralKind::String(_)) = &arg.kind {
                        self.expression(func, arg)?; // Needed to add the string value to data
                        let Some(was_str) = self.strings.get(&arg.node.id) else {
                            return Err(error!(arg.node.span, "String constant not found"));
                        };
                        func.instruction(&Instruction::I32Const(was_str.offset as i32));
                        func.instruction(&Instruction::I32Const(was_str.len as i32));
                        func.instruction(&Instruction::Call(index));
                        Ok(())
                    } else {
                        Err(error!(expr.node.span, "Incorrect arguments for 'print'!"))
                    };
                }

                for arg in args.iter() {
                    self.expression(func, arg)?;
                }

                func.instruction(&Instruction::Call(index));
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
            minimum: STACK_NUM_PAGES as u64,
            maximum: None,
            memory64: false,
            shared: false,
            page_size_log2: None,
        };
        self.memory_section.memory(memory);
        self.export_section.export("memory", ExportKind::Memory, 0);
    }

    fn globals(&mut self) {
        self.global_section.global(
            GlobalType {
                val_type: ValType::I32,
                mutable: true,
                shared: false,
            },
            &ConstExpr::i32_const(STACK_SIZE as i32 - 1),
        );
    }

    fn encode_wasm(&mut self) -> CompilerResult<Vec<u8>> {
        let mut wasm_module = wasm_encoder::Module::new();
        wasm_module.section(&self.type_section);
        wasm_module.section(&self.import_section);
        wasm_module.section(&self.function_section);
        wasm_module.section(&self.memory_section);
        wasm_module.section(&self.global_section);
        wasm_module.section(&self.export_section);
        wasm_module.section(&self.code_section);
        wasm_module.section(&self.data_section);
        Ok(wasm_module.finish())
    }

    fn compile(&mut self, module: &Module) -> CompilerResult<Vec<u8>> {
        self.calculate_addresses();
        self.import_functions()?;
        self.export_memory();
        self.globals();
        self.module(module)?;
        self.encode_wasm()
    }
}

pub fn compile(source: &str) -> CompilerResult<Vec<u8>> {
    let module = parse(source)?;
    let resolution = resolve(&module)?;
    let mut compiler = Compiler {
        res: resolution,
        ..Default::default()
    };
    compiler.compile(&module)
}
