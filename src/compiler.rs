mod test;

use std::collections::HashMap;

use wasm_encoder::{
    CodeSection, ConstExpr, DataSection, EntityType, ExportKind, ExportSection, Function,
    FunctionSection, ImportSection, Instruction, MemoryType, TypeSection, ValType,
};

use crate::lexer::Token;
use crate::parser;
use crate::parser::{parse, Expression, ParseError};

#[derive(Clone, Copy)]
struct WasmStr {
    memory: u32,
    offset: u32,
    len: u32,
}

struct Compiler<'src> {
    source: &'src str,
    strings: HashMap<Token, WasmStr>,
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
            fn_indices: Default::default(),
            types: Default::default(),
            functions: Default::default(),
            codes: Default::default(),
            data: Default::default(),
            data_offset: 0,
            imports: Default::default(),
            exports: Default::default(),
        }
    }

    fn fill_strings(&mut self, module: &parser::Module) {
        for expr in &module.expressions {
            if let Expression::Call { args, .. } = expr {
                for expr in args {
                    if let Expression::Literal { token } = expr {
                        let value = &self.source[token.start + 1..token.end - 1];
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
            }
        }
    }

    fn main(&mut self, module: &parser::Module) {
        let type_index = self.types.len();
        self.types.function(vec![], vec![]);
        let main_fn_index = 1;
        self.functions.function(type_index);
        let mut main_function = Function::new(vec![]);
        let print_fn = *self.fn_indices.get("print").expect("No print available");
        for expr in &module.expressions {
            if let Expression::Call { args, .. } = expr {
                for arg in args {
                    if let Expression::Literal { token } = arg {
                        let Some(was_str) = self.strings.get(token) else {
                            continue;
                        };
                        main_function.instruction(&Instruction::I32Const(was_str.offset as i32));
                        main_function.instruction(&Instruction::I32Const(was_str.len as i32));
                        main_function.instruction(&Instruction::Call(print_fn));
                    }
                }
            }
        }
        main_function.instruction(&Instruction::End);
        self.codes.function(&main_function);
        self.exports
            .export("hello", ExportKind::Func, main_fn_index);
    }

    fn compile(&mut self, module: &parser::Module) -> Vec<u8> {
        let print_idx = self.import_function("js", "print", &[ValType::I32, ValType::I32], &[]);
        self.fn_indices.insert("print", print_idx);
        self.import_memory();
        self.fill_strings(module);
        self.main(module);

        let mut wasm_module = wasm_encoder::Module::new();

        wasm_module.section(&self.types);
        wasm_module.section(&self.imports);
        wasm_module.section(&self.functions);
        wasm_module.section(&self.exports);
        wasm_module.section(&self.codes);
        wasm_module.section(&self.data);

        wasm_module.finish()
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

pub fn compile(source: &str) -> Result<Vec<u8>, ParseError> {
    let module = parse(source)?;
    let mut compiler = Compiler::new(source);
    Ok(compiler.compile(&module))
}
