mod test;

use std::collections::HashMap;

use wasm_encoder::{CodeSection, ConstExpr, DataSection, EntityType, ExportKind, ExportSection, Function, FunctionSection, ImportSection, Instruction, MemoryType, TypeSection, ValType};

use crate::lexer::Token;
use crate::parser;
use crate::parser::Expression;

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
    imports: ImportSection,
    exports: ExportSection,
}

impl<'src> Compiler<'src> {
    fn new(source: &'src str) -> Self {
        Compiler {
            source,
            strings: Default::default(),
            fn_indices: Default::default(),
            types: Default::default(),
            functions: Default::default(),
            codes: Default::default(),
            data: Default::default(),
            imports: Default::default(),
            exports: Default::default(),
        }
    }

    fn fill_strings(&mut self, module: &parser::Module) {
        const MEM: u32 = 0;
        for expr in &module.expressions {
            match expr {
                Expression::Call { args, .. } => {
                    for expr in args {
                        match expr {
                            Expression::Literal { token } => {
                                let value = &self.source[token.start+1..token.end-1];
                                let wasm_str = WasmStr {
                                    memory: MEM,
                                    offset: self.data.len(),
                                    len: value.len() as u32,
                                };

                                self.strings.insert(*token, wasm_str);
                                self.data.active(
                                    MEM,
                                    &ConstExpr::i32_const(wasm_str.offset as i32), // TODO: i32?
                                    value.bytes(),
                                );
                            },
                            _ => {}
                        }
                    }
                }
                _ => {}
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
            match expr {
                Expression::Call { args, .. } => {
                    for expr in args {
                        match expr {
                            Expression::Literal { token } => {
                                let Some(was_str) = self.strings.get(token)
                                    else { continue };
                                main_function.instruction(&Instruction::I32Const(was_str.offset as i32));
                                main_function.instruction(&Instruction::I32Const(was_str.len as i32));
                                main_function.instruction(&Instruction::Call(print_fn));
                            },
                            _ => {}
                        }
                    }
                }
                _ => {}
            }
        }
        main_function.instruction(&Instruction::End);
        self.codes.function(&main_function);
        self.exports.export("hello", ExportKind::Func, main_fn_index);
    }

    fn compile(&mut self, module: &parser::Module) -> Vec<u8> {
        let print_idx = self.import_function("js", "print", &[ValType::I32, ValType::I32], &[]);
        self.fn_indices.insert("print", print_idx);
        self.import_memory();
        self.fill_strings(module);
        self.main(module);

        let mut wasm_module = wasm_encoder::Module::new();

        println!("{:#?}", self.types);
        println!("{:#?}", self.imports);
        println!("{:#?}", self.data);
        println!("{:#?}", self.functions);
        println!("{:#?}", self.codes);
        println!("{:#?}", self.exports);

        wasm_module.section(&self.types);
        wasm_module.section(&self.imports);
        wasm_module.section(&self.functions);
        wasm_module.section(&self.exports);
        wasm_module.section(&self.codes);
        wasm_module.section(&self.data);

        wasm_module.finish()
    }

    fn import_function(&mut self, module: &str, name: &str, params: &[ValType], results: &[ValType]) -> u32 {
        let type_idx = self.types.len();
        // TODO: Figure this out without having to create vectors!
        let p = params.iter().map(|v| *v).collect::<Vec<ValType>>();
        let r = results.iter().map(|v| *v).collect::<Vec<ValType>>();
        self.types.function(p, r);
        let import_idx = self.imports.len();
        self.imports.import(module, name, EntityType::Function(type_idx));
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