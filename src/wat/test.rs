#[test]
fn hello_world() {
    use crate::ir::{
        Data, Export, FunctionDefinition, Import, ImportKind, Instruction, Module, Param, Type,
    };
    use crate::wat::WatEmitter;

    let hello_world = Module {
        imports: vec![
            Import {
                module: "js".to_string(),
                name: "print".to_string(),
                kind: ImportKind::Func {
                    name: "print".to_string(),
                    params: vec![
                        Param {
                            name: "start".to_string(),
                            ty: Type::I32,
                        },
                        Param {
                            name: "len".to_string(),
                            ty: Type::I32,
                        },
                    ],
                    results: vec![],
                },
            },
            Import {
                module: "js".to_string(),
                name: "mem".to_string(),
                kind: ImportKind::Mem { id: 1 },
            },
        ],
        data: vec![Data {
            offset: 0,
            contents: "Hello from Wasm!".to_string(),
        }],
        defined_functions: vec![FunctionDefinition {
            name: "hello".to_string(),
            export: Some(Export {
                name: "hello".to_string(),
            }),
            params: vec![],
            results: vec![],
            instructions: vec![
                Instruction::I32Const(0),
                Instruction::I32Const(17),
                Instruction::Call("print".to_string()),
            ],
        }],
    };
    println!("{}", hello_world.to_wat());
}

#[test]
fn hello_world_encoder() {
    use wasm_encoder::*;

    let mut imports = ImportSection::new();
    let mut types = TypeSection::new();
    types.function(vec![ValType::I32, ValType::I32], vec![]);
    types.function(vec![], vec![]);
    imports.import("js", "print", EntityType::Function(0));
    imports.import(
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
    let mut data = DataSection::new();
    data.active(
        0,
        &ConstExpr::i32_const(0),
        "Hello from Wasm Encoder!".bytes(),
    );

    let mut functions = FunctionSection::new();
    functions.function(1);

    let mut codes = CodeSection::new();
    let mut function = Function::new(vec![]);
    function.instruction(&Instruction::I32Const(0));
    function.instruction(&Instruction::I32Const(24));
    function.instruction(&Instruction::Call(0));
    function.instruction(&Instruction::End);
    codes.function(&function);

    let mut exports = ExportSection::new();
    exports.export("hello", ExportKind::Func, 1);

    let mut module = Module::new();

    println!("{:#?}", types);
    println!("{:#?}", imports);
    println!("{:#?}", data);
    println!("{:#?}", functions);
    println!("{:#?}", codes);
    println!("{:#?}", exports);

    module.section(&types);
    module.section(&imports);
    module.section(&data);
    module.section(&functions);
    module.section(&codes);
    module.section(&exports);

    let bytes = module.finish();

    let wat = wasmprinter::print_bytes(bytes).unwrap();
    println!("{}", wat);
}
