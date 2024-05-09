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
