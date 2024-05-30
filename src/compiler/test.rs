#[test]
fn hello_world_compile() {
    use crate::compiler::Compiler;
    use crate::parser::parse;
    use std::io::Write;

    let src = r#"
        let a i32 = 256
        print("Hello")
        print("from")
        print("Bosco!")
    
    "#;
    let module = parse(src).unwrap();
    let mut compiler = Compiler::new(src);
    let bytes = compiler.compile(&module);
    let mut f = std::fs::OpenOptions::new()
        .create(true)
        .write(true)
        .truncate(true)
        .open("web/hello.wasm")
        .unwrap();
    f.write_all(&bytes).unwrap();
    f.flush().unwrap();

    let wat = wasmprinter::print_bytes(bytes).unwrap();
    println!("{}", wat);
}
