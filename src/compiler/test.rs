#[test]
fn hello_world_compile() {
    use crate::compiler::Compiler;
    use crate::parser::parse;
    use std::io::Write;

    let src = r#"
        let a i32 = 1024
        print("Hello")
        print("from")
        print("Bosco!")
        print_num(256)
        print_num(a)
        a = 64
        print_num(a)
        let b i32 = a + 100
        print_num(b)
        let c i32 = 1 + 2 * 3 + 4
        print_num(c)
    "#;
    let module = parse(src).unwrap();
    println!("Module: \n {module:#?}");
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
