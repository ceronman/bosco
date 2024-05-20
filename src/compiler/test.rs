use std::io::Write;
use crate::compiler::Compiler;
use crate::parser::parse;

#[test]
fn hello_world_compile() {
    let src = "print(\"Hello from Wasm Compiler!\")";
    let module = parse(src).unwrap();
    let mut compiler = Compiler::new(src);
    let bytes = compiler.compile(&module);
    let mut f = std::fs::OpenOptions::new()
        .create(true)
        .write(true)
        .truncate(true)
        .open("web/hello.wasm").unwrap();
    f.write_all(&bytes).unwrap();
    f.flush().unwrap();

    let wat = wasmprinter::print_bytes(bytes).unwrap();
    println!("{}", wat);
}