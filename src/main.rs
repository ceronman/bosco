use crate::compiler::compile;

mod compiler;
mod lexer;
mod parser;

fn main() {
    let code = r#"
        1
        print("Hello")
        print("from")
        print("Bosco!")
    "#;
    if let Err(error) = compile(code) {
        eprintln!("Compile error:\n{error}");
        std::process::exit(1);
    }
}
