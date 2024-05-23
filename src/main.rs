use crate::compiler::compile;
use crate::interpreter::interpret;

mod compiler;
mod interpreter;
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
    interpret(code);
}
