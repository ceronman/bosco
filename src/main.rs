use crate::compiler::compile;

mod ast;
mod compiler;
mod error;
mod lexer;
mod parser;
mod types;
mod resolver;

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
