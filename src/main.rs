use crate::compiler::compile;

mod ast;
mod compiler;
mod error;
mod lexer;
mod parser;
mod resolver;
mod types;

fn main() {
    let code = r#"
        1
        print("Hello")
        print("from")
        print("Bosco!")
    "#;
    if let Err(error) = compile(code) {
        eprintln!(
            "Compile error:\n{error} at {:?}\n{:?}",
            error.span, error.backtrace
        );
        std::process::exit(1);
    }
}
