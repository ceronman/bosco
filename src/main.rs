use crate::compiler::compile;
use crate::interpreter::interpret;

mod compiler;
mod interpreter;
mod lexer;
mod parser;

fn main() {
    let code = r#"
        print("Hello")
        print("from")
        print("Bosco!")
    "#;
    compile(code);
    interpret(code);
}
