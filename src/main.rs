use crate::interpreter::interpret;

mod interpreter;
mod lexer;
mod parser;
mod wasm;

fn main() {
    let code = "print(\"hello world\")";
    interpret(code);
}
