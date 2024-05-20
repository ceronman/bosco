use crate::interpreter::interpret;

mod interpreter;
mod ir;
mod lexer;
mod parser;
mod wat;
mod compiler;

fn main() {
    let code = "print(\"hello world\")";
    interpret(code);
}
