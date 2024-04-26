use crate::interpreter::interpret;

mod interpreter;
mod lexer;
mod parser;

fn main() {
    let code = "print(\"hello world\")";
    interpret(code);
}
