use crate::parser::Parser;

mod lexer;
mod parser;

fn main() {
    let code = "print(\"hello\")";
    let mut parser = Parser::new(code);
    let program = parser.parse().unwrap();
    println!("{:#?}", program);
}
