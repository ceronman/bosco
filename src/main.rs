use crate::parser::Parser;

mod lexer;
mod parser;

fn main() {
    let code = "\"hello world\"\"world\"";
    let mut parser = Parser::new(code);
    let program = parser.parse();
    println!("{:#?}", program);
}
