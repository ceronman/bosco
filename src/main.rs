use crate::lexer::{Lexer, Token};

mod lexer;
mod parser;

fn main() {
    let code = "hello 1 [ ]";
    let tokens: Vec<Token> = Lexer::new(code.chars()).collect();
    for Token { kind, start, end } in tokens {
        let lexeme = &code[start..end];
        println!("[{kind:?}] \"{lexeme}\"")
    }
}
