use crate::lexer::{Lexer, Token};

mod lexer;

fn main() {
    let code = "hello 1 [ ]";
    let tokens: Vec<Token> = Lexer::new(code).collect();
    for Token { kind, start, end } in tokens {
        let lexeme = &code[start..end];
        println!("[{kind:?}] \"{lexeme}\"")
    }
}
