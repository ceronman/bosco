use super::{Lexer, Token, TokenKind};
use std::iter::from_fn;
use TokenKind::*;

fn test_lexer(code: &str, expected: Vec<TokenKind>, skip_ws: bool) {
    let mut lexer = Lexer::new(code);
    let tokens: Vec<Token> = from_fn(move || {
        let token = lexer.next();
        if token.kind == Eof {
            None
        } else {
            Some(token)
        }
    })
    .collect();

    let kinds: Vec<TokenKind> = tokens
        .clone()
        .into_iter()
        .map(|token| token.kind)
        .filter(|&kind| !skip_ws || kind != Whitespace)
        .collect();

    assert_eq!(kinds, expected);

    let text = tokens
        .into_iter()
        .map(|token| &code[token.start..token.end])
        .fold(String::new(), |a, b| a + b);

    assert_eq!(text.as_str(), code);
}
#[test]
fn operators() {
    test_lexer("+ -", vec![Plus, Minus], true);
}

#[test]
fn numbers() {
    test_lexer(
        "123 0 00123 123_345",
        vec![Number, Number, Number, Number],
        true,
    );
}

#[test]
fn identifiers() {
    test_lexer(
        "one one2 _ _one __one__",
        vec![Identifier, Identifier, Identifier, Identifier, Identifier],
        true,
    );
}

#[test]
fn keywords() {
    test_lexer(
        "true false _true False",
        vec![True, False, Identifier, Identifier],
        true,
    );
}

#[test]
fn braces() {
    test_lexer(
        "( [ { } ] )",
        vec![LParen, LBracket, LBrace, RBrace, RBracket, RParen],
        true,
    );
}