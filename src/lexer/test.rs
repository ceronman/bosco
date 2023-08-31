use super::{Lexer, Token, TokenKind};
use TokenKind::*;

fn test_lexer(code: &str, expected: Vec<TokenKind>, skip_ws: bool) {
    let mut lexer = Lexer::new(code);
    let tokens: Vec<Token> = lexer.collect();

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

#[test]
fn lines() {
    test_lexer(
        "one\ntwo\nthree",
        vec![Identifier, Eol, Identifier, Eol, Identifier],
        true,
    );
}
#[test]
fn line_comment() {
    test_lexer(
        "one // this is a comment\n two",
        vec![Identifier, LineComment, Eol, Identifier],
        true,
    );
}
#[test]
fn ending_line_comment() {
    test_lexer(
        "one // this is a comment",
        vec![Identifier, LineComment],
        true,
    );
}

#[test]
fn block_comment() {
    test_lexer(
        "one /* comment */ other",
        vec![Identifier, BlockComment, Identifier],
        true,
    );
}

#[test]
fn block_comment_nested() {
    test_lexer(
        "one /* comment /* inner */ part */ other",
        vec![Identifier, BlockComment, Identifier],
        true,
    );
}

#[test]
fn block_comment_minimal() {
    test_lexer("/**/", vec![BlockComment], true);
}

#[test]
fn block_comment_unterminated() {
    test_lexer(
        "one /* comment never terminated",
        vec![Identifier, UnterminatedCommentError],
        true,
    );
}
