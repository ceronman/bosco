use super::{Lexer, TokenKind};
use TokenKind::*;

fn test_lexer(code: &str, expected: Vec<TokenKind>, skip_ws: bool) {
    let mut lexer = Lexer::new(code);
    let mut tokens = Vec::new();
    loop {
        let token = lexer.next_token();
        if token.kind == Eof {
            break;
        }
        tokens.push(token);
    }

    let kinds: Vec<TokenKind> = tokens
        .clone()
        .into_iter()
        .map(|token| token.kind)
        .filter(|&kind| !skip_ws || kind != Whitespace)
        .collect();

    assert_eq!(kinds, expected);

    let text = tokens
        .into_iter()
        .map(|token| token.span.as_str(code))
        .fold(String::new(), |a, b| a + b);

    assert_eq!(text.as_str(), code);
}
#[test]
fn operators() {
    test_lexer("+ - / * %", vec![Plus, Minus, Slash, Star, Percent], true);
}

#[test]
fn numbers() {
    test_lexer(
        "123 0 00123 1.1 123.456 1.",
        vec![Int, Int, Int, Float, Float, Float],
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
fn book_keywords() {
    test_lexer(
        "true false _true False",
        vec![True, False, Identifier, Identifier],
        true,
    );
}

#[test]
fn fn_keyword() {
    test_lexer(
        "fn foo() {}",
        vec![Fn, Identifier, LParen, RParen, LBrace, RBrace],
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

#[test]
fn let_declaration() {
    test_lexer(r#" let foo = 1"#, vec![Let, Identifier, Equal, Int], true);
}

#[test]
fn collapsed_eol() {
    test_lexer(
        r#"
            a


            b


            c
        "#,
        vec![Eol, Identifier, Eol, Identifier, Eol, Identifier, Eol],
        true,
    );
}

#[test]
fn arithmetic_expressions() {
    test_lexer(
        r#"
            let a = 1
            let b = 2
            let c = 3
            let x = (a + b) - (a + c)
        "#,
        vec![
            Eol, Let, Identifier, Equal, Int, Eol, Let, Identifier, Equal, Int, Eol, Let,
            Identifier, Equal, Int, Eol, Let, Identifier, Equal, LParen, Identifier, Plus,
            Identifier, RParen, Minus, LParen, Identifier, Plus, Identifier, RParen, Eol,
        ],
        true,
    );
}

#[test]
fn boolean_expressions() {
    test_lexer(
        r#"
            a > b
            c < d
            x >= y
            z <= z
            a == b
            b != c
            x or y
            a and b
            not z
        "#,
        vec![
            Eol,
            Identifier,
            Greater,
            Identifier,
            Eol,
            Identifier,
            Less,
            Identifier,
            Eol,
            Identifier,
            GreaterEqual,
            Identifier,
            Eol,
            Identifier,
            LessEqual,
            Identifier,
            Eol,
            Identifier,
            EqualEqual,
            Identifier,
            Eol,
            Identifier,
            BangEqual,
            Identifier,
            Eol,
            Identifier,
            Or,
            Identifier,
            Eol,
            Identifier,
            And,
            Identifier,
            Eol,
            Not,
            Identifier,
            Eol,
        ],
        true,
    );
}

#[test]
fn strings() {
    test_lexer(
        r#" ("foo" ident "bar")  "#,
        vec![LParen, Str, Identifier, Str, RParen],
        true,
    );
}

#[test]
fn strings_together() {
    test_lexer(
        r#" "foo""bar"  "#,
        vec![Whitespace, Str, Str, Whitespace],
        false,
    );
}

#[test]
fn args() {
    test_lexer(
        "foo(1, two, 3.0)",
        vec![
            Identifier, LParen, Int, Comma, Identifier, Comma, Float, RParen,
        ],
        true,
    );
}

#[test]
fn control_flow() {
    test_lexer(r#"if else while"#, vec![If, Else, While], true);
}
