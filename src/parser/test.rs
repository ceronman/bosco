use crate::ast::{Expression, Literal, Module, Statement};
use crate::lexer::Token;
use crate::parser::parse;
use std::fmt::{Debug, Formatter};
use std::str::Chars;

trait SExpr {
    fn s_expr(&self, src: &str) -> String;
}

impl SExpr for Module {
    fn s_expr(&self, src: &str) -> String {
        format!("(module {})", self.statements.s_expr(src))
    }
}

impl SExpr for Token {
    fn s_expr(&self, src: &str) -> String {
        src[self.start..self.end].into()
    }
}

impl SExpr for Statement {
    fn s_expr(&self, src: &str) -> String {
        match self {
            Statement::Call { callee, args } => {
                format!("(call {} {})", callee.s_expr(src), args.s_expr(src))
            }
            Statement::Declaration { name, ty, value } => format!(
                "(let {} {} {})",
                name.s_expr(src),
                ty.s_expr(&src),
                value.s_expr(src)
            ),
            Statement::Assignment { name, value } => {
                format!("(= {} {})", name.s_expr(src), value.s_expr(src))
            }

            Statement::If {
                condition,
                then_block,
                else_block,
            } => {
                format!(
                    "(if {} ({}) ({}))",
                    condition.s_expr(src),
                    then_block.s_expr(src),
                    else_block.s_expr(src)
                )
            }
        }
    }
}

impl SExpr for Expression {
    fn s_expr(&self, src: &str) -> String {
        match self {
            Expression::Literal(literal) => literal.s_expr(src),
            Expression::Variable { name } => format!("{}", name.s_expr(src)),
            Expression::Binary {
                left,
                right,
                operator,
            } => format!(
                "({} {} {})",
                operator.s_expr(src),
                left.s_expr(src),
                right.s_expr(src)
            ),
        }
    }
}

impl SExpr for Literal {
    fn s_expr(&self, _src: &str) -> String {
        match self {
            Literal::Number(value) => format!("{value}"),
            Literal::String { value, .. } => format!("\"{value}\""),
        }
    }
}

impl<T: SExpr> SExpr for Vec<T> {
    fn s_expr(&self, src: &str) -> String {
        format!(
            "{}",
            self.iter()
                .map(|e| e.s_expr(src))
                .collect::<Vec<String>>()
                .join(" ")
        )
    }
}

fn s_expr(src: &str) -> String {
    let program = parse(src).unwrap();
    program.s_expr(src)
}

#[derive(Eq, PartialEq)]
enum SExpression {
    Symbol(String),
    Expr(Vec<SExpression>),
}

impl Debug for SExpression {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            SExpression::Symbol(s) => write!(f, "{s}"),
            SExpression::Expr(expressions) => {
                write!(f, "(")?;
                for (i, e) in expressions.iter().enumerate() {
                    write!(f, "{e:?}")?;
                    if i < expressions.len() - 1 {
                        write!(f, " ")?;
                    }
                }
                write!(f, ")")
            }
        }
    }
}

fn parse_sexpr(code: &str) -> SExpression {
    parse_chars(&mut code.chars())
}

fn parse_chars(expr: &mut Chars<'_>) -> SExpression {
    match expr.skip_while(|c| c.is_whitespace()).next() {
        Some('(') => {
            let mut elements = Vec::new();
            loop {
                if let Some(')') = expr.clone().next() {
                    break;
                }
                let e = parse_chars(expr);
                elements.push(e);
            }
            match expr.next() {
                Some(')') => (),
                _ => panic!("Missing closing s-expression"),
            }
            SExpression::Expr(elements)
        }
        Some(char) => {
            let mut symbol = String::new();
            symbol.push(char);
            loop {
                match expr.clone().next() {
                    None => break,
                    Some(')') | Some('(') => break,
                    Some(c) if c.is_whitespace() => break,
                    Some(c) => {
                        symbol.push(c);
                        expr.next();
                    }
                }
            }
            SExpression::Symbol(symbol)
        }
        None => panic!("Unexpected end of input in sexpr"),
    }
}

macro_rules! test_parser {
    ($code:expr , $($t:tt)*) => {
        let actual = s_expr($code);
        let actual = parse_sexpr(&actual);
        let expected = stringify!($($t)*);
        let expected = parse_sexpr(expected);
        assert_eq!(expected, actual);
    }
}

#[test]
fn test_simple_call() {
    test_parser! {
        "print(\"hello\")",
        (module (call print "hello"))
    }
}

#[test]
fn test_simple_call_with_ws() {
    test_parser! {
        r#"
            print("Hello world")
        "#,
        (module (call print "Hello world"))
    }
}

#[test]
fn test_let_declaration() {
    test_parser! {
        "let a i32 = 1",
        (module (let a i32 1))
    }
}

#[test]
fn test_call_expression() {
    test_parser! {
        r#"
            let a i32 = 1
            print(a)
        "#,
        (module (let a i32 1) (call print a))
    }
}

#[test]
fn test_assignment() {
    test_parser! {
        r#"
            let a i32 = 1
            a = 256
        "#,
        (module (let a i32 1) (= a 256))
    }
}

#[test]
fn test_assignment_binary_expression() {
    test_parser! {
        r#"
            let a i32 = 4
            let b i32 = a + 10
        "#,
        (module
            (let a i32 4)
            (let b i32 (+ a 10)))
    }
}

#[test]
fn test_associativity() {
    test_parser! {
        "x = a + b + c",
        (module
            (= x (+ (+ a b) c))
        )
    }
}

#[test]
fn test_precedence() {
    test_parser! {
        "x = a + b * c + d",
        (module
            (= x (+ (+ a (* b c)) d))
        )
    }
}

#[test]
fn test_grouping() {
    test_parser! {
        "x = (a + b) * (c + d)",
        (module
            (= x (* (+ a b) (+ c d)))
        )
    }
}

#[test]
fn test_if_statement() {
    test_parser! {
        r#"
            if 1 + 1 {
                let a i32 = 1
                print("true")
            } else {
                print("false")
            }
        "#,
        (module
            (if (+ 1 1)
                ((let a i32 1) (call print "true"))
                ((call print "false"))
            )
        )
    }
}

#[test]
fn test_conditionals() {
    test_parser! {
        r#"
            if a > 2 and b < c or 1 >= x and z == 1 {
                print("true")
            }
        "#,
        (module
            (if (or (and (> a 2) (< b c)) (and (>= 1 x) (== z 1)))
                ((call print "true"))
                ()
            )
        )
    }
}
