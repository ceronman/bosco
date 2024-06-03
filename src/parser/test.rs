use crate::ast::{Expression, Literal, Module, Statement};
use crate::lexer::Token;
use crate::parser::parse;

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
            "({})",
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

#[test]
fn test_simple_call() {
    let s = s_expr("print(\"hello\")");
    assert_eq!(s, "(module ((call print (\"hello\"))))");
}

#[test]
fn test_simple_call_with_ws() {
    let s = s_expr(
        r#"

        print("Hello world")

    "#,
    );
    assert_eq!(s, "(module ((call print (\"Hello world\"))))");
}

#[test]
fn test_let_declaration() {
    let s = s_expr(
        r#"
        let a i32 = 1
    "#,
    );
    assert_eq!(s, "(module ((let a i32 1)))");
}

#[test]
fn test_call_expression() {
    let s = s_expr(
        r#"
        let a i32 = 1
        print(a)
    "#,
    );
    println!("{s}");
    assert_eq!(s, "(module ((let a i32 1) (call print (a))))");
}

#[test]
fn test_assignment() {
    let s = s_expr(
        r#"
        let a i32 = 1
        a = 256
    "#,
    );
    println!("{s}");
    assert_eq!(s, "(module ((let a i32 1) (= a 256)))");
}

#[test]
fn test_assignment_binary_expression() {
    let s = s_expr(
        r#"
        let a i32 = 4
        let b i32 = a + 10
    "#,
    );
    println!("{s}");
    assert_eq!(s, "(module ((let a i32 4) (let b i32 (+ a 10))))");
}

#[test]
fn test_chained_binary() {
    let s = s_expr(
        r#"
        a = b + c + d
    "#,
    );
    println!("{s}");
    assert_eq!(s, "(module ((= a (+ b (+ c d)))))");
}
