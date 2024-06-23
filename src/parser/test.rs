use crate::ast::{Expr, ExprKind, Item, ItemKind, LiteralKind, Module, Param, Stmt, StmtKind};
use crate::lexer::Token;
use crate::parser::parse;
use std::fmt::{Debug, Formatter};
use std::str::Chars;

trait SExpr {
    fn s_expr(&self, src: &str) -> String;
}

impl SExpr for Module {
    fn s_expr(&self, src: &str) -> String {
        format!("(module {})", self.items.s_expr(src))
    }
}

impl SExpr for Token {
    fn s_expr(&self, src: &str) -> String {
        self.span.as_str(src).into()
    }
}

impl SExpr for Item {
    fn s_expr(&self, src: &str) -> String {
        match &self.kind {
            ItemKind::Function {
                name,
                return_ty,
                params,
                body,
            } => {
                format!(
                    "(fn {} {} (ret {}) {})",
                    name.s_expr(src),
                    params.s_expr(src),
                    return_ty.s_expr(src),
                    body.s_expr(src)
                )
            }
        }
    }
}

impl SExpr for Param {
    fn s_expr(&self, src: &str) -> String {
        format!("(param {} {})", self.name.s_expr(src), self.ty.s_expr(src))
    }
}

impl SExpr for Stmt {
    fn s_expr(&self, src: &str) -> String {
        match &self.kind {
            StmtKind::Block { statements } => {
                format!("({})", statements.s_expr(src))
            }
            StmtKind::Call { callee, args } => {
                format!("(call {} {})", callee.s_expr(src), args.s_expr(src))
            }
            StmtKind::Declaration { name, ty, value } => format!(
                "(let {} {} {})",
                name.s_expr(src),
                ty.s_expr(&src),
                value.s_expr(src)
            ),
            StmtKind::Assignment { name, value } => {
                format!("(= {} {})", name.s_expr(src), value.s_expr(src))
            }

            StmtKind::If {
                condition,
                then_block,
                else_block,
            } => {
                format!(
                    "(if {} {} {})",
                    condition.s_expr(src),
                    then_block.s_expr(src),
                    else_block.s_expr(src)
                )
            }

            StmtKind::While { condition, body } => {
                format!("(while {} ({}))", condition.s_expr(src), body.s_expr(src))
            }
        }
    }
}

impl SExpr for Expr {
    fn s_expr(&self, src: &str) -> String {
        match &self.kind {
            ExprKind::Literal(literal) => literal.s_expr(src),
            ExprKind::Variable { name } => format!("{}", name.s_expr(src)),
            ExprKind::Binary {
                left,
                right,
                operator,
            } => format!(
                "({} {} {})",
                operator.s_expr(src),
                left.s_expr(src),
                right.s_expr(src)
            ),
            ExprKind::Or { left, right } => {
                format!("(or {} {})", left.s_expr(src), right.s_expr(src))
            }
            ExprKind::And { left, right } => {
                format!("(and {} {})", left.s_expr(src), right.s_expr(src))
            }
            ExprKind::Not { right } => format!("(not {})", right.s_expr(src)),
        }
    }
}

impl SExpr for LiteralKind {
    fn s_expr(&self, _src: &str) -> String {
        match self {
            LiteralKind::Int(value) => format!("{value}"),
            LiteralKind::Float(value) => format!("{value}"),
            LiteralKind::String { value, .. } => format!("\"{value}\""),
            LiteralKind::Bool(value) => {
                if *value {
                    format!("true")
                } else {
                    format!("false")
                }
            }
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

impl<T: SExpr> SExpr for Option<Box<T>> {
    fn s_expr(&self, src: &str) -> String {
        match self {
            None => "".to_string(),
            Some(e) => e.s_expr(&src),
        }
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
                while let Some(c) = expr.clone().next() {
                    if c.is_whitespace() {
                        expr.next();
                    } else {
                        break;
                    }
                }
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

macro_rules! test_main {
    ($code:expr , $($t:tt)*) => {
        let code = &format!("fn main() int {{ {} }}", $code);
        test_parser!(
            code,
            (module
                (fn main (ret int)
                    (
                        $($t)*
                    )
                )
            )
        )
    }
}

#[test]
fn test_hello_world() {
    test_parser! {
        r#"
            fn main() int {
                print("Hello world!")
            }
        "#,
        (module
            (fn main (ret int)
                (
                    (call print "Hello world!")
                )
            )
        )
    }
}

#[test]
fn test_simple_call() {
    test_main! {
        "print(\"hello\")",
        (call print "hello")
    }
}

#[test]
fn test_literals() {
    test_main! {
        r#"
            a = 1
            b = 2.5
            c = true
            d = false
        "#,
        (= a 1)
        (= b 2.5)
        (= c true)
        (= d false)
    }
}

#[test]
fn test_simple_call_with_ws() {
    test_main! {
        r#"
            print("Hello world")
        "#,
        (call print "Hello world")
    }
}

#[test]
fn test_let_declaration() {
    test_main! {
        "let a int = 1",
        (let a int 1)
    }
}

#[test]
fn test_call_expression() {
    test_main! {
        r#"
            let a int = 1
            print(a)
        "#,
        (let a int 1)
        (call print a)
    }
}

#[test]
fn test_assignment() {
    test_main! {
        r#"
            let a int = 1
            a = 256
        "#,
        (let a int 1)
        (= a 256)
    }
}

#[test]
fn test_assignment_binary_expression() {
    test_main! {
        r#"
            let a int = 4
            let b int = a + 10
        "#,
        (let a int 4)
        (let b int (+ a 10))
    }
}

#[test]
fn test_associativity() {
    test_main! {
        "x = a + b + c",
        (= x (+ (+ a b) c))
    }
}

#[test]
fn test_precedence() {
    test_main! {
        "x = a + b * c + d",
        (= x (+ (+ a (* b c)) d))
    }
}

#[test]
fn test_grouping() {
    test_main! {
        "x = (a + b) * (c + d)",
        (= x (* (+ a b) (+ c d)))
    }
}

#[test]
fn test_if_statement() {
    test_main! {
        r#"
            if 1 + 1 {
                let a int = 1
                print("true")
            } else {
                print("false")
            }
        "#,
        (if (+ 1 1)
            ((let a int 1) (call print "true"))
            ((call print "false"))
        )
    }
}

#[test]
fn test_conditionals() {
    test_main! {
        r#"
            if a > 2 and b < c or 1 >= x and z == 1 {
                print("true")
            }
        "#,
        (if (or (and (> a 2) (< b c)) (and (>= 1 x) (== z 1)))
            ((call print "true"))
        )
    }
}

#[test]
fn test_block() {
    test_main! {
        r#"
            {
                print("hello")
            }
        "#,
        (
            (call print "hello")
        )
    }
}
