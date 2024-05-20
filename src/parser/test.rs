use crate::lexer::Token;
use crate::parser::{Expression, Module, parse, Parser};

trait SExpr {
    fn s_expr(&self, src: &str) -> String;
}

impl SExpr for Module {
    fn s_expr(&self, src: &str) -> String {
        format!("(module {})", self.expressions.s_expr(&src))
    }
}

impl SExpr for Token {
    fn s_expr(&self, src: &str) -> String {
        src[self.start..self.end].into()
    }
}

impl SExpr for Expression {
    fn s_expr(&self, src: &str) -> String {
        match self {
            Expression::Call { callee, args } => {
                format!("(call {} {})", callee.s_expr(&src), args.s_expr(&src))
            }
            Expression::Literal { token } => token.s_expr(&src),
        }
    }
}

impl SExpr for Vec<Expression> {
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
    program.s_expr(&src)
}

#[test]
fn test_simple_call() {
    let s = s_expr("print(\"hello\")");
    assert_eq!(s, "(module ((call print (\"hello\"))))");
}
