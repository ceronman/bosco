use crate::lexer::Token;

#[derive(Debug)]
pub struct Module {
    pub statements: Vec<Statement>,
}

#[derive(Debug)]
pub enum Statement {
    Call {
        callee: Token,
        args: Vec<Expression>,
    },
    Declaration {
        name: Token,
        ty: Token,
        value: Expression, // TODO: Support optional values
    },
}

#[derive(Debug)]
pub enum Expression {
    Literal(Literal),
    Variable { name: Token },
}

#[derive(Debug)]
pub enum Literal {
    Number(i32),
    String { token: Token, value: String },
}
