use crate::lexer::Token;

#[derive(Debug)]
pub struct Module {
    pub statement: Statement,
}

#[derive(Debug)]
pub enum Statement {
    Block {
        statements: Vec<Statement>,
    },
    Call {
        callee: Token,
        args: Vec<Expression>,
    },
    Declaration {
        name: Token,
        ty: Token,
        value: Expression, // TODO: Support optional values
    },
    Assignment {
        name: Token,
        value: Expression,
    },
    If {
        condition: Expression,
        then_block: Box<Statement>,
        else_block: Option<Box<Statement>>,
    },
    While {
        condition: Expression,
        body: Box<Statement>,
    },
}

#[derive(Debug)]
pub enum Expression {
    Literal(Literal),
    Variable {
        name: Token,
    },
    Binary {
        left: Box<Expression>,
        right: Box<Expression>,
        operator: Token,
    },
    Or {
        left: Box<Expression>,
        right: Box<Expression>,
    },
    And {
        left: Box<Expression>,
        right: Box<Expression>,
    },
    Not {
        right: Box<Expression>,
    },
}

#[derive(Debug)]
pub enum Literal {
    Number(i32),
    String { token: Token, value: String },
}
