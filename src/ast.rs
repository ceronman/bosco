use crate::lexer::{Span, Token};

pub type NodeId = u32;

#[derive(Copy, Clone, Debug)]
pub struct Node {
    pub id: NodeId,
    pub span: Span,
}

#[derive(Debug)]
pub struct Module {
    pub node: Node,
    pub items: Vec<Item>,
}

#[derive(Debug)]
pub struct Item {
    pub node: Node,
    pub kind: ItemKind,
}

#[derive(Debug)]
pub enum ItemKind {
    Function {
        name: Token,
        return_ty: Option<Token>,
        params: Vec<Param>,
        body: Stmt,
    },
}

#[derive(Debug)]
pub struct Param {
    pub node: Node,
    pub name: Token,
    pub ty: Token,
}

#[derive(Debug)]
pub struct Stmt {
    pub node: Node,
    pub kind: StmtKind,
}

#[derive(Debug)]
pub enum StmtKind {
    Block {
        statements: Vec<Stmt>,
    },
    Call {
        callee: Token,
        args: Vec<Expr>,
    },
    Declaration {
        name: Token,
        ty: Token,
        value: Option<Expr>,
    },
    Assignment {
        name: Token,
        value: Expr,
    },
    If {
        condition: Expr,
        then_block: Box<Stmt>,
        else_block: Option<Box<Stmt>>,
    },
    While {
        condition: Expr,
        body: Box<Stmt>,
    },
}

#[derive(Debug)]
pub struct Expr {
    pub node: Node,
    pub kind: ExprKind,
}

#[derive(Debug)]
pub enum ExprKind {
    Literal(LiteralKind),
    Variable {
        name: Token,
    },
    Binary {
        left: Box<Expr>,
        right: Box<Expr>,
        operator: Token,
    },
    Or {
        left: Box<Expr>,
        right: Box<Expr>,
    },
    And {
        left: Box<Expr>,
        right: Box<Expr>,
    },
    Not {
        right: Box<Expr>,
    },
}

#[derive(Debug)]
pub enum LiteralKind {
    Int(i32),
    Float(f64),
    Bool(bool),
    String { token: Token, value: String },
}
