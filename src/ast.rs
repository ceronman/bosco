use std::fmt::{Display, Formatter};

use crate::lexer::Span;

pub type NodeId = u32;

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct Symbol(String);

impl Symbol {
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl Display for Symbol {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}

impl From<&str> for Symbol {
    fn from(value: &str) -> Self {
        Symbol(value.to_owned())
    }
}

#[derive(Copy, Clone, Debug)]
pub struct Node {
    pub id: NodeId,
    pub span: Span,
}

#[derive(Debug)]
pub struct Module {
    pub _node: Node,
    pub items: Vec<Item>,
}

#[derive(Debug)]
pub struct Item {
    pub node: Node,
    pub kind: ItemKind,
}

#[derive(Debug)]
pub enum ItemKind {
    Function(Function),
    Record(Record),
}

#[derive(Debug)]
pub struct Function {
    pub exported: bool,
    pub name: Identifier,
    pub return_ty: Option<Type>,
    pub params: Vec<Param>,
    pub body: Stmt,
}

#[derive(Debug)]
pub struct Record {
    pub name: Identifier,
    pub fields: Vec<Field>,
}

#[derive(Debug)]
pub struct Field {
    pub name: Identifier,
    pub ty: Type,
}

#[derive(Debug)]
pub struct Param {
    pub name: Identifier,
    pub ty: Type,
}

#[derive(Debug)]
pub struct Stmt {
    pub node: Node,
    pub kind: StmtKind,
}

#[derive(Debug)]
pub enum StmtKind {
    ExprStmt(Expr),
    Block {
        statements: Vec<Stmt>,
    },
    Declaration {
        name: Identifier,
        ty: Type,
        value: Option<Expr>,
    },
    Assignment {
        target: Expr,
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
    Return {
        expr: Expr,
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
    Variable(Identifier),
    ArrayIndex {
        expr: Box<Expr>,
        index: Box<Expr>,
    },
    FieldAccess {
        expr: Box<Expr>,
        field: Identifier,
    },
    Unary {
        operator: UnOp,
        right: Box<Expr>,
    },
    Binary {
        operator: BinOp,
        left: Box<Expr>,
        right: Box<Expr>,
    },
    Call {
        callee: Box<Expr>,
        args: Vec<Expr>,
    },
}

#[derive(Debug)]
pub struct BinOp {
    pub node: Node,
    pub kind: BinOpKind,
}

#[derive(Debug, PartialEq, Eq)]
pub enum BinOpKind {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    And,
    Or,
}

#[derive(Debug)]
pub struct UnOp {
    pub node: Node,
    pub kind: UnOpKind,
}

#[derive(Debug, PartialEq, Eq)]
pub enum UnOpKind {
    Neg,
    Not,
}

#[derive(Debug)]
pub enum LiteralKind {
    Int(i32),
    Float(f64),
    Bool(bool),
    String(Symbol),
}

#[derive(Debug)]
pub struct Identifier {
    pub node: Node,
    pub symbol: Symbol,
}

#[derive(Debug)]
pub struct Type {
    pub node: Node,
    pub name: Identifier,
    pub params: Vec<TypeParam>,
}

#[derive(Debug)]
pub enum TypeParam {
    Type(Box<Type>),
    Const(u32),
}
