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

// TODO: Decide if Clone is the best thing to do here, or lifetimes instead.
// If decided for Clone, then make pointers Rc instead of Box.
#[derive(Debug, Clone)]
pub struct Module {
    pub _node: Node,
    pub items: Vec<Item>,
}

#[derive(Debug, Clone)]
pub struct Item {
    pub node: Node,
    pub kind: ItemKind,
}

#[derive(Debug, Clone)]
pub enum ItemKind {
    Function(Function),
    Record(Record),
}

#[derive(Debug, Clone)]
pub struct Function {
    pub exported: bool,
    pub name: Identifier,
    pub return_ty: Option<Type>,
    pub params: Vec<Param>,
    pub body: Stmt,
}

#[derive(Debug, Clone)]
pub struct Record {
    pub name: Identifier,
    pub fields: Vec<Field>,
}

#[derive(Debug, Clone)]
pub struct Field {
    pub name: Identifier,
    pub ty: Type,
}

#[derive(Debug, Clone)]
pub struct Param {
    pub name: Identifier,
    pub ty: Type,
}

#[derive(Debug, Clone)]
pub struct Stmt {
    pub node: Node,
    pub kind: StmtKind,
}

#[derive(Debug, Clone)]
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

#[derive(Debug, Clone)]
pub struct Expr {
    pub node: Node,
    pub kind: ExprKind,
}

#[derive(Debug, Clone)]
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

#[derive(Debug, Clone)]
pub struct BinOp {
    pub node: Node,
    pub kind: BinOpKind,
}

#[derive(Debug, PartialEq, Eq, Clone)]
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

#[derive(Debug, Clone)]
pub struct UnOp {
    pub node: Node,
    pub kind: UnOpKind,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum UnOpKind {
    Neg,
    Not,
}

#[derive(Debug, Clone)]
pub enum LiteralKind {
    Int(i32),
    Float(f64),
    Bool(bool),
    String(Symbol),
}

#[derive(Debug, Clone)]
pub struct Identifier {
    pub node: Node,
    pub symbol: Symbol,
}

#[derive(Debug, Clone)]
pub struct Type {
    pub node: Node,
    pub name: Identifier,
    pub params: Vec<TypeParam>,
}

#[derive(Debug, Clone)]
pub enum TypeParam {
    Type(Box<Type>),
    Const(u32),
}

impl Identifier {
    pub fn fake(s: &str) -> Self {
        Self {
            node: Node {
                id: 0,
                span: Span(0, 0),
            },
            symbol: Symbol::from(s),
        }
    }
}
