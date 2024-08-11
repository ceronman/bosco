use crate::lexer::Span;
use std::fmt::{Display, Formatter};
use std::rc::Rc;

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

#[derive(Debug, Clone)]
pub struct Module {
    pub _node: Node,
    pub items: Rc<[Item]>,
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
    pub params: Rc<[Param]>,
    pub body: Stmt,
}

#[derive(Debug, Clone)]
pub struct Record {
    pub name: Identifier,
    pub fields: Rc<[Field]>,
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
        statements: Rc<[Stmt]>,
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
        then_block: Rc<Stmt>,
        else_block: Option<Rc<Stmt>>,
    },
    While {
        condition: Expr,
        body: Rc<Stmt>,
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
        expr: Rc<Expr>,
        index: Rc<Expr>,
    },
    FieldAccess {
        expr: Rc<Expr>,
        field: Identifier,
    },
    Unary {
        operator: UnOp,
        right: Rc<Expr>,
    },
    Binary {
        operator: BinOp,
        left: Rc<Expr>,
        right: Rc<Expr>,
    },
    Call {
        callee: Rc<Expr>,
        args: Rc<[Expr]>,
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
    pub params: Rc<[TypeParam]>,
}

#[derive(Debug, Clone)]
pub enum TypeParam {
    Type(Rc<Type>),
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
