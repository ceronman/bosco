use std::fmt::{write, Display, Formatter};
use crate::ast::Symbol;
use std::rc::Rc;

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Type {
    Void,
    Int,
    Float,
    Bool,
    Array { inner: Rc<Type>, size: u32 },
    Record { fields: Rc<[Field]> },
    Function(Signature),
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Signature {
    pub params: Rc<[Type]>,
    pub return_ty: Rc<Type>,
}

#[derive(Debug, Eq, PartialEq)]
pub struct Field {
    pub name: Symbol,
    pub ty: Rc<Type>,
}

impl Display for Type {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Void => write!(f, "void"),
            Type::Int => write!(f, "int"),
            Type::Float => write!(f, "float"),
            Type::Bool => write!(f, "bool"),
            Type::Array { inner, size } => write!(f, "Array<{inner}, {size}>"),
            Type::Record { .. } => write!(f, "record"), // TODO: should probably print record name 
            Type::Function(_) => write!(f, "function"), // TODO: signature
        }
    }
}
