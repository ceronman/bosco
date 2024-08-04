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
