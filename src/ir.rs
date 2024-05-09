mod test;

#[derive(Debug, Clone)]
pub struct Module {
    pub imports: Vec<Import>,
    pub data: Vec<Data>,
    pub defined_functions: Vec<FunctionDefinition>,
}

// TODO: Find proper names
#[derive(Debug, Clone)]
pub struct Import {
    pub module: String,
    pub name: String,
    pub kind: ImportKind,
}

#[derive(Debug, Clone)]
pub enum ImportKind {
    Func {
        name: String,
        params: Vec<Param>,
        results: Vec<Return>,
    },
    Mem {
        id: u32,
    },
}

#[derive(Debug, Clone)]
pub struct Param {
    pub name: String,
    pub ty: Type,
}

#[derive(Debug, Clone)]
pub struct Return {
    pub ty: Type,
}

#[derive(Debug, Clone)]
pub struct Data {
    pub offset: u32,
    pub contents: String,
}

#[derive(Debug, Clone)]
pub struct FunctionDefinition {
    pub name: String,
    pub export: Option<Export>,
    pub params: Vec<Param>,
    pub results: Vec<Return>,
    pub instructions: Vec<Instruction>,
}

#[derive(Debug, Clone)]
pub struct Export {
    pub name: String,
}
#[derive(Debug, Clone)]
pub enum Type {
    I32,
    I64,
    F32,
    F64,
}
#[derive(Debug, Clone)]
pub enum Instruction {
    I32Const(i32),
    I64Const(i64),
    F32Const(f32),
    F64Const(f64),

    Call(String),
}
