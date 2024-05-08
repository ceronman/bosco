#[derive(Debug, Clone)]
pub struct Module {
    importedFunctions: Vec<FunctionImport>,
    data: Vec<Data>,
    definedFunctions: Vec<FunctionDefinition>
}

#[derive(Debug, Clone)]
pub struct FunctionImport {
    module: String,
    import: String,
    name: String,
    params: Vec<Binding>,
    results: Vec<Binding>,
}

#[derive(Debug, Clone)]
pub struct Binding {
    name: String,
    ty: Type,
}

#[derive(Debug, Clone)]
pub struct Data {
    offset: u32,
    contents: String,
}

#[derive(Debug, Clone)]
pub struct FunctionDefinition {
    name: String,
    export: Option<Export>,
    params: Vec<Binding>,
    results: Vec<Binding>,
    instructions: Vec<Instruction>,
}

#[derive(Debug, Clone)]
pub struct Export {
    name: String,
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
