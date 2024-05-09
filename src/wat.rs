mod test;

use crate::ir::{
    Data, Export, FunctionDefinition, Import, ImportKind, Instruction, Module, Param, Return, Type,
};

trait WatEmitter {
    fn to_wat(&self) -> String;
}

impl WatEmitter for Module {
    fn to_wat(&self) -> String {
        let imports = self.imports.to_wat();
        let data = self.data.to_wat();
        let fn_defs = self.defined_functions.to_wat();
        format!("(module {} {} {})", imports, data, fn_defs)
    }
}

impl WatEmitter for Import {
    fn to_wat(&self) -> String {
        format!(
            "(import {} {} {})",
            quote(&self.module),
            quote(&self.name),
            self.kind.to_wat()
        )
    }
}

impl WatEmitter for ImportKind {
    fn to_wat(&self) -> String {
        match self {
            ImportKind::Func {
                name,
                params,
                results,
            } => format!("(func ${} {} {})", name, params.to_wat(), results.to_wat()),
            ImportKind::Mem { id } => format!("(memory {})", id),
        }
    }
}

impl WatEmitter for Type {
    fn to_wat(&self) -> String {
        match self {
            Type::I32 => "i32".to_string(),
            Type::I64 => "i54".to_string(),
            Type::F32 => "f32".to_string(),
            Type::F64 => "f64".to_string(),
        }
    }
}

impl<T> WatEmitter for Vec<T>
where
    T: WatEmitter,
{
    fn to_wat(&self) -> String {
        self.iter()
            .map(|element| element.to_wat())
            .collect::<Vec<String>>()
            .join(" ")
    }
}

impl<T> WatEmitter for Option<T>
where
    T: WatEmitter,
{
    fn to_wat(&self) -> String {
        match self {
            None => "".to_string(),
            Some(inner) => inner.to_wat(),
        }
    }
}

impl WatEmitter for Param {
    fn to_wat(&self) -> String {
        format!("(param ${} {})", self.name, self.ty.to_wat())
    }
}

impl WatEmitter for Return {
    fn to_wat(&self) -> String {
        format!("(result {})", self.ty.to_wat())
    }
}

impl WatEmitter for Data {
    fn to_wat(&self) -> String {
        format!(
            "(data (i32.const {}) {})",
            self.offset,
            quote(&self.contents)
        )
    }
}

impl WatEmitter for FunctionDefinition {
    fn to_wat(&self) -> String {
        format!(
            "(func ${} {} {})",
            self.name,
            self.export.to_wat(),
            self.instructions.to_wat()
        )
    }
}

impl WatEmitter for Export {
    fn to_wat(&self) -> String {
        format!("(export {})", quote(&self.name))
    }
}

fn quote(s: &String) -> String {
    format!("\"{}\"", s)
}

impl WatEmitter for Instruction {
    fn to_wat(&self) -> String {
        match self {
            Instruction::I32Const(value) => format!("(i32.const {})", value),
            Instruction::I64Const(value) => format!("(i64.const {})", value),
            Instruction::F32Const(value) => format!("(f32.const {})", value),
            Instruction::F64Const(value) => format!("(f54.const {})", value),
            Instruction::Call(name) => format!("(call ${})", name),
        }
    }
}
