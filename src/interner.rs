use std::collections::HashMap;
use std::hash::{Hash, Hasher};
use std::rc::Rc;

#[cfg(test)]
mod test;

#[derive(Clone, Debug, Eq)]
struct Symbol(Rc<str>);

impl AsRef<str> for Symbol {
    fn as_ref(&self) -> &str {
        self.0.as_ref()
    }
}

impl Hash for Symbol {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.as_ptr().hash(state);
    }
}

impl PartialEq for Symbol {
    fn eq(&self, other: &Self) -> bool {
        self.0.as_ptr() == other.0.as_ptr()
    }
}

#[derive(Default)]
pub struct Interner {
    strings: HashMap<Rc<str>, Symbol>
}

impl Interner {
    fn intern(&mut self, s: &str) -> Symbol {
        if let Some(interned) = self.strings.get(s) {
            return interned.clone()
        }
        let inner = Rc::from(s);
        let symbol = Symbol(Rc::clone(&inner));
        self.strings.insert(inner, symbol.clone());
        symbol
    }
}


// #[derive(Default)]
// pub struct Interner {
//     index: HashMap<Rc<str>, Symbol>,
//     strings: Vec<Rc<str>>
// }
//
// impl Interner {
//     fn intern(&mut self, s: &str) -> Symbol {
//         if let Some(interned) = self.index.get(s) {
//             return interned.clone();
//         }
//         let symbol = Symbol(self.strings.len());
//         let rc1 = Rc::from(s);
//         let rc2 = Rc::clone(&rc1);
//         self.index.insert(rc1, symbol);
//         self.strings.push(rc2);
//
//         debug_assert!(self.get(symbol) == s);
//         debug_assert!(self.intern(s) == symbol);
//
//         symbol
//     }
//
//     fn get(&self, s: Symbol) -> &str {
//         self.strings[s.0].as_ref()
//     }
// }