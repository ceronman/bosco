use std::collections::HashSet;
use std::hash::{Hash, Hasher};
use std::rc::Rc;


#[derive(Clone, Debug, Eq)]
pub struct Symbol(Rc<str>);

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
    strings: HashSet<Rc<str>>
}

impl Interner {
    fn intern(&mut self, s: &str) -> Symbol {
        if let Some(interned) = self.strings.get(s) {
            return Symbol(Rc::clone(interned))
        }
        let inner = Rc::from(s);
        self.strings.insert(Rc::clone(&inner));
        Symbol(inner)
    }
}

#[cfg(test)]
mod test {
    use crate::interner::Interner;

    #[test]
    fn test_interner() {
        let mut interner = Interner::default();

        let a = interner.intern("hello");
        let b = interner.intern("world");
        let c = interner.intern("hello");
        let d = interner.intern("hello");

        assert_eq!(a, c);
        assert_eq!(a, d);
        assert_ne!(a, b);
        assert_eq!(a.as_ref(), "hello");
        assert_eq!(interner.strings.len(), 2);
    }
}