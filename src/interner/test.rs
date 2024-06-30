use crate::interner::Interner;

use stats_alloc::{StatsAlloc, Region, INSTRUMENTED_SYSTEM};
use std::alloc::System;

#[global_allocator]
static GLOBAL: &StatsAlloc<System> = &INSTRUMENTED_SYSTEM;

#[test]
fn test_interner() {
    let reg = Region::new(&GLOBAL);
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

    println!("Stats at 1: {:#?}", reg.change());
}