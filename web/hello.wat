(module
  (type (;0;) (func (param i32 i32)))
  (type (;1;) (func))
  (import "js" "print" (func (;0;) (type 0)))
  (import "js" "mem" (memory (;0;) 0))
  (data (;0;) (i32.const 0) "Hello from Wasm Encoder!")
  (func (;1;) (type 1)
    i32.const 0
    i32.const 24
    call 0
  )
  (export "hello" (func 1))
)