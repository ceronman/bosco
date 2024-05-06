(module
    (import "js" "print" (func $print (param $start i32) (param $len i32)))
    (import "js" "mem" (memory 1))
    (data (i32.const 0) "Hello from Wasm!")
    (func $hello (export "hello")
        (i32.const 0)
        (i32.const 17)
        (call $print)))