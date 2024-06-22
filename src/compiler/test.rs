use std::sync::{Arc, Mutex};

use wasmi::{Caller, Engine, Func, Linker, Memory, MemoryType, Module, Store};

use crate::compiler::compile;

fn run_in_wasmi(source: &str) -> anyhow::Result<String> {
    let wasm = compile(source)?;
    let engine = Engine::default();
    let module = Module::new(&engine, &wasm)?;

    type HostState = ();
    let mut store = Store::new(&engine, ());

    let memory_type = MemoryType::new(1, None).unwrap();
    let memory = Memory::new(&mut store, memory_type).unwrap();
    let imported_memory = memory.clone();
    let output = Arc::new(Mutex::new(String::new()));
    let output_print = output.clone();
    let print = Func::wrap(
        &mut store,
        move |caller: Caller<'_, ()>, ptr: i32, len: i32| {
            let bytes = &imported_memory.data(&caller)[(ptr as usize)..(ptr + len) as usize];
            let message = std::str::from_utf8(bytes).unwrap();
            output_print.lock().unwrap().push_str(message);
            output_print.lock().unwrap().push('\n');
            Ok(())
        },
    );

    let output_print_int = output.clone();
    let print_int = Func::wrap(&mut store, move |_caller: Caller<'_, ()>, num: i32| {
        output_print_int
            .lock()
            .unwrap()
            .push_str(&format!("{num}\n"));
        Ok(())
    });

    let output_print_float = output.clone();
    let print_float = Func::wrap(&mut store, move |_caller: Caller<'_, ()>, num: f64| {
        output_print_float
            .lock()
            .unwrap()
            .push_str(&format!("{num}\n"));
        Ok(())
    });

    let mut linker = <Linker<HostState>>::new(&engine);
    linker.define("js", "print", print)?;
    linker.define("js", "print_int", print_int)?;
    linker.define("js", "print_float", print_float)?;
    linker.define("js", "mem", memory)?;

    let instance = linker.instantiate(&mut store, &module)?.start(&mut store)?;
    let hello = instance.get_typed_func::<(), ()>(&store, "hello")?;
    hello.call(&mut store, ())?;

    let result = output.clone().lock().unwrap().as_str().to_string();
    Ok(result)
}

fn program_test(source: &str, expected_out: &str) {
    match run_in_wasmi(source) {
        Ok(output) => {
            assert_eq!(
                output.trim(),
                expected_out
                    .trim()
                    .lines()
                    .map(|e| e.trim())
                    .collect::<Vec<_>>()
                    .join("\n")
            );
        }
        Err(e) => panic!("{e:?}"),
    }
}

#[test]
fn test_hello_world() {
    program_test(
        r#"
            print("Hello world!")
        "#,
        r#"
            Hello world!
        "#,
    )
}

#[test]
fn test_declaration_assignment() {
    program_test(
        r#"
            let a int = 1
            print_int(a)
            a = 64
            print_int(a)
        "#,
        r#"
            1
            64
        "#,
    )
}

#[test]
fn test_expressions() {
    program_test(
        r#"
            let a int = 1
            let b int = 2
            let c int = a + b * 2 + 4
            print_int(c)
            let d int = a + b * c / 5 % 2
            print_int(d)
            let e int = (a + b) * (c - d)
            print_int(e)
        "#,
        r#"
            9
            2
            21
        "#,
    )
}

#[test]
fn test_if_statement() {
    program_test(
        r#"
            let a int = 1
            let b int = 2
            if a > b {
                print("first")
            } else {
                print("second")
            }
            if 1 > 10 {
                print("Should not print")
            }
            if a == 1 {
                print("This should be printed")
            }

            if a < 0 or b > 4 or a == 1 and not (b == 1) {
                print("logical operators work")
            }
        "#,
        r#"
            second
            This should be printed
            logical operators work
        "#,
    )
}

#[test]
fn test_while_loop() {
    program_test(
        r#"
            let x int = 5
            while x > 0 {
                print_int(x)
                x = x - 1
            }
            print("end")
        "#,
        r#"
            5
            4
            3
            2
            1
            end
        "#,
    )
}

#[test]
fn test_scopes() {
    program_test(
        r#"
            let x int = 1
            {
                print_int(x)
                let x int = 2
                print_int(x)
            }
            print_int(x)
        "#,
        r#"
            1
            2
            1
        "#,
    )
}

#[test]
fn test_float() {
    program_test(
        r#"
            let x float = 1.0
            let y float = 2.0
            print_float(x / y)
        "#,
        r#"
            0.5
        "#,
    )
}

fn assert_error(source: &str, expected: &str) {
    match compile(source) {
        Ok(_) => panic!("No error returned"),
        Err(e) => {
            assert_eq!(format!("{e}"), expected)
        }
    }
}

#[test]
fn test_errors() {
    assert_error(
        "print()",
        "Compilation Error: The 'print' function requires a single argument at Span(0, 7)",
    );
    assert_error(
        "print(",
        "Parse Error: Expected expression, got Eof at Span(6, 6)",
    );
    assert_error(
        "x = 1",
        "Compilation Error: Undeclared variable 'x' at Span(0, 1)",
    );
    assert_error(
        r#"
        let x int = 1
        let x int = 2
    "#,
        "Compilation Error: Variable 'x' was already declared in this scope at Span(35, 36)",
    );
    assert_error(
        "let x = 1",
        "Parse Error: Expected variable type, got Equal at Span(6, 7)",
    );
}

#[test]
fn test_type_errors() {
    assert_error(
        "let x float = 1",
        "Compilation Error: Type Error: expected Float but found Int at Span(14, 15)",
    );
    assert_error(
        r#"
            let x int = 1
            let y float = x
        "#,
        "Compilation Error: Type Error: expected Float but found Int at Span(53, 54)",
    );
    assert_error(
        r#"
            let x int = 1
            let y float = 1.5
            let z int = x + y
        "#,
        "Compilation Error: Type Error: operator Plus has incompatible types Int and Float at Span(81, 86)",
    );

    assert_error(
        r#"
            let x int = 1
            if 2 > 1 {
                x = 1.5
            }
        "#,
        "Compilation Error: Type Error: expected Int but found Float at Span(70, 73)",
    );

    assert_error(
        r#"
            let x int = 1
            let y float = 1.5
            let z int = x % y
        "#,
        "Compilation Error: Type Error: operator Percent has incompatible types Int and Float at Span(81, 86)",
    );

    assert_error(
        r#"
            let x float = 1.0
            let y float = 1.5
            let z int = x % y
        "#,
        "Compilation Error: Type Error: '%' operator doesn't work on floats at Span(85, 90)",
    );

    assert_error(
        "print_int(1.5)",
        "Compilation Error: Function 'print_int' requires an int as argument at Span(0, 14)",
    );

    assert_error(
        "print_float(1)",
        "Compilation Error: Function 'print_float' requires an float as argument at Span(0, 14)",
    );
}
