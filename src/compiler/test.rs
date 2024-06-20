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

    let output_print_num = output.clone();
    let print_num = Func::wrap(&mut store, move |_caller: Caller<'_, ()>, num: i32| {
        output_print_num
            .lock()
            .unwrap()
            .push_str(&format!("{num}\n"));
        Ok(())
    });

    let mut linker = <Linker<HostState>>::new(&engine);
    linker.define("js", "print", print)?;
    linker.define("js", "print_num", print_num)?;
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
            let a i32 = 1
            print_num(a)
            a = 64
            print_num(a)
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
            let a i32 = 1
            let b i32 = 2
            let c i32 = a + b * 2 + 4
            print_num(c)
            let d i32 = a + b * c / 5 % 2
            print_num(d)
            let e i32 = (a + b) * (c - d)
            print_num(e)
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
            let a i32 = 1
            let b i32 = 2
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
            let x i32 = 5
            while x > 0 {
                print_num(x)
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
            let x i32 = 1
            {
                print_num(x)
                let x i32 = 2
                print_num(x)
            }
            print_num(x)
        "#,
        r#"
            1
            2
            1
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
        "Compilation Error: The 'print' function requires one argument at Span(0, 7)",
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
        let x i32 = 1
        let x i32 = 2
    "#,
        "Compilation Error: Variable 'x' was already declared in this scope at Span(35, 36)",
    );
    assert_error(
        "let x = 1",
        "Parse Error: Expected variable type, got Equal at Span(6, 7)",
    );
}
