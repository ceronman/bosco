use ariadne::{Label, Report, ReportKind, Source};
use std::sync::{Arc, Mutex};

use wasmi::{Caller, Engine, Func, Linker, Memory, MemoryType, Module, Store};

use crate::compiler::{compile, CompileError};
use crate::lexer::Span;
use crate::parser::ParseError;

fn run_in_wasmi(source: &str) -> anyhow::Result<String> {
    let wasm = compile(source)?;
    // let wat = wasmprinter::print_bytes(&wasm)?; println!("\n{wat}\n");
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
    let hello = instance.get_typed_func::<(), ()>(&store, "main")?;
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
        Err(dynamic_error) => {
            let mut title = "Unknown error";
            let mut message = format!("{dynamic_error:?}");
            let mut span = Span(0, 0);
            if let Some(e) = dynamic_error.downcast_ref::<CompileError>() {
                title = "Compile Error";
                message = e.msg.clone();
                span = e.span;
            }
            if let Some(e) = dynamic_error.downcast_ref::<ParseError>() {
                title = "Parse Error";
                message = e.msg.clone();
                span = e.span;
            }
            let mut buffer = Vec::new();
            Report::build(ReportKind::Error, (), span.0)
                .with_message(title)
                .with_label(Label::new(span.0..span.1).with_message(message))
                .finish()
                .write(Source::from(source), &mut buffer)
                .unwrap();
            panic!("{}\n{dynamic_error:?}", String::from_utf8(buffer).unwrap());
        }
    }
}

#[test]
fn test_hello_world() {
    program_test(
        r#"
            export fn main() {
                print("Hello world!")
            }
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
            export fn main() {
                let a int = 1
                print_int(a)
                a = 64
                print_int(a)
                let b float
                b = 1.5
                print_float(b)
            }
        "#,
        r#"
            1
            64
            1.5
        "#,
    )
}

#[test]
fn test_one() {
    program_test(
        r#"
            export fn main() {
                print("hello")
            }
        "#,
        r#"
            hello
        "#,
    )
}

#[test]
fn test_expressions() {
    program_test(
        r#"
            export fn main() {
                let a int = 1
                let b int = 2
                let c int = a + b * 2 + 4
                print_int(c)
                let d int = a + b * c / 5 % 2
                print_int(d)
                let e int = (a + b) * (c - d)
                print_int(e)
            }
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
            export fn main() {
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
            export fn main() {
                let x int = 5
                while x > 0 {
                    print_int(x)
                    x = x - 1
                }
                print("end")
            }
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
            export fn main() {
                let x int = 1
                {
                    print_int(x)
                    let x int = 2
                    print_int(x)
                }
                print_int(x)
            }
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
            export fn main() {
                let x float = 1.0
                let y float = 2.0
                print_float(x / y)
            }
        "#,
        r#"
            0.5
        "#,
    )
}

#[test]
fn test_bool() {
    program_test(
        r#"
            export fn main() {
                let x bool = true
                let y bool = false
                if x or y {
                    print("worked")
                }
            }
        "#,
        r#"
            worked
        "#,
    )
}

#[test]
fn test_functions() {
    program_test(
        r#"
            export fn main() {
                print("hello main!")
                print_int(foo(4, 5))
            }

            fn foo(a int, b int) int {
                let x int = a * b
                return x + 1
            }
        "#,
        r#"
            hello main!
            21
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

// TODO: Make the spans not a nightmare please!!!
#[test]
fn test_errors() {
    assert_error(
        "export fn main() { print() }",
        "Compilation Error: The 'print' function requires a single argument at Span(19, 26)",
    );
    assert_error(
        "export fn main() { print(",
        "Parse Error: Expected expression, got Eof at Span(25, 25)",
    );
    assert_error(
        "export fn main() { x = 1 }",
        "Compilation Error: Undeclared variable 'x' at Span(19, 20)",
    );
    assert_error(
        r#"
            export fn main() {
                let x int = 1
                let x int = 2
            }
    "#,
        "Compilation Error: Variable 'x' was already declared in this scope at Span(82, 83)",
    );
    assert_error(
        "export fn main() { let x = 1 }",
        "Parse Error: Expected type, found Equal instead at Span(25, 26)",
    );
}

#[test]
fn test_type_errors() {
    assert_error(
        "export fn main() { let x float = 1 }",
        "Compilation Error: Type Error: expected Float but found Int at Span(33, 34)",
    );
    assert_error(
        r#"
            export fn main() {
                let x int = 1
                let y float = x
            }
        "#,
        "Compilation Error: Type Error: expected Float but found Int at Span(92, 93)",
    );
    assert_error(
        r#"
            export fn main() {
                let x int = 1
                let y float = 1.5
                let z int = x + y
            }
        "#,
        "Compilation Error: Type Error: operator Plus has incompatible types Int and Float at Span(124, 129)",
    );

    assert_error(
        r#"
            export fn main() {
                let x int = 1
                if 2 > 1 {
                    x = 1.5
                }
            }
        "#,
        "Compilation Error: Type Error: expected Int but found Float at Span(113, 116)",
    );

    assert_error(
        r#"
            export fn main() {
                let x int = 1
                let y float = 1.5
                let z int = x % y
            }
        "#,
        "Compilation Error: Type Error: operator Percent has incompatible types Int and Float at Span(124, 129)",
    );

    assert_error(
        r#"
            export fn main() {
                let x float = 1.0
                let y float = 1.5
                let z int = x % y
            }
        "#,
        "Compilation Error: Type Error: '%' operator doesn't work on floats at Span(128, 133)",
    );

    assert_error(
        "export fn main() { print_int(1.5) }",
        "Compilation Error: Type Error: argument type mismatch at Span(29, 32)",
    );

    assert_error(
        "export fn main() { print_float(1) }",
        "Compilation Error: Type Error: argument type mismatch at Span(31, 32)",
    );

    assert_error(
        r#"
            export fn main() {
                if 1 {
                    print("hello")
                }
            }
        "#,
        "Compilation Error: Type Error: condition should be 'bool', but got Int at Span(51, 52)",
    );

    assert_error(
        r#"
            export fn main() {
                while 0.0 {
                    print("hello")
                }
            }
        "#,
        "Compilation Error: Type Error: condition should be 'bool', but got Float at Span(54, 57)",
    );

    assert_error(
        r#"
            export fn main() {
                let x int = 1
                let y int = 1
                if x or y {
                    print("foo!")
                }
            }
        "#,
        "Compilation Error: Type Error: operand should be 'bool' at Span(111, 112)",
    );
}
