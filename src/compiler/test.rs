use std::sync::{Arc, Mutex};

use ariadne::{Label, Report, ReportKind, Source};
use regex::Regex;
use wasmi::{Caller, Engine, Extern, Func, Linker, Module, Store};

use crate::compiler::compile;
use crate::error::CompilerError;

fn run_in_wasmi(source: &str) -> anyhow::Result<String> {
    let wasm = compile(source)?;
    // let wat = wasmprinter::print_bytes(&wasm)?; println!("\n{wat}\n");
    let engine = Engine::default();
    let module = Module::new(&engine, &wasm)?;

    type HostState = ();
    let mut store = Store::new(&engine, ());

    let output = Arc::new(Mutex::new(String::new()));
    let output_print = output.clone();
    let print = Func::wrap(
        &mut store,
        move |caller: Caller<'_, ()>, ptr: i32, len: i32| {
            let mem = match caller.get_export("memory") {
                Some(Extern::Memory(mem)) => mem,
                _ => return Err(wasmi::Error::new("Memory not found")),
            };
            let bytes = &mem.data(&caller)[(ptr as usize)..(ptr + len) as usize];
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
            // TODO Make CompilerError enum to avoid this kind of duplication
            if let Some(e) = dynamic_error.downcast_ref::<CompilerError>() {
                let mut buffer = Vec::new();
                Report::build(ReportKind::Error, (), e.span.0)
                    .with_message("Compile Error")
                    .with_label(Label::new(e.span.0..e.span.1).with_message(&e.msg))
                    .finish()
                    .write(Source::from(source), &mut buffer)
                    .unwrap();
                panic!("{}\n{}", String::from_utf8(buffer).unwrap(), e.backtrace);
            } else {
                panic!("{dynamic_error:?}");
            }
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
                let f int = -1
                print_int(f)
                let g int = -1 + (a + b)
                print_int(g)
            }
        "#,
        r#"
            9
            2
            21
            -1
            2
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

#[test]
fn test_arrays() {
    program_test(
        r#"
            export fn main() {
                let items Array<int, 5>
                items[0] = 4
                items[4] = 5
                let result int = items[0] * items[4]
                let i int = 0
                print_int(items[i])
                i = 4
                print_int(items[i])
                print_int(result)
                i = 2
                items[i + 1] = 100
                print_int(items[i + 1])
                let floats Array<float, 2>
                floats[0] = 1.5
                floats[1] = 0.5
                print_float(floats[0] + floats[1])
                let bools Array<bool, 3>
                bools[0] = false
                bools[1] = true
                bools[2] = false
                if bools[1] {
                    print_int(1)
                }
            }
        "#,
        r#"
            4
            5
            20
            100
            2
            1
        "#,
    )
}

#[test]
fn test_arrays_mini() {
    program_test(
        r#"
            export fn main() {
                let items Array<int, 5>
                items[0] = 4
                print_int(items[0])
            }
        "#,
        r#"
            4
        "#,
    )
}

#[test]
fn test_nested_arrays() {
    program_test(
        r#"
            export fn main() {
                let nested Array<Array<int, 4>, 3>
                nested[0][0] = 100
                print_int(nested[0][0])

                let nested2 Array<Array<float, 2>, 3>
                nested2[1][1] = 1.5
                print_float(nested2[1][1])
            }
        "#,
        r#"
        100
        1.5
        "#,
    )
}

fn assert_error(annotated_source: &str) {
    let error_re = Regex::new(r"^\s*//\s*(\^*)\s+(.*)\n$").unwrap();
    let mut source = String::new();
    for line in annotated_source.split_inclusive('\n') {
        if error_re.captures(line).is_none() {
            source.push_str(line);
        }
    }

    fn annotate_result(source: String, span: crate::lexer::Span, msg: String) -> String {
        let mut result = String::new();
        let mut offset = 0;
        let mut annotated = false;
        for line in source.split_inclusive('\n') {
            result.push_str(line);
            if !annotated && offset + line.len() > span.0 {
                let start = span.0 - offset - 2;
                let len = span.1 - span.0;
                let annotation = format!("{}//{} {}\n", " ".repeat(start), "^".repeat(len), msg,);
                result.push_str(&annotation);
                annotated = true
            }
            offset += line.len();
        }
        result
    }

    match compile(&source) {
        Ok(_) => panic!("No error returned"),
        Err(e) => {
            let result = annotate_result(source, e.span, format!("{}: {}", e.kind, e.msg));
            if result != annotated_source {
                eprintln!("{}", e.backtrace);
            }
            assert_eq!(result, annotated_source);
        }
    }
}

#[test]
fn test_function_call_argument_check() {
    assert_error(
        r#"
        export fn main() {
            print()
          //^^^^^^^ Compiler Error: The 'print' function requires a single argument
        }"#,
    );
}

#[test]
fn test_parse_error_expected_closing_paren() {
    assert_error(
        r#"
        export fn main() {
            print(
// ParseError: Expected expression, got Eof"#,
    );
}

#[test]
fn test_undeclared_var() {
    assert_error(
        r#"
        export fn main() {
            x = 1
          //^ Compiler Error: Undeclared variable 'x'
        }"#,
    );
}

#[test]
fn test_already_declared_var() {
    assert_error(
        r#"
        export fn main() {
            let x int = 1
            let x int = 2
              //^ Compiler Error: Variable 'x' was already declared in this scope
        }"#,
    );
}

#[test]
fn test_parse_missing_explicit_type() {
    assert_error(
        r#"
        export fn main() {
            let x = 1
                //^ Parsing Error: Expected type, found Equal instead
        }"#,
    );
}

#[test]
fn test_duplicate_function() {
    assert_error(
        r#"
        export fn main() {
        }
        
        fn foo() {}
        fn foo(x int) int {}
         //^^^ Compiler Error: Function 'foo' was already defined
        "#,
    );
}

#[test]
fn test_duplicate_function_from_export() {
    assert_error(
        r#"
        export fn main() {
        }
        
        fn print_int(x int) int {}
         //^^^^^^^^^ Compiler Error: Function 'print_int' was already defined
        "#,
    );
}

#[test]
fn test_assignment_type_mismatch() {
    assert_error(
        r#"
        export fn main() {
            let x float = 1
                        //^ Compiler Error: Type Error: expected Float but found Int
        }"#,
    );
}

#[test]
fn test_assignment_type_mismatch_2() {
    assert_error(
        r#"
        export fn main() {
            let x int = 1
            let y float = x
                        //^ Compiler Error: Type Error: expected Float but found Int
        }"#,
    );
}

#[test]
fn test_binary_operation_type_mismatch() {
    assert_error(
        r#"
        export fn main() {
            let x int = 1
            let y float = 1.5
            let z int = x + y
                      //^^^^^ Compiler Error: Type Error: operator Add has incompatible types Int and Float
        }"#,
    );
}

#[test]
fn test_type_mismatch_in_if() {
    assert_error(
        r#"
        export fn main() {
            let x int = 1
            if 2 > 1 {
                x = 1.5
                  //^^^ Compiler Error: Type Error: expected Int but found Float
            }
        }"#,
    );
}

#[test]
fn test_modulo_type_mismatch() {
    assert_error(
        r#"
        export fn main() {
            let x int = 1
            let y float = 1.5
            let z int = x % y
                      //^^^^^ Compiler Error: Type Error: operator Mod has incompatible types Int and Float
        }"#,
    );
}

#[test]
fn test_module_type_mismatch_2() {
    assert_error(
        r#"
        export fn main() {
            let x float = 1.0
            let y float = 1.5
            let z int = x % y
                      //^^^^^ Compiler Error: Type Error: '%' operator doesn't work on floats
        }"#,
    );
}

#[test]
fn test_function_call_arg_type_mismatch() {
    assert_error(
        r#"
        export fn main() {
            print_int(1.5)
                    //^^^ Compiler Error: Type Error: argument type mismatch
        }"#,
    );
}

#[test]
fn function_call_arg_type_mismatch_2() {
    assert_error(
        r#"
        export fn main() {
            print_float(1)
                      //^ Compiler Error: Type Error: argument type mismatch
        }"#,
    );
}

#[test]
fn test_condition_type_mismatch() {
    assert_error(
        r#"
        export fn main() {
            if 1 {
             //^ Compiler Error: Type Error: condition should be 'bool', but got Int

                print("hello")
            }
        }"#,
    );
}

#[test]
fn test_while_condition_type_mismatch() {
    assert_error(
        r#"
        export fn main() {
            while 0.0 {
                //^^^ Compiler Error: Type Error: condition should be 'bool', but got Float
                print("hello")
            }
        }"#,
    );
}

#[test]
fn test_logical_operator_type_mismatch() {
    assert_error(
        r#"
        export fn main() {
            let x int = 1
            let y int = 1
            if x or y {
             //^ Compiler Error: Type Error: operand should be 'bool'

                print("foo!")
            }
        }"#,
    );
}

#[test]
fn test_return_type_mismatch() {
    assert_error(
        r#"
        export fn main() {
            return 1
          //^^^^^^^^ Compiler Error: Type Error: return type mismatch, expected Void, but found Int
        }"#,
    );
}

#[test]
fn test_return_type_mismatch_2() {
    assert_error(
        r#"
        export fn main() {
            let a int = foo(1)
        }

        fn foo(x int) int {
            return true
          //^^^^^^^^^^^ Compiler Error: Type Error: return type mismatch, expected Int, but found Bool
        }
        "#,
    );
}

#[test]
fn test_array_index_type_mismatch() {
    assert_error(
        r#"
        export fn main() {
            let a int = 1
            let b int = a[1]
                      //^ Compiler Error: Type Error: Expecting an Array, found Int
        }
        "#,
    );
}

#[test]
fn test_array_index_assignment_type_mismatch() {
    assert_error(
        r#"
        export fn main() {
            let a int = 1
            a[1] = 2
          //^ Compiler Error: Type Error: Expecting an Array, found Int
        }
        "#,
    );
}

#[test]
fn test_array_indexing_expression_type_mismatch() {
    assert_error(
        r#"
        export fn main() {
            let a Array<int, 5>
            a[true or false]
            //^^^^^^^^^^^^^ Compiler Error: Type Error: Array index must be Int
        }
        "#,
    );
}

#[test]
fn test_nested_array_assignment_type_mismatch() {
    assert_error(
        r#"
        export fn main() {
            let a Array<Array<float, 2>, 5>
            a[0][0] = true
                    //^^^^ Compiler Error: Type Error: expected Float but found Bool
        }
        "#,
    );
}

#[test]
fn test_nested_array_index_expr_type_mismatch() {
    assert_error(
        r#"
        export fn main() {
            let a Array<Array<float, 2>, 2>
            if a[0][0] {
             //^^^^^^^ Compiler Error: Type Error: condition should be 'bool', but got Float
                print("it worked")
            }
        }
        "#,
    );
}
