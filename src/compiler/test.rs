use std::sync::{Arc, Mutex};

use ariadne::{Label, Report, ReportKind, Source};
use regex::Regex;
use wasmi::{Caller, Engine, Extern, Func, Linker, Module, Store};

use crate::compiler::compile;
use crate::error::CompilerError;

fn run_in_wasmi(source: &str) -> anyhow::Result<String> {
    let wasm = compile(source)?;
    // {
    //     use std::io::Write;
    //     let wat = wasmprinter::print_bytes(&wasm)?;
    //     println!("\n{wat}\n");
    //
    //     let mut f = std::fs::OpenOptions::new()
    //         .create(true)
    //         .write(true)
    //         .truncate(true)
    //         .open("src/compiler/main.wasm")?;
    //     f.write_all(&wasm)?;
    //     f.flush()?;
    // }
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

// TODO: Fix with proper data-flow analysis.
#[test]
fn test_function_with_conditional_return() {
    program_test(
        r#"
            export fn main() {
                print_int(cond(true))
            }

            fn cond(c bool) int {
                if c {
                    return 1
                } else {
                    return 2
                }
                1 // Should not be necessary!
            }
        "#,
        r#"
            1
        "#,
    )
}

#[test]
fn test_recursive_stack_function() {
    program_test(
        r#"
            export fn main() {
                let a Array<int, 5>
                a[4] = 100
                print_int(last(a, 0))
            }

            fn last(a Array<int, 5>, i int) int {
                let result int
                if i == 4 {
                    result = a[4]
                } else {
                    result = last(a, i + 1)
                }
                return result
            }
        "#,
        r#"
            100
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
fn test_array_assignment() {
    program_test(
        r#"
            export fn main() {
                let a Array<int, 2>
                a[0] = 10
                a[1] = 20
                let b Array<int, 2>
                b[0] = 1
                b[1] = 2
                print_int(a[0])
                print_int(a[1])
                a = b
                print_int(a[0])
                print_int(a[1])
            }
        "#,
        r#"
            10
            20
            1
            2
        "#,
    )
}

#[test]
fn test_inner_array_assignment() {
    program_test(
        r#"
            export fn main() {
                let a Array<Array<int, 3>, 2>
                a[0][0] = 10
                a[0][1] = 20
                a[0][2] = 30
                let b Array<int, 3>
                b = a[0]
                print_int(b[0])
                print_int(b[1])
                print_int(b[2])
            }
        "#,
        r#"
            10
            20
            30
        "#,
    )
}

#[test]
fn test_array_argument() {
    program_test(
        r#"
            export fn main() {
                let x Array<float, 2>
                x[0] = 20.0
                x[1] = 30.0
                print_array(x)
                print_float(x[0])
                print_float(x[1])
            }

            fn print_array(a Array<float, 2>) {
                a[0] = a[0] + 0.5
                a[1] = a[1] + 0.5
                print_float(a[0])
                print_float(a[1])
            }
        "#,
        r#"
            20.5
            30.5
            20
            30
        "#,
    )
}

#[test]
fn test_array_argument_mixed_with_regular() {
    program_test(
        r#"
            export fn main() {
                let x Array<float, 2>
                print_array(x, 100)
            }

            fn print_array(a Array<float, 2>, b int) {
                print_int(b)
            }
        "#,
        r#"
            100
        "#,
    )
}

#[test]
fn test_array_returned() {
    program_test(
        r#"
            export fn main() {
                let a Array<float, 2> = make_array() 
                print_float(a[0])
                print_float(a[1])
            }

            fn make_array() Array<float, 2> {
                let result Array<float, 2>
                result[0] = 1.5
                result[1] = 2.5
                return result
            }
        "#,
        r#"
            1.5
            2.5
        "#,
    )
}

#[test]
fn test_record_assignment() {
    program_test(
        r#"
            record Point {
                x int
                y int
            }
            export fn main() {
                let p1 Point
                let p2 Point
                p1.x = 100
                p1.y = 200
                p2.x = 10
                p2.y = 20
                print_int(p2.x)
                print_int(p2.y)
                p2 = p1
                print_int(p2.x)
                print_int(p2.y)
            }
        "#,
        r#"
            10
            20
            100
            200
        "#,
    )
}

#[test]
fn test_nested_record_assignment() {
    program_test(
        r#"
            record Line {
                p1 Point
                p2 Point
            }
            record Point {
                x int
                y int
            }
            export fn main() {
                let start Point
                start.x = 50
                start.y = 80
                let l1 Line
                l1.p1 = start
                start.x = 1
                start.y = 2
                l1.p2 = start
                print_int(l1.p1.x)
                print_int(l1.p1.y)
                print_int(l1.p2.x)
                print_int(l1.p2.y)
            }
        "#,
        r#"
            50
            80
            1
            2   
        "#,
    )
}

#[test]
fn test_nested_record_assignment_2() {
    program_test(
        r#"
            record Line {
                p1 Point
                p2 Point
            }
            record Point {
                x int
                y int
            }
            export fn main() {
                let line Line
                line.p1.x = 1
                line.p1.y = 5
                line.p2 = line.p1
                
                print_int(line.p1.x)
                print_int(line.p1.y)
                print_int(line.p2.x)
                print_int(line.p2.y)
            }
        "#,
        r#"
            1
            5
            1
            5
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

#[test]
fn test_records() {
    program_test(
        r#"
            record Point {
                x int
                y int
            }
            
            export fn main() {
                let p Point
                p.x = 4
                p.y = 5
                print_int(p.x * p.y)
            }
        "#,
        r#"
        20
        "#,
    )
}

#[test]
fn test_nested_records() {
    program_test(
        r#"
            record Point {
                x int
                y int
            }

            record Line {
                from Point
                to Point
            }

            export fn main() {
                let line Line

                line.from.x = 0
                line.from.y = 5

                line.to.x = 5
                line.to.y = 0

                print_int(line.from.y * line.to.x)
            }
        "#,
        r#"
        25
        "#,
    )
}

#[test]
fn test_nested_records_and_arrays() {
    program_test(
        r#"
            record Point {
                x int
                y int
                limits Array<int, 2>
            }

            record Data {
                start int
                points Array<Point, 3>
            }

            export fn main() {
                let data Data

                data.points[1].limits[0] = 100

                print_int(data.points[1].limits[0])
            }
        "#,
        r#"
        100
        "#,
    )
}

#[test]
fn test_nested_records_forward_declaration() {
    program_test(
        r#"
            record One {
                a Two
            }

            record Two {
                b int
            }

            export fn main() {
                let one One
                one.a.b = 25
                print_int(one.a.b)
            }
        "#,
        r#"
        25
        "#,
    )
}

#[test]
fn test_record_argument() {
    program_test(
        r#"
            record Point {
                x int
                y int
            }

            export fn main() {
                let point Point
                point.x = 1
                point.y = 2
                print_point(point)
            }
            
            fn print_point(p Point) {
                print_int(p.x)
                print_int(p.y)
            }
        "#,
        r#"
            1
            2
        "#,
    )
}

#[test]
fn test_record_return() {
    program_test(
        r#"
            record Point {
                x int
                y int
            }

            export fn main() {
                let p Point = make_point()
                print_int(p.x)
                print_int(p.y)
            }

            fn make_point() Point {
                let p Point
                p.x = 100
                p.y = 200
                return p
            }
        "#,
        r#"
            100
            200
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
          //^ Compiler Error: Undeclared 'x'
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
              //^ Compiler Error: Name 'x' is already declared in this scope
        }"#,
    );
}

#[test]
fn test_already_declared_param() {
    assert_error(
        r#"
        fn foo(a int, a float) {
                    //^ Compiler Error: Name 'a' is already declared in this scope
        }
        export fn main() {
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
         //^^^ Compiler Error: Name 'foo' is already declared in this scope
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
         //^^^^^^^^^ Compiler Error: Name 'print_int' is already declared in this scope
        "#,
    );
}

#[test]
fn test_assignment_type_mismatch() {
    assert_error(
        r#"
        export fn main() {
            let x float = 1
                        //^ Compiler Error: Type Error: expected float but found int
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
                        //^ Compiler Error: Type Error: expected float but found int
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
                  //^^^ Compiler Error: Type Error: expected int but found float
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
                      //^ Compiler Error: Type Error: int is not an array and cannot be indexed
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
          //^ Compiler Error: Type Error: int is not an array and cannot be indexed
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
                    //^^^^ Compiler Error: Type Error: expected float but found bool
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

#[test]
fn test_duplicated_record() {
    assert_error(
        r#"
        record Foo {
            name int
        }
        
        export fn main() {
        }
        
        record Foo {
             //^^^ Compiler Error: Name 'Foo' is already declared in this scope
            weight float
        }
        "#,
    );
}

#[test]
fn test_get_field_of_no_record() {
    assert_error(
        r#"
        export fn main() {
            let x Array<int, 2>
            print_int(x.foo)
                    //^^^^^ Compiler Error: Type Error: Array<int, 2> is not a record and does not have fields
        }
        "#,
    );
}

#[test]
fn test_calling_non_function() {
    assert_error(
        r#"
        export fn main() {
            let foo int = 1
            foo(2, 3)
          //^^^ Compiler Error: 'foo' is not a function
        }
        "#,
    );
}

#[test]
fn test_calling_function_with_wrong_arguments() {
    assert_error(
        r#"
        export fn main() {
            foo(2, 3)
          //^^^^^^^^^ Compiler Error: Function called with incorrect number of arguments
        }

        fn foo(x int) {
        }
        "#,
    );
}

#[test]
fn test_calling_arbitrary_expressions() {
    assert_error(
        r#"
        export fn main() {
            (1 + 1)(2, 3)
          //^^^^^^^ Compiler Error: Arbitrary expressions cannot be called as functions
        }
        "#,
    );
}

#[test]
fn test_wrong_array_assignment() {
    assert_error(
        r#"
        export fn main() {
            let a Array<int, 2>
            let b Array<int, 3>
            a = b
              //^ Compiler Error: Type Error: expected Array<int, 2> but found Array<int, 3>
        }
        "#,
    );
}
