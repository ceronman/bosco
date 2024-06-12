use crate::compiler::Compiler;
use crate::parser::parse;
use std::io::Write;
use std::sync::atomic::{AtomicUsize, Ordering};

static GLOBAL_THREAD_COUNT: AtomicUsize = AtomicUsize::new(0);

fn program_test(source: &str, expected_out: &str) {
    let module = parse(source).unwrap(); // TODO: Improve error display
    let mut compiler = Compiler::new(source);
    let bytes = compiler.compile(&module);
    let filename = format!(
        "test_{}.wasm",
        GLOBAL_THREAD_COUNT.fetch_add(1, Ordering::Relaxed)
    );

    let mut f = std::fs::OpenOptions::new()
        .create(true)
        .write(true)
        .truncate(true)
        .open(format!("web/{}", filename))
        .unwrap();
    f.write_all(&bytes).unwrap();
    f.flush().unwrap();
    // let wat = wasmprinter::print_bytes(bytes).unwrap();
    // println!("{}", wat);
    use std::process::{Command, Stdio};

    let output = Command::new("deno")
        .current_dir("web")
        .arg("run")
        .arg("--allow-read")
        .arg("hello.ts")
        .arg(&filename)
        .stdout(Stdio::piped())
        .output()
        .unwrap();

    let e = expected_out
        .trim()
        .lines()
        .map(|e| e.trim())
        .collect::<Vec<_>>()
        .join("\n");
    assert_eq!(e, std::str::from_utf8(&output.stdout).unwrap().trim());

    std::fs::remove_file(format!("web/{}", filename)).unwrap();
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
