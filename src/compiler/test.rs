use crate::compiler::Compiler;
use crate::parser::parse;
use std::io::Write;
use std::sync::atomic::{AtomicUsize, Ordering};

static GLOBAL_THREAD_COUNT: AtomicUsize = AtomicUsize::new(0);

fn program_test(source: &str, expected_out: &str) {
    let module = parse(source).unwrap(); // TODO: Improve error display
    let mut compiler = Compiler::new(source);
    let bytes = compiler.compile(&module).unwrap_or_else(|e| {
        eprintln!("ERROR: {e}");
        std::process::exit(1);
    });
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

    // TODO: Instead of using deno, use wasmi or similar
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

    std::fs::remove_file(format!("web/{}", filename)).unwrap();
    assert_eq!(std::str::from_utf8(&output.stdout).unwrap().trim(), e);
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
