use crate::lexer::{Token, TokenKind};
use crate::parser::{parse, Expression};

macro_rules! error {
    ($($arg:tt)*) => {{
        eprintln!($($arg)*);
        std::process::exit(1);
    }};
}

struct Interpreter<'src> {
    source: &'src str,
}

impl<'src> Interpreter<'src> {
    fn new(source: &'src str) -> Self {
        Interpreter { source }
    }

    fn run(self) {
        let module = match parse(self.source) {
            Ok(m) => m,
            Err(error) => {
                error!("Parse error: {} at {}", error.msg, error.start);
            }
        };

        for expr in module.expressions {
            match expr {
                Expression::Call { callee, args } => match self.token_text(callee) {
                    "print" => self.print_builtin(callee, &args),
                    other => {
                        error!("Error: unknown function {} at {}", other, callee.start);
                    }
                },
                _ => {
                    error!("Error: unsupported expression"); // TODO: Need position for error message.
                }
            }
        }
    }

    fn print_builtin(&self, name: Token, args: &[Expression]) {
        match args.len() {
            0 => error!("Error: No arguments passed to 'print'"),
            1 => match args.first().unwrap() {
                Expression::Literal { token } => match token.kind {
                    TokenKind::Str => {
                        let value = self.token_text(*token);
                        println!("{}", &value[1..value.len() - 1])
                    }
                    _ => error!("Invalid argument to 'print' at {}", name.start),
                },
                _ => {
                    error!("Invalid argument to 'print' at {}", name.start)
                }
            },
            _ => error!("Too many arguments for 'print' at {}", name.start),
        }
    }

    fn token_text(&self, token: Token) -> &'src str {
        &self.source[token.start..token.end]
    }
}

pub fn interpret(src: &str) {
    Interpreter::new(src).run()
}
