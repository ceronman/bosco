use crate::lexer::Span;
use std::backtrace::Backtrace;
use std::error::Error;
use std::fmt::{Display, Formatter};

#[derive(Debug)]
pub struct CompilerError {
    pub msg: String,
    pub span: Span,
    pub backtrace: Backtrace,
    pub kind: ErrorKind,
}

impl Error for CompilerError {}

impl Display for CompilerError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{kind}: {msg}", kind = self.kind, msg = self.msg)
    }
}

pub type CompilerResult<T> = Result<T, CompilerError>;

#[derive(Debug)]
pub enum ErrorKind {
    Parse,
    Type,
    Resolution,
    Compilation,
}

impl Display for ErrorKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            ErrorKind::Parse => write!(f, "Parsing Error"),
            ErrorKind::Type => write!(f, "Type Error"),
            ErrorKind::Resolution => write!(f, "Resolution Error"),
            ErrorKind::Compilation => write!(f, "Compiler Error"),
        }
    }
}

macro_rules! parse_error {
    ($span:expr, $($format:tt)*) => {
        $crate::error::CompilerError {
            msg: format!($($format)*),
            span: $span,
            backtrace: std::backtrace::Backtrace::capture(),
            kind: $crate::error::ErrorKind::Parse,
        }
    };
}

macro_rules! error {
    ($span:expr, $($format:tt)*) => {
        $crate::error::CompilerError {
            msg: format!($($format)*),
            span: $span,
            backtrace: std::backtrace::Backtrace::capture(),
            kind: $crate::error::ErrorKind::Compilation,
        }
    };
}

pub(crate) use error;
pub(crate) use parse_error;
