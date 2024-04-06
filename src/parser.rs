use crate::lexer::Lexer;

enum NodeType {
    BinaryExpression,
    Literal,
    Error
}

struct Parser<'source> {
    lexer: Lexer<'source>,
}