grammar Bosco;

LET: 'let';
VAR: 'var';
TRUE: 'true';
FALSE: 'false';
EQUALS: '=';
MINUS: '-';

IDENTIFIER: ('_' | LETTER) ('_' | LETTER | DIGIT)*;
COMMENT: '/*' .*? '*/' -> skip;
LINE_COMMENT: '//' ~[\n]* '\n' -> skip;
WHITESPACE: [ \t\r] -> skip;
EOS: '\n' | ';';

DECIMAL_LITERAL
    : '0'
    | [1-9]+ ((DIGIT | '_')* DIGIT+)?;

HEX_LITERAL:        '0' [xX] [0-9a-fA-F] ([0-9a-fA-F_]* [0-9a-fA-F])?;
OCT_LITERAL:        '0' [oO] [0-7] ([0-7_]* [0-7])? [lL]?;
BINARY_LITERAL:     '0' [bB] [01] ([01_]* [01])? [lL]?;

fragment DIGIT: [0-9];
fragment LETTER: [\p{L}];


//program: varDeclaration (EOS varDeclaration)* EOF;

program: expression (EOS expression)* EOF;

varDeclaration:
    (LET | VAR) IDENTIFIER typeAnnotation? EQUALS expression;

typeAnnotation: IDENTIFIER;

expression: atomExpression;

atomExpression
    : numExpression
    | boolExpression;

boolExpression: TRUE | FALSE;
numExpression: DECIMAL_LITERAL;
