grammar Bosco;

LET: 'let';
VAR: 'var';
EQUALS: '=';

IDENTIFIER: ('_' | LETTER) ('_' | LETTER | DIGIT)*;
COMMENT: '/*' .*? '*/' -> skip;
LINE_COMMENT: '//' ~[\n]* '\n' -> skip;
WHITESPACE: [ \t\r] -> skip;
EOS: '\n' | ';';

fragment DIGIT: [\p{Nd}];
fragment LETTER: [\p{L}];

program: varDeclaration (EOS varDeclaration)* EOF;
varDeclaration: (LET | VAR) IDENTIFIER typeAnnotation?;
typeAnnotation: IDENTIFIER;