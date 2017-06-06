lexer grammar DepGrammarLexer;

// To generate files run: antlr4 -Dlanguage=Python2 -no-listener DepGrammarLexer.g4

fragment SPECIAL_CHAR: ('-'|'_'|'+'|'.');
fragment NUM: [0-9];
fragment LETTER: [a-zA-Z];

// logic operators
OR: '||' ;
XOR: '^^' ;
ONEMAX: '??' ;

BLOCK: '!!';
NOT: '!';

IMPLIES: '?';

// version operators

LEQ : '<=' ;
GEQ : '>=' ;
EQ : '='   ;
LT : '<'   ;
GT : '>'   ;
REV: '~'   ;

// special symbols

LPAREN  : '(' ;
RPAREN  : ')' ;
LBRACKET: '[' -> pushMode(BRACKET_MODE);
LBRACE  : '{' ;
RBRACE  : '}' ;

MINUS : '-' ;
TIMES : '*' ;
DIV   : '/' -> pushMode(NO_DIV_MODE);
COLON : ':' ;
DOT   : '.' ;
UNDERSCORE: '_' ;
AT    : '@' ;

// identifiers
Block : [a-zA-Z0-9]([a-zA-Z0-9]|SPECIAL_CHAR)* ;

WS: [ \t\r\n]+ -> skip ;

// tokens inside a square braket
mode BRACKET_MODE;

COMMA : ',' ;
RBRACKET: ']' -> mode(DEFAULT_MODE) ;
PREFIX  : '!' | '-' | '+' ;
PREFERENCE: '(+)' | '(-)';
SUFFIX: '?'|'=';

FLAG: [a-zA-Z0-9]('.'|'-'|[a-zA-Z0-9_])*;

// tokens after a div
mode NO_DIV_MODE;

// Some packages are written in sequence without any space to delimit them
// In these cases the last number is consider as a delimitator of the package version
PKG_SUBSLOT : ([a-zA-Z0-9]([a-zA-Z0-9]|SPECIAL_CHAR)*([ ]|EOF) |
    [a-zA-Z0-9]([a-zA-Z0-9]|SPECIAL_CHAR)*
        { self._input.LA(1) in [ord(x) for x in ":*[?=!"] }? |
    [a-zA-Z0-9]([a-zA-Z0-9]|SPECIAL_CHAR)*NUM+) -> mode(DEFAULT_MODE);


