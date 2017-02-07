lexer grammar DepGrammarLexer;

// To generate files run antlr4 -Dlanguage=Python2 -no-listener

fragment ALPHA: [a-zA-Z] ;  // '@' is in the name of some features...
fragment NUM: [0-9] ;

WS: [ \t\r\n]+ -> skip ;

///////////////////////////////////////////////////////////
// mode: default:

// logic operators
OR: '||' ;
XOR: '^^' ;
ONEMAX: '??' ;

NOT: '!';
BLOCK: '!!';

IMPLIES: '?';


// version operators

LEQ : '<=' ;
EQ : '='   ;
GEQ : '>=' ;
LT : '<'   ;
GT : '>'   ;
// michael extended version NEQ : '!=' ;
REV: '~'   ;


// special symbols

LPAREN  : '(' ;
RPAREN  : ')' ;
LBRACKET: '[' ;
RBRACKET: ']' ;
LBRACE  : '{' ;
RBRACE  : '}' ;

PLUS  : '+' ;
MINUS : '-' ;
TIMES : '*' ;
DIV   : '/' ;
COLON : ':' ;
COMMA : ',' ;
DOT   : '.' ;
UNDERSCORE: '_' ;
AT    : '@' ;


// identifiers
// Valid package names: [a-zA-Z0-9'-'_+] "that does not end with a version..."
// valid version names: [0-9]+('.'[0-9]+)*[a-zA-Z]?( ('_alpha' | '_beta' | '_pre' | '_rc' | '_p') ([1-9][0-9]*)? )* ('-r' [0-9]+)?
// the intersection between package names and version names is [0-9]+[a-zA-Z]?( ('_alpha' | '_beta' | '_pre' | '_rc' | '_p') ([1-9][0-9]*)? )* ('-r' [0-9]+)?

SBlock: [0-9]+[a-zA-Z]?( ('_alpha' | '_beta' | '_pre' | '_rc' | '_p') [0-9]* )* ('-r' [0-9]+)? ;
VBlock: [0-9]+('.'[0-9]+)*[a-zA-Z]?( ('_alpha' | '_beta' | '_pre' | '_rc' | '_p') [0-9]* )* ('-r' [0-9]+)? ;
ABlock: [a-zA-Z_+] [a-zA-Z0-9_+]* ;

//ABlock: (ALPHA | (NUM+ ALPHA ALPHA)) (ALPHA | NUM | PLUS | UNDERSCORE)* | ; // not enough: sys-firmware/tt-s2-6400-firmware
//NBlock: NUM (ALPHA | NUM | PLUS | DOT | UNDERSCORE)*;

//ABlock: ALPHA (ALPHA | NUM | PLUS| DOT | UNDERSCORE)*;
//NBlock: NUM (ALPHA | NUM | PLUS| DOT | UNDERSCORE)*;





