lexer grammar DepGrammarLexer;


fragment SPACE: [ \t\r\n]+ ;
WS: SPACE -> skip ;

///////////////////////////////////////////////////////////
// mode: default:

// logic operators
OR    : '||' ;
XOR   : '^^' ;
ONEMAX: '??' ;

NOT  : '!';
BLOCK: '!!';

IMPLIES: '?';


// version operators

LEQ : '<=' ;
EQ  : '='  ;
GEQ : '>=' ;
LT  : '<'  ;
GT  : '>'  ;
NEQ : '!=' ;
REV : '~'  ;


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

// simplified identifiers
ID    : [a-zA-Z0-9._@][a-zA-Z0-9._'-'+@]*;


// identifiers
// Valid package names: [a-zA-Z0-9'-'_+] "that does not end with a version..."
// valid version names: [0-9]+('.'[0-9]+)*[a-zA-Z]?( ('_alpha' | '_beta' | '_pre' | '_rc' | '_p') ([1-9][0-9]*)? )* ('-r' [0-9]+)?
// the intersection between package names and version names is [0-9]+[a-zA-Z]?( ('_alpha' | '_beta' | '_pre' | '_rc' | '_p') ([1-9][0-9]*)? )* ('-r' [0-9]+)?
