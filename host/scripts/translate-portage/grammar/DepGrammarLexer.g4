lexer grammar DepGrammarLexer;


fragment ALPHA: [a-zA-Z] ;  // '@' is in the name of some features...
fragment NUM: [0-9] ;
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
//DOT   : '.' ;
AT    : '@' ;
//UNDERSCORE: '_' ;


// identifiers
// Valid package names: [a-zA-Z0-9'-'_+] "that does not end with a version..."
// valid version names: [0-9]+('.'[0-9]+)*[a-zA-Z]?( ('_alpha' | '_beta' | '_pre' | '_rc' | '_p') ([1-9][0-9]*)? )* ('-r' [0-9]+)?
// the intersection between package names and version names is [0-9]+[a-zA-Z]?( ('_alpha' | '_beta' | '_pre' | '_rc' | '_p') ([1-9][0-9]*)? )* ('-r' [0-9]+)?

SBlock: [0-9]+[a-zA-Z]?( ('_alpha' | '_beta' | '_pre' | '_rc' | '_p') [0-9]* )* ('-r' [0-9]+)?             -> pushMode(CONTINUATION_MODE) ;
VBlock: [0-9]+('.'[0-9]+)*[a-zA-Z]?( ('_alpha' | '_beta' | '_pre' | '_rc' | '_p') [0-9]* )* ('-r' [0-9]+)? -> pushMode(CONTINUATION_MODE) ;
ABlock: [a-zA-Z_+] [a-zA-Z0-9_+]*                                                                          -> pushMode(CONTINUATION_MODE) ;


mode CONTINUATION_MODE ; // copie of the default mode... It seems from stackoverflow that there is no better option :-(

CONTINUATION_MODE_WS: SPACE -> skip, popMode ;

CONTINUATION_MODE_OR    : '||'  -> type(OR), popMode;
CONTINUATION_MODE_XOR   : '^^'  -> type(XOR), popMode;
CONTINUATION_MODE_ONEMAX: '??'  -> type(ONEMAX), popMode;

CONTINUATION_MODE_NOT  : '!'  -> type(NOT), popMode;
CONTINUATION_MODE_BLOCK: '!!'  -> type(BLOCK), popMode;

CONTINUATION_MODE_IMPLIES : '?' -> type(IMPLIES), popMode;

CONTINUATION_MODE_LEQ : '<=' -> type(LEQ), popMode;
CONTINUATION_MODE_EQ  : '='  -> type(EQ), popMode;
CONTINUATION_MODE_GEQ : '>=' -> type(GEQ), popMode;
CONTINUATION_MODE_LT  : '<'  -> type(LT), popMode;
CONTINUATION_MODE_GT  : '>'  -> type(GT), popMode;
CONTINUATION_MODE_NEQ : '!=' -> type(NEQ), popMode;
CONTINUATION_MODE_REV : '~'  -> type(REV), popMode;

CONTINUATION_MODE_LPAREN  : '(' -> type(LPAREN), popMode;
CONTINUATION_MODE_RPAREN  : ')' -> type(RPAREN), popMode;
CONTINUATION_MODE_LBRACKET: '[' -> type(LBRACKET), popMode;
CONTINUATION_MODE_RBRACKET: ']' -> type(RBRACKET), popMode;
CONTINUATION_MODE_LBRACE  : '{' -> type(LBRACE), popMode;
CONTINUATION_MODE_RBRACE  : '}' -> type(RBRACE), popMode;


CONTINUATION_MODE_PLUS  : '+' -> type(PLUS), popMode;
CONTINUATION_MODE_MINUS : '-' -> type(MINUS);
CONTINUATION_MODE_TIMES : '*' -> type(TIMES), popMode;
CONTINUATION_MODE_DIV   : '/' -> type(DIV), popMode;
CONTINUATION_MODE_COLON : ':' -> type(COLON), popMode;
CONTINUATION_MODE_COMMA : ',' -> type(COMMA), popMode;
//CONTINUATION_MODE_DOT   : '.' -> type(DOT), popMode;
CONTINUATION_MODE_AT    : '@' -> type(AT);
//CONTINUATION_MODE_UNDERSCORE: '_' -> type(UNDERSCORE);


CM_SBlock: [0-9]+[a-zA-Z]?( ('_alpha' | '_beta' | '_pre' | '_rc' | '_p') [0-9]* )* ('-r' [0-9]+)?             ;
CM_VBlock: [0-9]+('.'[0-9]+)*[a-zA-Z]?( ('_alpha' | '_beta' | '_pre' | '_rc' | '_p') [0-9]* )* ('-r' [0-9]+)? ;
CM_ABlock: [a-zA-Z_+] [a-zA-Z0-9_+]*                                                                          ;





