grammar SpecificationGrammar;

// To generate files run antlr4 -Dlanguage=Python2 -visitor -no-listener

preference:
  constraint                                 #constraintPreference |
  (MIN | MAX) '(' 'attribute[' ID ']' ')' EOF          #minMaxPreference;
 
 
constraint : b_expr EOF;

b_expr : b_term ( (AND | OR | IMPL | IFF | XOR) b_term )* ;

b_term : (NOT)? b_factor ;

b_factor : boolFact | relation ;

relation : expr ((LEQ | EQ | GEQ | LT | GT | NEQ) expr)? ;

expr : term ((PLUS | MINUS | TIMES) term)* ;

term :
  INT                       #termInt |
  'context[' ID ']'                 #termContext |
  'feature[' ID ']'                  #termFeature |
  'attribute[' ID ']'                 #termAttribute |
  '(' b_expr ')'            #termBrackets;


boolFact : TRUE | FALSE;


AND : 'and';
OR : 'or';
XOR : 'xor';
NOT : 'not';
TRUE : 'true';
FALSE : 'false';
IMPL: 'impl';
IFF: 'iff';
MIN: 'min';
MAX: 'max';
ABS: 'abs';

LEQ : '<=';
EQ : '=';
GEQ : '>=';
LT : '<';
GT : '>';
NEQ : '!=';

PLUS : '+';
MINUS : '-';
TIMES : '*';

ID : [a-zA-Z_][-a-zA-Z0-9_]* ;    // match letters, numbers, underscore
INT : [-]?[0-9]+ ;
WS : [ \t\r\n]+ -> skip ; // skip spaces, tabs, newlines
