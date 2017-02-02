grammar DepGrammar;

// To generate files run antlr4 -Dlanguage=Python2 -visitor -no-listener

options { tokenVocab=DepGrammarLexer; }


///////////////////////////////////////////////////////////
// MAIN

required: requiredEL* ;

requiredEL:
    NOT? use                                          
  | condition LPAREN requiredEL* RPAREN   
  | choice LPAREN requiredEL* RPAREN                   
  | LPAREN requiredEL* RPAREN             
  ;

depend: dependEL* ;

dependEL:
    (NOT | BLOCK)? atom                                          
  | condition LPAREN dependEL* RPAREN   
  | choice LPAREN dependEL* RPAREN                   
  | LPAREN dependEL* RPAREN             
  ;

choice: OR | ONEMAX | XOR ;

condition: NOT? use (LBRACE conditionAttribute* RBRACE)? IMPLIES;
conditionAttribute: attribute=use conditionOP value ;
conditionOP: LEQ | LT | GT | GEQ | EQ | NEQ ;

use: (ABlock | SBlock) ( (MINUS | AT)? (ABlock | SBlock))*;
value: (ABlock | SBlock | VBlock) (MINUS (ABlock | SBlock | VBlock))*;

///////////////////////////////////////////////////////////
// ATOM

atom:
    catpackage (COLON slotSPEC)? (LBRACKET selection (COMMA selection)* RBRACKET)?
  | versionOP catpackage MINUS version (COLON slotSPEC)? (LBRACKET selection (COMMA selection)* RBRACKET)?
  ;

versionOP: LEQ | LT | GT | GEQ | EQ | NEQ | REV ;
catpackage: category DIV package;
category: (ABlock | SBlock) (MINUS (ABlock | SBlock))* ;
package: ( (ABlock MINUS) | (SBlock MINUS?) )* ABlock;
version: (SBlock | VBlock) TIMES?;

slotSPEC: slot=slotID | slot=slotID DIV subslot=slotID | EQ | TIMES | slot=slotID EQ ;
slotID: (ABlock | SBlock | VBlock) (MINUS (ABlock | SBlock | VBlock))* ;

selection: prefix? use preference? suffix? ;
prefix: NOT | MINUS | PLUS ;
preference: LPAREN (PLUS | MINUS) RPAREN ;
suffix: IMPLIES | EQ ;





