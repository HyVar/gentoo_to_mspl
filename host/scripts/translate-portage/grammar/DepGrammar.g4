grammar DepGrammar;


options { tokenVocab=DepGrammarLexer; }


///////////////////////////////////////////////////////////
// MAIN

required: requiredEL* ;

requiredEL:
    NOT? use                                          #requiredSIMPLE
  | condition LPAREN requiredEL* RPAREN               #requiredCONDITION
  | choice LPAREN requiredEL* RPAREN                  #requiredCHOICE
  | LPAREN requiredEL* RPAREN                         #requiredINNER
  ;

depend: dependEL* ;

dependEL:
    (NOT | BLOCK)? atom                               #dependSIMPLE
  | condition LPAREN dependEL* RPAREN                 #dependCONDITION
  | choice LPAREN dependEL* RPAREN                    #dependCHOICE
  | LPAREN dependEL* RPAREN                           #dependINNER
  ;

choice: OR | ONEMAX | XOR ;

condition: NOT? use (LBRACE conditionAttribute* RBRACE)? IMPLIES;
conditionAttribute: attribute=use conditionOP value ;
conditionOP: LEQ | LT | GT | GEQ | EQ | NEQ ;

use: (ABlock | SBlock) ( (MINUS | AT)? (CM_ABlock | CM_SBlock))*;
value: (ABlock | SBlock | VBlock) (MINUS (CM_ABlock | CM_SBlock | CM_VBlock))*;

///////////////////////////////////////////////////////////
// ATOM

atom:
    catpackage (COLON slotSPEC)? (LBRACKET selection (COMMA selection)* RBRACKET)?
  | versionOP catpackage MINUS version (COLON slotSPEC)? (LBRACKET selection (COMMA selection)* RBRACKET)?
  ;

versionOP: LEQ | LT | GT | GEQ | EQ | NEQ | REV ;
catpackage: category DIV package;
category: (ABlock | SBlock) (MINUS (CM_ABlock | CM_SBlock))* ;
package: ABlock | ( (ABlock MINUS) | (SBlock MINUS?) ) ( (CM_ABlock MINUS) | (CM_SBlock MINUS?) )* CM_ABlock;
version: (CM_SBlock | CM_VBlock) TIMES?;

slotSPEC:
    slot=slotID                                       #slotSIMPLE
  | slot=slotID DIV subslot=slotID                    #slotFULL
  | EQ                                                #slotEQ
  | TIMES                                             #slotSTAR
  | slot=slotID EQ                                    #slotSIMPLEEQ
  ;
slotID: (ABlock | SBlock | VBlock) (MINUS (CM_ABlock | CM_SBlock | CM_VBlock))* ;

selection: prefix? use preference? suffix? ;
prefix: NOT | MINUS | PLUS ;
preference: LPAREN (PLUS | MINUS) RPAREN ;
suffix: IMPLIES | EQ ;





