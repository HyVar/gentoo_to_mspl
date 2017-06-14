grammar DepGrammar;

// To generate files run: antlr4 -Dlanguage=Python2 -visitor -no-listener DepGrammar.g4

options { tokenVocab=DepGrammarLexer; }


///////////////////////////////////////////////////////////
// MAIN

required: requiredEL? (SPACE+ requiredEL)* ;

requiredEL:
    NOT? SPACE* use=ID                                       #requiredSIMPLE
  | condition SPACE* LPAREN requiredEL? (SPACE+ requiredEL)* SPACE* RPAREN               #requiredCONDITION
  | choice SPACE* LPAREN requiredEL? (SPACE+ requiredEL)* SPACE* RPAREN                  #requiredCHOICE
  | LPAREN requiredEL? (SPACE+ requiredEL)* SPACE* RPAREN                         #requiredINNER
  ;

depend: dependEL? (SPACE+ dependEL)* ;

dependEL:
    (NOT NOT?)? SPACE* atom                               #dependSIMPLE
  | condition SPACE* LPAREN dependEL? (SPACE+ dependEL)* SPACE* RPAREN                 #dependCONDITION
  | choice SPACE* LPAREN dependEL? (SPACE+ dependEL)* SPACE* RPAREN                    #dependCHOICE
  | LPAREN dependEL? (SPACE+ dependEL)* SPACE* RPAREN                           #dependINNER
  ;

choice: OR | ONEMAX | XOR ;
condition: NOT? use=ID IMPLIES;

atom:
  version_op? category=ID DIV package=ID TIMES? (COLON slot_spec)? (LBRACKET SPACE* selection (SPACE* COMMA SPACE* selection)* SPACE* RBRACKET)?
  ;

// != is not needed since the ! is matched in dependSIMPLE
version_op: LEQ | LT | GT | GEQ | EQ | REV ;



slot_spec:
    slot=ID                                   #slotSIMPLE
  | slot=ID DIV subslot=ID                    #slotFULL
  // why is there a ? for the id?
  | slot=ID? EQ                               #slotEQ
  | TIMES                                     #slotSTAR
  ;

selection: prefix? use=ID preference? suffix? ;
prefix: NOT | MINUS | PLUS ;
preference: LPAREN (PLUS | MINUS) RPAREN ;
suffix: IMPLIES | EQ ;





