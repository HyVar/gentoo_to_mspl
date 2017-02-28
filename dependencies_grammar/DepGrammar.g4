grammar DepGrammar;

// To generate files run antlr4 -Dlanguage=Python2 -visitor -no-listener

options { tokenVocab=DepGrammarLexer; }


///////////////////////////////////////////////////////////
// MAIN

localDEP: localDEPEL+ ;

localDEPEL:
    NOT? use                                    #localDEPatom
  | NOT? use_flag  LPAREN localDEPEL* RPAREN    #localDEPcondition
  | choice  LPAREN localDEPEL* RPAREN           #localDEPchoice
  | LPAREN localDEPEL* RPAREN                   #localDEPparen
  ;

depend: dependEL+ ;

dependEL:
    (NOT | BLOCK)? atom                         #dependELatom
  | NOT? use_flag LPAREN dependEL+ RPAREN       #dependELcondition
  | OR LPAREN dependEL* RPAREN                  #dependELor
  | LPAREN dependEL* RPAREN                     #dependELparen
  ;


use_flag: use IMPLIES;

choice: OR | ONEMAX | XOR;

///////////////////////////////////////////////////////////
// ATOM

atom:
    catpackage (COLON slotSPEC)? (LBRACKET selection_comma_list RBRACKET)?
  | versionOP catpackage TIMES? (COLON slotSPEC)? (LBRACKET selection_comma_list RBRACKET)?
  ;

selection_comma_list:
    selection (COMMA selection)* ;

slotSPEC: slot=slotID EQ | slot=slotID DIV subslot=PKG_SUBSLOT | slot=slotID |  EQ | TIMES  ;

versionOP: LEQ | LT | GT | GEQ | EQ | REV ;
catpackage: category DIV package;
category: Block ;
package: PKG_SUBSLOT ;
use: FLAG | Block ;
slotID: Block ;

selection: prefix? use preference? suffix? ;
prefix: PREFIX ;
preference: PREFERENCE ;
suffix: SUFFIX ;





