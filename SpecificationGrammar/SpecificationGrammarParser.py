# Generated from SpecificationGrammar.g4 by ANTLR 4.6
# encoding: utf-8
from __future__ import print_function
from antlr4 import *
from io import StringIO

def serializedATN():
    with StringIO() as buf:
        buf.write(u"\3\u0430\ud6d1\u8206\uad2d\u4417\uaef1\u8d80\uaadd\3")
        buf.write(u"\37R\4\2\t\2\4\3\t\3\4\4\t\4\4\5\t\5\4\6\t\6\4\7\t\7")
        buf.write(u"\4\b\t\b\4\t\t\t\4\n\t\n\3\2\3\2\3\2\3\2\3\2\3\2\3\2")
        buf.write(u"\3\2\5\2\35\n\2\3\3\3\3\3\3\3\4\3\4\3\4\7\4%\n\4\f\4")
        buf.write(u"\16\4(\13\4\3\5\5\5+\n\5\3\5\3\5\3\6\3\6\5\6\61\n\6\3")
        buf.write(u"\7\3\7\3\7\5\7\66\n\7\3\b\3\b\3\b\7\b;\n\b\f\b\16\b>")
        buf.write(u"\13\b\3\t\3\t\3\t\3\t\3\t\3\t\3\t\3\t\3\t\3\t\3\t\3\t")
        buf.write(u"\3\t\3\t\5\tN\n\t\3\n\3\n\3\n\2\2\13\2\4\6\b\n\f\16\20")
        buf.write(u"\22\2\7\3\2\21\22\4\2\t\13\17\20\3\2\24\31\3\2\32\34")
        buf.write(u"\3\2\r\16R\2\34\3\2\2\2\4\36\3\2\2\2\6!\3\2\2\2\b*\3")
        buf.write(u"\2\2\2\n\60\3\2\2\2\f\62\3\2\2\2\16\67\3\2\2\2\20M\3")
        buf.write(u"\2\2\2\22O\3\2\2\2\24\35\5\4\3\2\25\26\t\2\2\2\26\27")
        buf.write(u"\7\3\2\2\27\30\7\4\2\2\30\31\7\35\2\2\31\32\7\5\2\2\32")
        buf.write(u"\33\7\6\2\2\33\35\7\2\2\3\34\24\3\2\2\2\34\25\3\2\2\2")
        buf.write(u"\35\3\3\2\2\2\36\37\5\6\4\2\37 \7\2\2\3 \5\3\2\2\2!&")
        buf.write(u"\5\b\5\2\"#\t\3\2\2#%\5\b\5\2$\"\3\2\2\2%(\3\2\2\2&$")
        buf.write(u"\3\2\2\2&\'\3\2\2\2\'\7\3\2\2\2(&\3\2\2\2)+\7\f\2\2*")
        buf.write(u")\3\2\2\2*+\3\2\2\2+,\3\2\2\2,-\5\n\6\2-\t\3\2\2\2.\61")
        buf.write(u"\5\22\n\2/\61\5\f\7\2\60.\3\2\2\2\60/\3\2\2\2\61\13\3")
        buf.write(u"\2\2\2\62\65\5\16\b\2\63\64\t\4\2\2\64\66\5\16\b\2\65")
        buf.write(u"\63\3\2\2\2\65\66\3\2\2\2\66\r\3\2\2\2\67<\5\20\t\28")
        buf.write(u"9\t\5\2\29;\5\20\t\2:8\3\2\2\2;>\3\2\2\2<:\3\2\2\2<=")
        buf.write(u"\3\2\2\2=\17\3\2\2\2><\3\2\2\2?N\7\36\2\2@A\7\7\2\2A")
        buf.write(u"B\7\35\2\2BN\7\5\2\2CD\7\b\2\2DE\7\35\2\2EN\7\5\2\2F")
        buf.write(u"G\7\4\2\2GH\7\35\2\2HN\7\5\2\2IJ\7\3\2\2JK\5\6\4\2KL")
        buf.write(u"\7\6\2\2LN\3\2\2\2M?\3\2\2\2M@\3\2\2\2MC\3\2\2\2MF\3")
        buf.write(u"\2\2\2MI\3\2\2\2N\21\3\2\2\2OP\t\6\2\2P\23\3\2\2\2\t")
        buf.write(u"\34&*\60\65<M")
        return buf.getvalue()


class SpecificationGrammarParser ( Parser ):

    grammarFileName = "SpecificationGrammar.g4"

    atn = ATNDeserializer().deserialize(serializedATN())

    decisionsToDFA = [ DFA(ds, i) for i, ds in enumerate(atn.decisionToState) ]

    sharedContextCache = PredictionContextCache()

    literalNames = [ u"<INVALID>", u"'('", u"'attribute['", u"']'", u"')'", 
                     u"'context['", u"'feature['", u"'and'", u"'or'", u"'xor'", 
                     u"'not'", u"'true'", u"'false'", u"'impl'", u"'iff'", 
                     u"'min'", u"'max'", u"'abs'", u"'<='", u"'='", u"'>='", 
                     u"'<'", u"'>'", u"'!='", u"'+'", u"'-'", u"'*'" ]

    symbolicNames = [ u"<INVALID>", u"<INVALID>", u"<INVALID>", u"<INVALID>", 
                      u"<INVALID>", u"<INVALID>", u"<INVALID>", u"AND", 
                      u"OR", u"XOR", u"NOT", u"TRUE", u"FALSE", u"IMPL", 
                      u"IFF", u"MIN", u"MAX", u"ABS", u"LEQ", u"EQ", u"GEQ", 
                      u"LT", u"GT", u"NEQ", u"PLUS", u"MINUS", u"TIMES", 
                      u"ID", u"INT", u"WS" ]

    RULE_preference = 0
    RULE_constraint = 1
    RULE_b_expr = 2
    RULE_b_term = 3
    RULE_b_factor = 4
    RULE_relation = 5
    RULE_expr = 6
    RULE_term = 7
    RULE_boolFact = 8

    ruleNames =  [ u"preference", u"constraint", u"b_expr", u"b_term", u"b_factor", 
                   u"relation", u"expr", u"term", u"boolFact" ]

    EOF = Token.EOF
    T__0=1
    T__1=2
    T__2=3
    T__3=4
    T__4=5
    T__5=6
    AND=7
    OR=8
    XOR=9
    NOT=10
    TRUE=11
    FALSE=12
    IMPL=13
    IFF=14
    MIN=15
    MAX=16
    ABS=17
    LEQ=18
    EQ=19
    GEQ=20
    LT=21
    GT=22
    NEQ=23
    PLUS=24
    MINUS=25
    TIMES=26
    ID=27
    INT=28
    WS=29

    def __init__(self, input):
        super(SpecificationGrammarParser, self).__init__(input)
        self.checkVersion("4.6")
        self._interp = ParserATNSimulator(self, self.atn, self.decisionsToDFA, self.sharedContextCache)
        self._predicates = None



    class PreferenceContext(ParserRuleContext):

        def __init__(self, parser, parent=None, invokingState=-1):
            super(SpecificationGrammarParser.PreferenceContext, self).__init__(parent, invokingState)
            self.parser = parser


        def getRuleIndex(self):
            return SpecificationGrammarParser.RULE_preference

     
        def copyFrom(self, ctx):
            super(SpecificationGrammarParser.PreferenceContext, self).copyFrom(ctx)



    class ConstraintPreferenceContext(PreferenceContext):

        def __init__(self, parser, ctx): # actually a SpecificationGrammarParser.PreferenceContext)
            super(SpecificationGrammarParser.ConstraintPreferenceContext, self).__init__(parser)
            self.copyFrom(ctx)

        def constraint(self):
            return self.getTypedRuleContext(SpecificationGrammarParser.ConstraintContext,0)


        def accept(self, visitor):
            if hasattr(visitor, "visitConstraintPreference"):
                return visitor.visitConstraintPreference(self)
            else:
                return visitor.visitChildren(self)


    class MinMaxPreferenceContext(PreferenceContext):

        def __init__(self, parser, ctx): # actually a SpecificationGrammarParser.PreferenceContext)
            super(SpecificationGrammarParser.MinMaxPreferenceContext, self).__init__(parser)
            self.copyFrom(ctx)

        def ID(self):
            return self.getToken(SpecificationGrammarParser.ID, 0)
        def EOF(self):
            return self.getToken(SpecificationGrammarParser.EOF, 0)
        def MIN(self):
            return self.getToken(SpecificationGrammarParser.MIN, 0)
        def MAX(self):
            return self.getToken(SpecificationGrammarParser.MAX, 0)

        def accept(self, visitor):
            if hasattr(visitor, "visitMinMaxPreference"):
                return visitor.visitMinMaxPreference(self)
            else:
                return visitor.visitChildren(self)



    def preference(self):

        localctx = SpecificationGrammarParser.PreferenceContext(self, self._ctx, self.state)
        self.enterRule(localctx, 0, self.RULE_preference)
        self._la = 0 # Token type
        try:
            self.state = 26
            self._errHandler.sync(self)
            token = self._input.LA(1)
            if token in [SpecificationGrammarParser.T__0, SpecificationGrammarParser.T__1, SpecificationGrammarParser.T__4, SpecificationGrammarParser.T__5, SpecificationGrammarParser.NOT, SpecificationGrammarParser.TRUE, SpecificationGrammarParser.FALSE, SpecificationGrammarParser.INT]:
                localctx = SpecificationGrammarParser.ConstraintPreferenceContext(self, localctx)
                self.enterOuterAlt(localctx, 1)
                self.state = 18
                self.constraint()
                pass
            elif token in [SpecificationGrammarParser.MIN, SpecificationGrammarParser.MAX]:
                localctx = SpecificationGrammarParser.MinMaxPreferenceContext(self, localctx)
                self.enterOuterAlt(localctx, 2)
                self.state = 19
                _la = self._input.LA(1)
                if not(_la==SpecificationGrammarParser.MIN or _la==SpecificationGrammarParser.MAX):
                    self._errHandler.recoverInline(self)
                else:
                    self._errHandler.reportMatch(self)
                    self.consume()
                self.state = 20
                self.match(SpecificationGrammarParser.T__0)
                self.state = 21
                self.match(SpecificationGrammarParser.T__1)
                self.state = 22
                self.match(SpecificationGrammarParser.ID)
                self.state = 23
                self.match(SpecificationGrammarParser.T__2)
                self.state = 24
                self.match(SpecificationGrammarParser.T__3)
                self.state = 25
                self.match(SpecificationGrammarParser.EOF)
                pass
            else:
                raise NoViableAltException(self)

        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx

    class ConstraintContext(ParserRuleContext):

        def __init__(self, parser, parent=None, invokingState=-1):
            super(SpecificationGrammarParser.ConstraintContext, self).__init__(parent, invokingState)
            self.parser = parser

        def b_expr(self):
            return self.getTypedRuleContext(SpecificationGrammarParser.B_exprContext,0)


        def EOF(self):
            return self.getToken(SpecificationGrammarParser.EOF, 0)

        def getRuleIndex(self):
            return SpecificationGrammarParser.RULE_constraint

        def accept(self, visitor):
            if hasattr(visitor, "visitConstraint"):
                return visitor.visitConstraint(self)
            else:
                return visitor.visitChildren(self)




    def constraint(self):

        localctx = SpecificationGrammarParser.ConstraintContext(self, self._ctx, self.state)
        self.enterRule(localctx, 2, self.RULE_constraint)
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 28
            self.b_expr()
            self.state = 29
            self.match(SpecificationGrammarParser.EOF)
        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx

    class B_exprContext(ParserRuleContext):

        def __init__(self, parser, parent=None, invokingState=-1):
            super(SpecificationGrammarParser.B_exprContext, self).__init__(parent, invokingState)
            self.parser = parser

        def b_term(self, i=None):
            if i is None:
                return self.getTypedRuleContexts(SpecificationGrammarParser.B_termContext)
            else:
                return self.getTypedRuleContext(SpecificationGrammarParser.B_termContext,i)


        def AND(self, i=None):
            if i is None:
                return self.getTokens(SpecificationGrammarParser.AND)
            else:
                return self.getToken(SpecificationGrammarParser.AND, i)

        def OR(self, i=None):
            if i is None:
                return self.getTokens(SpecificationGrammarParser.OR)
            else:
                return self.getToken(SpecificationGrammarParser.OR, i)

        def IMPL(self, i=None):
            if i is None:
                return self.getTokens(SpecificationGrammarParser.IMPL)
            else:
                return self.getToken(SpecificationGrammarParser.IMPL, i)

        def IFF(self, i=None):
            if i is None:
                return self.getTokens(SpecificationGrammarParser.IFF)
            else:
                return self.getToken(SpecificationGrammarParser.IFF, i)

        def XOR(self, i=None):
            if i is None:
                return self.getTokens(SpecificationGrammarParser.XOR)
            else:
                return self.getToken(SpecificationGrammarParser.XOR, i)

        def getRuleIndex(self):
            return SpecificationGrammarParser.RULE_b_expr

        def accept(self, visitor):
            if hasattr(visitor, "visitB_expr"):
                return visitor.visitB_expr(self)
            else:
                return visitor.visitChildren(self)




    def b_expr(self):

        localctx = SpecificationGrammarParser.B_exprContext(self, self._ctx, self.state)
        self.enterRule(localctx, 4, self.RULE_b_expr)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 31
            self.b_term()
            self.state = 36
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while (((_la) & ~0x3f) == 0 and ((1 << _la) & ((1 << SpecificationGrammarParser.AND) | (1 << SpecificationGrammarParser.OR) | (1 << SpecificationGrammarParser.XOR) | (1 << SpecificationGrammarParser.IMPL) | (1 << SpecificationGrammarParser.IFF))) != 0):
                self.state = 32
                _la = self._input.LA(1)
                if not((((_la) & ~0x3f) == 0 and ((1 << _la) & ((1 << SpecificationGrammarParser.AND) | (1 << SpecificationGrammarParser.OR) | (1 << SpecificationGrammarParser.XOR) | (1 << SpecificationGrammarParser.IMPL) | (1 << SpecificationGrammarParser.IFF))) != 0)):
                    self._errHandler.recoverInline(self)
                else:
                    self._errHandler.reportMatch(self)
                    self.consume()
                self.state = 33
                self.b_term()
                self.state = 38
                self._errHandler.sync(self)
                _la = self._input.LA(1)

        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx

    class B_termContext(ParserRuleContext):

        def __init__(self, parser, parent=None, invokingState=-1):
            super(SpecificationGrammarParser.B_termContext, self).__init__(parent, invokingState)
            self.parser = parser

        def b_factor(self):
            return self.getTypedRuleContext(SpecificationGrammarParser.B_factorContext,0)


        def NOT(self):
            return self.getToken(SpecificationGrammarParser.NOT, 0)

        def getRuleIndex(self):
            return SpecificationGrammarParser.RULE_b_term

        def accept(self, visitor):
            if hasattr(visitor, "visitB_term"):
                return visitor.visitB_term(self)
            else:
                return visitor.visitChildren(self)




    def b_term(self):

        localctx = SpecificationGrammarParser.B_termContext(self, self._ctx, self.state)
        self.enterRule(localctx, 6, self.RULE_b_term)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 40
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            if _la==SpecificationGrammarParser.NOT:
                self.state = 39
                self.match(SpecificationGrammarParser.NOT)


            self.state = 42
            self.b_factor()
        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx

    class B_factorContext(ParserRuleContext):

        def __init__(self, parser, parent=None, invokingState=-1):
            super(SpecificationGrammarParser.B_factorContext, self).__init__(parent, invokingState)
            self.parser = parser

        def boolFact(self):
            return self.getTypedRuleContext(SpecificationGrammarParser.BoolFactContext,0)


        def relation(self):
            return self.getTypedRuleContext(SpecificationGrammarParser.RelationContext,0)


        def getRuleIndex(self):
            return SpecificationGrammarParser.RULE_b_factor

        def accept(self, visitor):
            if hasattr(visitor, "visitB_factor"):
                return visitor.visitB_factor(self)
            else:
                return visitor.visitChildren(self)




    def b_factor(self):

        localctx = SpecificationGrammarParser.B_factorContext(self, self._ctx, self.state)
        self.enterRule(localctx, 8, self.RULE_b_factor)
        try:
            self.state = 46
            self._errHandler.sync(self)
            token = self._input.LA(1)
            if token in [SpecificationGrammarParser.TRUE, SpecificationGrammarParser.FALSE]:
                self.enterOuterAlt(localctx, 1)
                self.state = 44
                self.boolFact()
                pass
            elif token in [SpecificationGrammarParser.T__0, SpecificationGrammarParser.T__1, SpecificationGrammarParser.T__4, SpecificationGrammarParser.T__5, SpecificationGrammarParser.INT]:
                self.enterOuterAlt(localctx, 2)
                self.state = 45
                self.relation()
                pass
            else:
                raise NoViableAltException(self)

        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx

    class RelationContext(ParserRuleContext):

        def __init__(self, parser, parent=None, invokingState=-1):
            super(SpecificationGrammarParser.RelationContext, self).__init__(parent, invokingState)
            self.parser = parser

        def expr(self, i=None):
            if i is None:
                return self.getTypedRuleContexts(SpecificationGrammarParser.ExprContext)
            else:
                return self.getTypedRuleContext(SpecificationGrammarParser.ExprContext,i)


        def LEQ(self):
            return self.getToken(SpecificationGrammarParser.LEQ, 0)

        def EQ(self):
            return self.getToken(SpecificationGrammarParser.EQ, 0)

        def GEQ(self):
            return self.getToken(SpecificationGrammarParser.GEQ, 0)

        def LT(self):
            return self.getToken(SpecificationGrammarParser.LT, 0)

        def GT(self):
            return self.getToken(SpecificationGrammarParser.GT, 0)

        def NEQ(self):
            return self.getToken(SpecificationGrammarParser.NEQ, 0)

        def getRuleIndex(self):
            return SpecificationGrammarParser.RULE_relation

        def accept(self, visitor):
            if hasattr(visitor, "visitRelation"):
                return visitor.visitRelation(self)
            else:
                return visitor.visitChildren(self)




    def relation(self):

        localctx = SpecificationGrammarParser.RelationContext(self, self._ctx, self.state)
        self.enterRule(localctx, 10, self.RULE_relation)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 48
            self.expr()
            self.state = 51
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            if (((_la) & ~0x3f) == 0 and ((1 << _la) & ((1 << SpecificationGrammarParser.LEQ) | (1 << SpecificationGrammarParser.EQ) | (1 << SpecificationGrammarParser.GEQ) | (1 << SpecificationGrammarParser.LT) | (1 << SpecificationGrammarParser.GT) | (1 << SpecificationGrammarParser.NEQ))) != 0):
                self.state = 49
                _la = self._input.LA(1)
                if not((((_la) & ~0x3f) == 0 and ((1 << _la) & ((1 << SpecificationGrammarParser.LEQ) | (1 << SpecificationGrammarParser.EQ) | (1 << SpecificationGrammarParser.GEQ) | (1 << SpecificationGrammarParser.LT) | (1 << SpecificationGrammarParser.GT) | (1 << SpecificationGrammarParser.NEQ))) != 0)):
                    self._errHandler.recoverInline(self)
                else:
                    self._errHandler.reportMatch(self)
                    self.consume()
                self.state = 50
                self.expr()


        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx

    class ExprContext(ParserRuleContext):

        def __init__(self, parser, parent=None, invokingState=-1):
            super(SpecificationGrammarParser.ExprContext, self).__init__(parent, invokingState)
            self.parser = parser

        def term(self, i=None):
            if i is None:
                return self.getTypedRuleContexts(SpecificationGrammarParser.TermContext)
            else:
                return self.getTypedRuleContext(SpecificationGrammarParser.TermContext,i)


        def PLUS(self, i=None):
            if i is None:
                return self.getTokens(SpecificationGrammarParser.PLUS)
            else:
                return self.getToken(SpecificationGrammarParser.PLUS, i)

        def MINUS(self, i=None):
            if i is None:
                return self.getTokens(SpecificationGrammarParser.MINUS)
            else:
                return self.getToken(SpecificationGrammarParser.MINUS, i)

        def TIMES(self, i=None):
            if i is None:
                return self.getTokens(SpecificationGrammarParser.TIMES)
            else:
                return self.getToken(SpecificationGrammarParser.TIMES, i)

        def getRuleIndex(self):
            return SpecificationGrammarParser.RULE_expr

        def accept(self, visitor):
            if hasattr(visitor, "visitExpr"):
                return visitor.visitExpr(self)
            else:
                return visitor.visitChildren(self)




    def expr(self):

        localctx = SpecificationGrammarParser.ExprContext(self, self._ctx, self.state)
        self.enterRule(localctx, 12, self.RULE_expr)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 53
            self.term()
            self.state = 58
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while (((_la) & ~0x3f) == 0 and ((1 << _la) & ((1 << SpecificationGrammarParser.PLUS) | (1 << SpecificationGrammarParser.MINUS) | (1 << SpecificationGrammarParser.TIMES))) != 0):
                self.state = 54
                _la = self._input.LA(1)
                if not((((_la) & ~0x3f) == 0 and ((1 << _la) & ((1 << SpecificationGrammarParser.PLUS) | (1 << SpecificationGrammarParser.MINUS) | (1 << SpecificationGrammarParser.TIMES))) != 0)):
                    self._errHandler.recoverInline(self)
                else:
                    self._errHandler.reportMatch(self)
                    self.consume()
                self.state = 55
                self.term()
                self.state = 60
                self._errHandler.sync(self)
                _la = self._input.LA(1)

        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx

    class TermContext(ParserRuleContext):

        def __init__(self, parser, parent=None, invokingState=-1):
            super(SpecificationGrammarParser.TermContext, self).__init__(parent, invokingState)
            self.parser = parser


        def getRuleIndex(self):
            return SpecificationGrammarParser.RULE_term

     
        def copyFrom(self, ctx):
            super(SpecificationGrammarParser.TermContext, self).copyFrom(ctx)



    class TermContextContext(TermContext):

        def __init__(self, parser, ctx): # actually a SpecificationGrammarParser.TermContext)
            super(SpecificationGrammarParser.TermContextContext, self).__init__(parser)
            self.copyFrom(ctx)

        def ID(self):
            return self.getToken(SpecificationGrammarParser.ID, 0)

        def accept(self, visitor):
            if hasattr(visitor, "visitTermContext"):
                return visitor.visitTermContext(self)
            else:
                return visitor.visitChildren(self)


    class TermFeatureContext(TermContext):

        def __init__(self, parser, ctx): # actually a SpecificationGrammarParser.TermContext)
            super(SpecificationGrammarParser.TermFeatureContext, self).__init__(parser)
            self.copyFrom(ctx)

        def ID(self):
            return self.getToken(SpecificationGrammarParser.ID, 0)

        def accept(self, visitor):
            if hasattr(visitor, "visitTermFeature"):
                return visitor.visitTermFeature(self)
            else:
                return visitor.visitChildren(self)


    class TermIntContext(TermContext):

        def __init__(self, parser, ctx): # actually a SpecificationGrammarParser.TermContext)
            super(SpecificationGrammarParser.TermIntContext, self).__init__(parser)
            self.copyFrom(ctx)

        def INT(self):
            return self.getToken(SpecificationGrammarParser.INT, 0)

        def accept(self, visitor):
            if hasattr(visitor, "visitTermInt"):
                return visitor.visitTermInt(self)
            else:
                return visitor.visitChildren(self)


    class TermBracketsContext(TermContext):

        def __init__(self, parser, ctx): # actually a SpecificationGrammarParser.TermContext)
            super(SpecificationGrammarParser.TermBracketsContext, self).__init__(parser)
            self.copyFrom(ctx)

        def b_expr(self):
            return self.getTypedRuleContext(SpecificationGrammarParser.B_exprContext,0)


        def accept(self, visitor):
            if hasattr(visitor, "visitTermBrackets"):
                return visitor.visitTermBrackets(self)
            else:
                return visitor.visitChildren(self)


    class TermAttributeContext(TermContext):

        def __init__(self, parser, ctx): # actually a SpecificationGrammarParser.TermContext)
            super(SpecificationGrammarParser.TermAttributeContext, self).__init__(parser)
            self.copyFrom(ctx)

        def ID(self):
            return self.getToken(SpecificationGrammarParser.ID, 0)

        def accept(self, visitor):
            if hasattr(visitor, "visitTermAttribute"):
                return visitor.visitTermAttribute(self)
            else:
                return visitor.visitChildren(self)



    def term(self):

        localctx = SpecificationGrammarParser.TermContext(self, self._ctx, self.state)
        self.enterRule(localctx, 14, self.RULE_term)
        try:
            self.state = 75
            self._errHandler.sync(self)
            token = self._input.LA(1)
            if token in [SpecificationGrammarParser.INT]:
                localctx = SpecificationGrammarParser.TermIntContext(self, localctx)
                self.enterOuterAlt(localctx, 1)
                self.state = 61
                self.match(SpecificationGrammarParser.INT)
                pass
            elif token in [SpecificationGrammarParser.T__4]:
                localctx = SpecificationGrammarParser.TermContextContext(self, localctx)
                self.enterOuterAlt(localctx, 2)
                self.state = 62
                self.match(SpecificationGrammarParser.T__4)
                self.state = 63
                self.match(SpecificationGrammarParser.ID)
                self.state = 64
                self.match(SpecificationGrammarParser.T__2)
                pass
            elif token in [SpecificationGrammarParser.T__5]:
                localctx = SpecificationGrammarParser.TermFeatureContext(self, localctx)
                self.enterOuterAlt(localctx, 3)
                self.state = 65
                self.match(SpecificationGrammarParser.T__5)
                self.state = 66
                self.match(SpecificationGrammarParser.ID)
                self.state = 67
                self.match(SpecificationGrammarParser.T__2)
                pass
            elif token in [SpecificationGrammarParser.T__1]:
                localctx = SpecificationGrammarParser.TermAttributeContext(self, localctx)
                self.enterOuterAlt(localctx, 4)
                self.state = 68
                self.match(SpecificationGrammarParser.T__1)
                self.state = 69
                self.match(SpecificationGrammarParser.ID)
                self.state = 70
                self.match(SpecificationGrammarParser.T__2)
                pass
            elif token in [SpecificationGrammarParser.T__0]:
                localctx = SpecificationGrammarParser.TermBracketsContext(self, localctx)
                self.enterOuterAlt(localctx, 5)
                self.state = 71
                self.match(SpecificationGrammarParser.T__0)
                self.state = 72
                self.b_expr()
                self.state = 73
                self.match(SpecificationGrammarParser.T__3)
                pass
            else:
                raise NoViableAltException(self)

        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx

    class BoolFactContext(ParserRuleContext):

        def __init__(self, parser, parent=None, invokingState=-1):
            super(SpecificationGrammarParser.BoolFactContext, self).__init__(parent, invokingState)
            self.parser = parser

        def TRUE(self):
            return self.getToken(SpecificationGrammarParser.TRUE, 0)

        def FALSE(self):
            return self.getToken(SpecificationGrammarParser.FALSE, 0)

        def getRuleIndex(self):
            return SpecificationGrammarParser.RULE_boolFact

        def accept(self, visitor):
            if hasattr(visitor, "visitBoolFact"):
                return visitor.visitBoolFact(self)
            else:
                return visitor.visitChildren(self)




    def boolFact(self):

        localctx = SpecificationGrammarParser.BoolFactContext(self, self._ctx, self.state)
        self.enterRule(localctx, 16, self.RULE_boolFact)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 77
            _la = self._input.LA(1)
            if not(_la==SpecificationGrammarParser.TRUE or _la==SpecificationGrammarParser.FALSE):
                self._errHandler.recoverInline(self)
            else:
                self._errHandler.reportMatch(self)
                self.consume()
        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx





