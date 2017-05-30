# Generated from DepGrammar.g4 by ANTLR 4.6
from antlr4 import *

# This class defines a complete generic visitor for a parse tree produced by DepGrammarParser.

class DepGrammarVisitor(ParseTreeVisitor):

    # Visit a parse tree produced by DepGrammarParser#required.
    def visitRequired(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by DepGrammarParser#requiredSIMPLE.
    def visitRequiredSIMPLE(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by DepGrammarParser#requiredCONDITION.
    def visitRequiredCONDITION(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by DepGrammarParser#requiredCHOICE.
    def visitRequiredCHOICE(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by DepGrammarParser#requiredINNER.
    def visitRequiredINNER(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by DepGrammarParser#depend.
    def visitDepend(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by DepGrammarParser#dependSIMPLE.
    def visitDependSIMPLE(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by DepGrammarParser#dependCONDITION.
    def visitDependCONDITION(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by DepGrammarParser#dependCHOICE.
    def visitDependCHOICE(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by DepGrammarParser#dependINNER.
    def visitDependINNER(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by DepGrammarParser#choice.
    def visitChoice(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by DepGrammarParser#condition.
    def visitCondition(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by DepGrammarParser#conditionAttribute.
    def visitConditionAttribute(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by DepGrammarParser#conditionOP.
    def visitConditionOP(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by DepGrammarParser#use.
    def visitUse(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by DepGrammarParser#value.
    def visitValue(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by DepGrammarParser#atom.
    def visitAtom(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by DepGrammarParser#versionOP.
    def visitVersionOP(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by DepGrammarParser#catpackage.
    def visitCatpackage(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by DepGrammarParser#category.
    def visitCategory(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by DepGrammarParser#package.
    def visitPackage(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by DepGrammarParser#version.
    def visitVersion(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by DepGrammarParser#slotSIMPLE.
    def visitSlotSIMPLE(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by DepGrammarParser#slotFULL.
    def visitSlotFULL(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by DepGrammarParser#slotEQ.
    def visitSlotEQ(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by DepGrammarParser#slotSTAR.
    def visitSlotSTAR(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by DepGrammarParser#slotSIMPLEEQ.
    def visitSlotSIMPLEEQ(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by DepGrammarParser#slotID.
    def visitSlotID(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by DepGrammarParser#selection.
    def visitSelection(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by DepGrammarParser#prefix.
    def visitPrefix(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by DepGrammarParser#preference.
    def visitPreference(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by DepGrammarParser#suffix.
    def visitSuffix(self, ctx):
        return self.visitChildren(ctx)


