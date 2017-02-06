# Generated from DepGrammar.g4 by ANTLR 4.6
from antlr4 import *

# This class defines a complete generic visitor for a parse tree produced by DepGrammarParser.

class DepGrammarVisitor(ParseTreeVisitor):

    # Visit a parse tree produced by DepGrammarParser#required.
    def visitRequired(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by DepGrammarParser#requiredEL.
    def visitRequiredEL(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by DepGrammarParser#depend.
    def visitDepend(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by DepGrammarParser#dependELatom.
    def visitDependELatom(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by DepGrammarParser#dependELcondition.
    def visitDependELcondition(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by DepGrammarParser#dependELor.
    def visitDependELor(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by DepGrammarParser#dependELxor_or_max.
    def visitDependELxor_or_max(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by DepGrammarParser#dependELparen.
    def visitDependELparen(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by DepGrammarParser#use_flag.
    def visitUse_flag(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by DepGrammarParser#conditionAttribute.
    def visitConditionAttribute(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by DepGrammarParser#conditionOP.
    def visitConditionOP(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by DepGrammarParser#choice.
    def visitChoice(self, ctx):
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


    # Visit a parse tree produced by DepGrammarParser#selection_comma_list.
    def visitSelection_comma_list(self, ctx):
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


    # Visit a parse tree produced by DepGrammarParser#slotSPEC.
    def visitSlotSPEC(self, ctx):
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


