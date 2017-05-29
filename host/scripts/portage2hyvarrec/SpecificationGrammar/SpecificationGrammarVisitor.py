# Generated from SpecificationGrammar.g4 by ANTLR 4.6
from antlr4 import *

# This class defines a complete generic visitor for a parse tree produced by SpecificationGrammarParser.

class SpecificationGrammarVisitor(ParseTreeVisitor):

    # Visit a parse tree produced by SpecificationGrammarParser#constraintPreference.
    def visitConstraintPreference(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SpecificationGrammarParser#minMaxPreference.
    def visitMinMaxPreference(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SpecificationGrammarParser#constraint.
    def visitConstraint(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SpecificationGrammarParser#b_expr.
    def visitB_expr(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SpecificationGrammarParser#b_term.
    def visitB_term(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SpecificationGrammarParser#b_factor.
    def visitB_factor(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SpecificationGrammarParser#relation.
    def visitRelation(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SpecificationGrammarParser#expr.
    def visitExpr(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SpecificationGrammarParser#termInt.
    def visitTermInt(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SpecificationGrammarParser#termContext.
    def visitTermContext(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SpecificationGrammarParser#termFeature.
    def visitTermFeature(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SpecificationGrammarParser#termAttribute.
    def visitTermAttribute(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SpecificationGrammarParser#termBrackets.
    def visitTermBrackets(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by SpecificationGrammarParser#boolFact.
    def visitBoolFact(self, ctx):
        return self.visitChildren(ctx)


