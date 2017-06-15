######################################################################
### FUNCTIONS TO PARSE THE CONSTRAINTS
######################################################################

from antlr4 import *
from antlr4.error.ErrorListener import ErrorListener
from grammar.DepGrammarLexer import DepGrammarLexer
from grammar.DepGrammarParser import DepGrammarParser
from grammar.DepGrammarVisitor import DepGrammarVisitor
import multiprocessing
import utils


class SPLParserErrorListener(ErrorListener):
    def __init__(self):
        super(ErrorListener, self).__init__()
        self.spl = None
        self.stage = None
        self.parsed_string = None
    def syntaxError(self, recognizer, offendingSymbol, line, column, msg, e):
        msg = "Parsing error in spl \"" + self.spl + "\" (stage " + self.stage + "): column " + str(column) + " " + msg + "\nSentence: " + self.parsed_string
        raise Exception(msg)


def SPLParserlocal(to_parse, syntax_error_listener):
    parser = __SPLParserparser(to_parse, syntax_error_listener)
    return parser.required()

def SPLParserexternal(to_parse, syntax_error_listener):
    parser = __SPLParserparser(to_parse, syntax_error_listener)
    return parser.depend()

def __SPLParserparser(to_parse, syntax_error_listener):
    lexer = DepGrammarLexer(InputStream(to_parse))
    lexer._listeners = [ syntax_error_listener ]
    parser = DepGrammarParser(CommonTokenStream(lexer))
    parser._listeners = [ syntax_error_listener ]
    return parser

class SPLParserTranslateConstraints(DepGrammarVisitor):
    """
    this class translates the ANTLR4 AST in our own AST
    """
    def __init__(self):
        super(DepGrammarVisitor, self).__init__()
    def visitRequired(self, ctx):
        return [child.accept(self) for child in ctx.requiredEL()]
    def visitRequiredSIMPLE(self, ctx):
        res = { 'type': "rsimple", 'use': ctx.ID().getText() }
        if ctx.NOT(): res['not'] = ctx.NOT().getText()
        return  res
    def visitRequiredCONDITION(self, ctx):
        return { 'type': "rcondition", 'condition': ctx.condition().accept(self), 'els': [ child.accept(self) for child in ctx.requiredEL() ] }
    def visitRequiredCHOICE(self, ctx):
        return {'type': "rchoice",
                'els': [child.accept(self) for child in ctx.requiredEL()],
                'choice': ctx.choice().accept(self)
                }
    def visitRequiredINNER(self, ctx):
        return { 'type': "rinner", 'els': [ child.accept(self) for child in ctx.requiredEL() ] }

    def visitDepend(self, ctx):
        return [ child.accept(self) for child in ctx.dependEL() ]
    def visitDependSIMPLE(self, ctx):
        res = { 'type': "dsimple", 'atom': ctx.atom().accept(self) }
        if ctx.NOT(): res['not'] = ctx.NOT()[0].getText()
        # hardblockers !! are treated as a single block !
        return res
    def visitDependCONDITION(self, ctx):
        return { 'type': "dcondition", 'condition': ctx.condition().accept(self), 'els': [ child.accept(self) for child in ctx.dependEL() ] }
    def visitDependCHOICE(self, ctx):
        return {'type': "dchoice",
                'els': [child.accept(self) for child in ctx.dependEL()],
                'choice': ctx.choice().accept(self)
                }
    def visitDependINNER(self, ctx):
        return { 'type': "dinner", 'els': [ child.accept(self) for child in ctx.dependEL() ] }

    def visitChoice(self, ctx):
        if ctx.OR(): return "or"
        if ctx.ONEMAX(): return "one-max"
        return "xor"
    def visitCondition(self, ctx):
        res = { 'type': "condition", 'use': ctx.ID().getText() }
        if ctx.NOT(): res['not'] = ctx.NOT().getText()
        return  res

    def visitAtom(self, ctx):
        res = {'type': "atom", 'package': ctx.ID(0).getText() + "/" + ctx.ID(1).getText() }
        if ctx.version_op(): res['version_op'] = ctx.version_op().accept(self)
        if ctx.TIMES(): res['times'] = ctx.TIMES().getText()
        if ctx.slot_spec(): res['slots'] = ctx.slot_spec().accept(self)
        if ctx.selection(): res['selection'] = [child.accept(self) for child in ctx.selection()]
        return res

    def visitVersion_op(self, ctx):
        if ctx.LEQ(): return "<="
        if ctx.LT(): return "<"
        if ctx.GT(): return ">"
        if ctx.GEQ(): return ">="
        if ctx.EQ(): return "="
        return "~"

    def visitSlotSIMPLE(self, ctx):
        return { 'type': "ssimple", 'slot': ctx.ID().getText() }
    def visitSlotFULL(self, ctx):
        return { 'type': "sfull", 'slot': ctx.ID(0).getText(), 'subslot': ctx.ID(1).getText() }
    def visitSlotEQ(self, ctx):
        res = { 'type': "seq" }
        if ctx.ID(): res['slot'] = ctx.ID().getText()
        return res
    def visitSlotSTAR(self, ctx):
        return { 'type': "sstar" }

    def visitSelection(self, ctx):
        res = { 'type': "selection", 'use': ctx.ID().getText() }
        if ctx.prefix(): res['prefix'] = ctx.prefix().accept(self)
        if ctx.preference(): res['default'] = ctx.preference().accept(self)
        if ctx.suffix(): res['suffix'] = ctx.suffix().accept(self)
        return res
    def visitPrefix(self, ctx):
        if ctx.NOT(): return '!'
        if ctx.MINUS(): return '-'
        if ctx.PLUS(): return '+'
        return ""
    def visitPreference(self, ctx):
        if ctx.MINUS(): return '-'
        if ctx.PLUS(): return '+'
    def visitSuffix(self, ctx):
        if ctx.IMPLIES(): return '?'
        if ctx.EQ(): return '='

ast_translator = SPLParserTranslateConstraints()

def parse_spl(spl):
    """
    this function translates the constraints into our AST, and simplifies them
    """
    # 1. create the error listener
    syntax_error_listener = SPLParserErrorListener()
    syntax_error_listener.spl = spl['name']

    # 2. parse the local constraint
    to_parse = spl['fm']['local']
    syntax_error_listener.stage = 'local'
    syntax_error_listener.parsed_string = to_parse
    local_ast = ast_translator.visitRequired(SPLParserlocal(to_parse, syntax_error_listener))

    # 3. parse the external constraints
    to_parse = spl['fm']['external']
    syntax_error_listener.stage = 'external'
    syntax_error_listener.parsed_string = to_parse
    external_ast = ast_translator.visitDepend(SPLParserexternal(to_parse, syntax_error_listener))

    # 3. parse the external constraints
    to_parse = spl['fm']['runtime']
    syntax_error_listener.stage = 'runtime'
    syntax_error_listener.parsed_string = to_parse
    runtime_ast = ast_translator.visitDepend(SPLParserexternal(to_parse, syntax_error_listener))

    # simplify the constraint
    local_ast = utils.compact_list(local_ast)
    #combined_ast = list(set(external_ast + runtime_ast))
    combined_ast = utils.compact_list(external_ast + runtime_ast)
    del spl['fm'] # try to save memory
    return (spl['name'], local_ast, combined_ast)


def parse_mspl(concurrent_map, raw_mspl):
    return concurrent_map(parse_spl, raw_mspl)