# extracting dependencies from the ast
import ast_visitor

class GenerateDependenciesAST(ast_visitor.ASTVisitor):
    def __init__(self):
        super(ast_visitor.ASTVisitor, self).__init__()
    def DefaultValue(self):
        return []
    def CombineValue(self, value1, value2):
        return value1 + value2

    def visitAtom(self, ctx):
        return [ ctx['package'] ]

def generate_dependencies_ast(ast_el):
    spl_name, local_ast, combined_ast = ast_el
    visitor = GenerateDependenciesAST()
    dependencies = visitor.visitDepend(combined_ast)
    return (spl_name, list(set(dependencies)))