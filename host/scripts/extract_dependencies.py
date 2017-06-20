# extracting dependencies from the ast
import constraint_ast_visitor

class GenerateDependenciesAST(constraint_ast_visitor.ASTVisitor):
    def __init__(self):
        super(constraint_ast_visitor.ASTVisitor, self).__init__()
    def DefaultValue(self):
        return []
    def CombineValue(self, value1, value2):
        return value1 + value2

    def visitAtom(self, ctx):
        return [ ctx['package'] ]

visitor = GenerateDependenciesAST()

def generate_dependencies_ast(parameter):
    spl, pkg_names = parameter
    dependencies = set(visitor.visitDepend(spl['fm']['combined']))
    # consider only the dependencies that we are aware of
    dependencies.intersection_update(pkg_names) # should not be necessary
    # add dependency to the base package too
    dependencies.add(spl['group_name'])
    spl['dependencies'] = dependencies

def generate_dependencies_mspl(concurrent_map, mspl):
    concurrent_map(generate_dependencies_ast, [ (spl, mspl.keys()) for spl in mspl.values() ])
