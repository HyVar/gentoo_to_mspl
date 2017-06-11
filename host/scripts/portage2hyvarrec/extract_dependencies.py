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

# note: this function is called also by reconfigure.py
def generate_dependencies_ast(input_tuple):
    pkg_name,ast,mspl,pkg_names = input_tuple
    visitor = GenerateDependenciesAST()
    dependencies = set(visitor.visitDepend(ast))
    # consider only the dependencies that we are aware of
    dependencies.intersection_update(pkg_names)
    # add dependency to the base package too
    dependencies.add(mspl[pkg_name]["group_name"])
    return (pkg_name, dependencies)