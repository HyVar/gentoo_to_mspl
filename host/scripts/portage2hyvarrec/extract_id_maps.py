######################################################################
### FUNCTIONS TO GET THE INFORMATION FROM THE MSPL
######################################################################

import utils
import constraint_ast_visitor

trust_feature_declaration = False

def create_empty_name_mappings():
    return ( { } , {'package': {}, 'flag': {}, 'slot': {}, 'subslot': {}, 'context': {}} )
def create_name_mappings(spl_name):
    new_id = utils.new_id()
    return ( {new_id: {'type': 'package', 'name': spl_name} } ,
        {'package': {spl_name: new_id}, 'flag': {spl_name:{}}, 'slot': {spl_name:{}}, 'subslot': {spl_name:{}}, 'context': {}} )


# extracting name mapping from the spl
def update_mappings(mappings, kind, spl_name, name):
    map_id_name, map_name_id = mappings
    new_id = utils.new_id()
    map_name_id[kind][spl_name][name] = new_id
    map_id_name[new_id] = {'type': kind, 'name': name, 'package': spl_name}
def update_mappings_context(mappings, name):
    map_id_name, map_name_id = mappings
    new_id = utils.new_id()
    map_name_id['context'][name] = new_id
    map_id_name[new_id] = {'type': "context", 'name': name}

def generate_name_mappings_spl(spl):
    spl_name = spl['name']
    mappings = create_name_mappings(spl_name)
    global trust_feature_declaration
    if trust_feature_declaration:
        for use in spl['features']:
            update_mappings(mappings, 'flag', spl_name, use)
    update_mappings(mappings, 'slot', spl_name, spl['slot'])
    update_mappings(mappings, 'subslot', spl_name, spl['subslot'])
    for keyword in spl['environment']:
        keyword = utils.process_keyword(keyword)
        if not keyword.startswith("-"):
            update_mappings_context(mappings, utils.process_keyword(keyword))
    return mappings


# extracting use mappings from the ast
class GenerateUseMappingsAST(constraint_ast_visitor.ASTVisitor):
    def __init__(self):
        super(constraint_ast_visitor.ASTVisitor, self).__init__()
    def DefaultValue(self):
        return {}
    def CombineValue(self, value1, value2):
        utils.inline_combine_dicts(value1, value2, utils.inline_combine_lists)
        return value1

    def visitRequiredSIMPLE(self, ctx):
        return { self.spl_name: [ ctx['use'] ] }
    def visitCondition(self, ctx):
        return { self.spl_name: [ ctx['use'] ] }
    def visitAtom(self, ctx):
        self.local_package_name = ctx['package']
        return constraint_ast_visitor.ASTVisitor.visitAtom(self, ctx)
    def visitSelection(self,ctx):
        res = { self.local_package_name: [ ctx['use'] ] }
        if 'suffix' in ctx: res[self.spl_name] = [ ctx['use'] ]
        return  res

def generate_use_mappings_ast(ast_el):
    spl_name, local_ast, combined_ast = ast_el
    visitor = GenerateUseMappingsAST()
    visitor.spl_name = spl_name
    uses = visitor.visitRequired(local_ast)
    utils.inline_combine_dicts(uses, visitor.visitDepend(combined_ast), utils.inline_combine_lists)
    mappings = create_empty_name_mappings()
    map_id_name, map_name_id = mappings
    for spl_name, uses in uses.iteritems():
        map_name_id['flag'][spl_name] = {}
        for use in set(uses):
            update_mappings(mappings, 'flag', spl_name, use)
    return mappings

def generate_name_mappings(concurrent_map,mspl,asts):
    mappings_list = concurrent_map(generate_name_mappings_spl,mspl)
    if not trust_feature_declaration:
        mappings_list = mappings_list + concurrent_map(generate_use_mappings_ast,asts)
    map_id_name, map_name_id = create_empty_name_mappings()
    for local_map_id_name, local_map_name_id in mappings_list:
        map_id_name.update(local_map_id_name)
        map_name_id['package'].update(local_map_name_id['package'])
        map_name_id['context'].update(local_map_name_id['context'])
        utils.inline_combine_dicts(map_name_id['flag'], local_map_name_id['flag'], __gnm_combine_util)
        utils.inline_combine_dicts(map_name_id['slot'], local_map_name_id['slot'], __gnm_combine_util)
        utils.inline_combine_dicts(map_name_id['subslot'], local_map_name_id['subslot'], __gnm_combine_util)
    return map_name_id,map_id_name

def __gnm_combine_util(map_el, local_map_el):
    utils.inline_combine_dicts(map_el, local_map_el, utils.inline_combine_drop)