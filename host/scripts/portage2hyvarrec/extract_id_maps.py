######################################################################
### FUNCTIONS TO GET THE INFORMATION FROM THE MSPL
######################################################################

import utils
import constraint_ast_visitor


# TODO: need to remove this option
trust_feature_declaration = False

def create_empty_name_mappings():
    return ( { } , {'package': {}, 'flag': {}, 'slot': {}, 'subslot': {}, 'context': {}} )
def create_name_mappings(spl_name):
    new_id = utils.new_id()
    return ( {new_id: {'type': 'package', 'name': spl_name} } ,
        {'package': {spl_name: new_id}, 'flag': {spl_name:{}}, 'slot': {spl_name:{}}, 'subslot': {spl_name:{}}, 'context': {}} )

def __gnm_combine_util(map_el, local_map_el):
    utils.inline_combine_dicts(map_el, local_map_el, utils.inline_combine_drop)

def update_name_mappings(mappings, added_mapping):
    map_id_name, map_name_id = mappings
    local_map_id_name, local_map_name_id = added_mapping
    map_id_name.update(local_map_id_name)
    map_name_id['package'].update(local_map_name_id['package'])
    map_name_id['context'].update(local_map_name_id['context'])
    utils.inline_combine_dicts(map_name_id['flag'], local_map_name_id['flag'], __gnm_combine_util)
    utils.inline_combine_dicts(map_name_id['slot'], local_map_name_id['slot'], __gnm_combine_util)
    utils.inline_combine_dicts(map_name_id['subslot'], local_map_name_id['subslot'], __gnm_combine_util)

# extracting name mapping from the spl
def update_mappings_package(mappings, name):
    map_id_name, map_name_id = mappings
    new_id = utils.new_id()
    map_name_id['package'][name] = new_id
    map_id_name[new_id] = {'type': "package", 'name': name}
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

# extracting name mapping from package group list
def generate_name_mappings_package_groups(package_groups):
    mappings = create_empty_name_mappings()
    for package_group in package_groups:
        update_mappings_package(mappings, package_group)
    return mappings





def add_context_ints(map_name_id):
    map_name_id["context_int"] = {}
    counter = 0
    for i in map_name_id["context"]:
        map_name_id["context_int"][i] = counter
        counter += 1


#def generate_name_mappings(concurrent_map,mspl,asts):
#    mappings_list = concurrent_map(generate_name_mappings_spl,mspl)
#    if not trust_feature_declaration:
#        mappings_list = mappings_list + concurrent_map(generate_use_mappings_ast,asts)
#    res = create_empty_name_mappings()
#    for local_mappings in mappings_list:
#        update_name_mappings(res, local_mappings)
#    return res


#    map_id_name, map_name_id = create_empty_name_mappings()
#    for local_map_id_name, local_map_name_id in mappings_list:
#        map_id_name.update(local_map_id_name)
#        map_name_id['package'].update(local_map_name_id['package'])
#        map_name_id['context'].update(local_map_name_id['context'])
#        utils.inline_combine_dicts(map_name_id['flag'], local_map_name_id['flag'], __gnm_combine_util)
#        utils.inline_combine_dicts(map_name_id['slot'], local_map_name_id['slot'], __gnm_combine_util)
#        utils.inline_combine_dicts(map_name_id['subslot'], local_map_name_id['subslot'], __gnm_combine_util)
#    return map_name_id,map_id_name
