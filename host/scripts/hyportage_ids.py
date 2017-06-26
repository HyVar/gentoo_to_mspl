# rename into hyportage_ids.py


import utils
import constraint_ast_visitor


######################################################################
### HYPORTAGE_IDS BASE FUNCTIONS
######################################################################

## hyportage_ids factory

def hyportage_ids_create():
    return ( { } , ( {}, {}, {}, [] ) ) #( { } , {'package': { package_name: id}, 'flag': { package_name: { use: id } }, 'slots': { package_name: (slot, id_slot, subslot, id_subslot) }, 'context': set()} )

## hyportage_ids getters

def hyportage_ids_get_ids(hyportage_ids): return hyportage_ids[0]
def hyportage_ids_get_names(hyportage_ids): return hyportage_ids[1]

##

def hyportage_ids_get_package(names): return names[0]
def hyportage_ids_get_slots(names): return names[1]
def hyportage_ids_get_iuses(names): return names[2]
def hyportage_ids_get_contexts(names): return names[3]


def hyportage_ids_get_names_packages(hyportage_ids):
    return hyportage_ids[1][0]

def hyportage_ids_get_names_iuses(hyportage_ids):
    return hyportage_ids[1][1]

def hyportage_ids_get_names_slots(hyportage_ids):
    return hyportage_ids[1][2]

def hyportage_ids_get_names_contexts(hyportage_ids):
    return hyportage_ids[1][3]




######################################################################
### HYPORTAGE_IDS MANIPULATION
######################################################################


def hyportage_ids_add_spl(hyportage_ids, spl):
    package_name = hyportage_data.spl_get_name(spl)
    slot = hyportage_data.spl_get_slot(spl)
    subslot = hyportage_data.spl_get_subslot(spl)
    iuses = hyportage_data.spl_get_iuses(spl)
    keywords = hyportage_data.spl_get_keywords(spl)
    id_list = utils.new_ids(3 + len(iuses))

    ids = hyportage_ids_get_ids(hyportage_ids)
    names = hyportage_ids_get_names(hyportage_ids)

    ids[id_list[0]] = ("package", package_name )
    hyportage_ids_get_package(names)[package_name] = id_list[0]
    ids[id_list[1]]    = ("slot", slot, package_name )
    ids[id_list[2]] = ("subslot", subslot, package_name )
    hyportage_ids_get_slots(names)[package_name] = ( id_list[1], id_list[2] )
    use_map = {}
    for idx, use in enumerate(iuses):
        ids[id_list[3 + idx]] = ("use", use, package_name)
        use_map[use] = id_list[3 + idx]
    hyportage_ids_get_iuses(names)[package_name] = use_map

    registered_keywords = hyportage_ids_get_contexts(names)
    for keyword in keywords:
        if keyword not in registered_keywords:
            registered_keywords.append(keyword)

def hyportage_ids_remove_spl(hyportage_ids, package_name):
    ids = hyportage_ids_get_ids(hyportage_ids)
    names = hyportage_ids_get_names(hyportage_ids)
    
    id_package = hyportage_ids_get_package(names).pop(package_name)
    id_slot, id_subslot = hyportage_ids_get_slots(names).pop(package_name)
    use_map = hyportage_ids_get_iuses(names).pop(package_name)
    ids.pop(id_package)
    ids.pop(id_slot)
    ids.pop(id_subslot)
    for id_use in use_map.values(): ids.pop(id_use)


######################################################################
### FUNCTIONS TO GET THE INFORMATION FROM THE MSPL
######################################################################



def create_empty_name_mappings():
    return ( { } , {'package': {}, 'flag': {}, 'slot': {}, 'subslot': {}, 'context': {}} )


def create_name_mappings(spl_name):
    new_id = utils.new_id()
    return ( {new_id: {'type': 'package', 'name': spl_name} } ,
        {'package': {spl_name: new_id}, 'flag': {spl_name:{}}, 'slot': {spl_name:{}}, 'subslot': {spl_name:{}}, 'context': {}} )

def __gnm_combine_util(map_el, local_map_el):
    utils.dict_combine_inline(map_el, local_map_el, utils.all_combine_inline_drop)

def update_name_mappings(mappings, added_mapping):
    map_id_name, map_name_id = mappings
    local_map_id_name, local_map_name_id = added_mapping
    map_id_name.update(local_map_id_name)
    map_name_id['package'].update(local_map_name_id['package'])
    map_name_id['context'].update(local_map_name_id['context'])
    utils.dict_combine_inline(map_name_id['flag'], local_map_name_id['flag'], __gnm_combine_util)
    utils.dict_combine_inline(map_name_id['slot'], local_map_name_id['slot'], __gnm_combine_util)
    utils.dict_combine_inline(map_name_id['subslot'], local_map_name_id['subslot'], __gnm_combine_util)

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
    print("found features: " + str(spl['features']))
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
