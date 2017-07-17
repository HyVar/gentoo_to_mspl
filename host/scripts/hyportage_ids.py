# rename into id_repository.py


import utils
import hyportage_data


######################################################################
# HYPORTAGE_IDS BASE FUNCTIONS
######################################################################

# id_repository factory

def id_repository_create():
	return {}, {}, ([], {})

# id_repository getters

def id_repository_get_ids(id_repository): return id_repository[0]
def id_repository_get_spls(id_repository): return id_repository[1]
def id_repository_get_keywords(id_repository): return id_repository[2]

######################################################################
# ID_REPOSITORY MANIPULATION
######################################################################


def id_repository_add_spl(id_repository, spl):
	package_name = hyportage_data.spl_get_name(spl)
	slot = hyportage_data.spl_get_slot(spl)
	subslot = hyportage_data.spl_get_subslot(spl)
	iuses = hyportage_data.spl_get_required_iuses(spl)
	id_list = utils.new_ids(3 + len(iuses))

	ids = id_repository_get_ids(id_repository)
	names = id_repository_get_spls(id_repository)

	ids[id_list[0]] = ("package", package_name)
	ids[id_list[1]] = ("slot", slot, package_name)
	ids[id_list[2]] = ("subslot", subslot, package_name)

	iuses_id = {}
	for idx, use in enumerate(iuses):
		ids[id_list[3 + idx]] = ("use", use, package_name)
		iuses_id[use] = id_list[3 + idx]
	names[package_name] = (id_list[0], id_list[1], id_list[2], iuses_id )


def id_repository_remove_spl(id_repository, spl):
	ids = id_repository_get_ids(id_repository)
	spl_id, slot_id, subslot_id, iuses_ids = id_repository_get_spls(id_repository).pop(hyportage_data.spl_get_name(spl))

	ids.pop(spl_id)
	ids.pop(slot_id)
	ids.pop(subslot_id)
	for id_use in iuses_ids.values(): ids.pop(id_use)


def id_repository_set_keywords(id_repository, keywords):
	ids, names = id_repository_get_keywords(id_repository)
	ids.clear()
	ids.extend(keywords)
	names.clear()
	for idx, keyword in enumerate(keywords):
		names[keyword] = idx

##


def id_repository_to_save_format(id_repository):
	return {
		'ids_spl': id_repository_get_ids(id_repository),
		'spl_ids': { spl_name: { 'id': value[0], 'slot': value[1], 'subslot': value[2], 'iuses': value[3] } for spl_name, value in id_repository_get_spls(id_repository).iteritems() },
		'ids_keyword': id_repository_get_keywords(id_repository)[0],
		'keyword_ids': id_repository_get_keywords(id_repository)[1],
		'last_id': utils.get_last_id()
	}


def id_repository_from_save_format(save_format):
	utils.set_last_id(save_format['last_id'])
	return (
		save_format['ids_spl'],
		{ spl_name: (value['id'], value['slot'], value['subslot'], value['iuses']) for spl_name, value in save_format['spl_ids'].iteritems() },
		(save_format['ids_keyword'], save_format['keyword_ids'])
	)



