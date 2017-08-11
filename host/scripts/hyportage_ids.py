# rename into id_repository.py


import utils
import hyportage_data


######################################################################
# HYPORTAGE_IDS BASE FUNCTIONS
######################################################################

# id_repository factory

class IDRepository(object):
	def __init__(self):
		self.id_current = 0       # next usable id
		self.ids = {}             # mapping between ids and id information
		self.spls = {}            # mapping between spl names and spl id information
		self.keywords = ([], {})  # list of keywords and mapping between keyword name and index in the list. not used

def id_repository_create():
	return IDRepository()

# id_repository getters

def id_repository_get_ids(id_repository): return id_repository.ids
def id_repository_get_spls(id_repository): return id_repository.spls
def id_repository_get_keywords(id_repository): return id_repository.keywords


def id_repository_get_id_from_spl_name(id_repository, spl_name):
	return id_repository_get_spls(id_repository)[spl_name][0]


def id_repository_get_id_from_use_flag(id_repository, spl_name, use_flag):
	return id_repository_get_spls(id_repository)[spl_name][3][use_flag]


def id_repository_get_use_flag_from_spl_name(id_repository, spl_name):
	return id_repository_get_spls(id_repository)[spl_name][3].keys()


##

def id_repository_exists_spl(id_repository, spl_name):
	return spl_name in id_repository_get_spls(id_repository)


def id_repository_exists_use_flag(id_repository, spl_name, use_flag):
	return use_flag in id_repository_get_spls(id_repository)[spl_name][3]


######################################################################
# ID_REPOSITORY MANIPULATION
######################################################################

def id_repository_add_spl(id_repository, spl):
	spl_name = hyportage_data.spl_get_name(spl)
	slot = hyportage_data.spl_get_slot(spl)
	subslot = hyportage_data.spl_get_subslot(spl)
	iuses = hyportage_data.spl_get_required_iuses(spl)
	id_list = utils.new_ids(id_repository, 3 + len(iuses))

	#print("id updating for " + package_name + ": " + str(iuses) + ", " + str(id_list))

	ids = id_repository_get_ids(id_repository)
	names = id_repository_get_spls(id_repository)

	ids[id_list[0]] = ("package", spl_name)
	ids[id_list[1]] = ("slot", slot, spl_name)
	ids[id_list[2]] = ("subslot", subslot, spl_name)

	iuses_id = {}
	for idx, use in enumerate(iuses):
		ids[id_list[3 + idx]] = ("use", use, spl_name)
		iuses_id[use] = id_list[3 + idx]
	names[spl_name] = (id_list[0], id_list[1], id_list[2], iuses_id)


def id_repository_remove_spl(id_repository, spl):
	ids = id_repository_get_ids(id_repository)
	spl_id, slot_id, subslot_id, iuses_ids = id_repository_get_spls(id_repository).pop(hyportage_data.spl_get_name(spl))

	ids.pop(spl_id)
	ids.pop(slot_id)
	ids.pop(subslot_id)
	for id_use in iuses_ids.values(): ids.pop(id_use)


def id_repository_add_spl_group(id_repository, spl_group):
	spl_group_name = hyportage_data.spl_group_get_name(spl_group)
	spl_group_id = utils.new_id(id_repository)

	ids = id_repository_get_ids(id_repository)
	names = id_repository_get_spls(id_repository)

	ids[spl_group_id] = ("package", spl_group_name)
	names[spl_group_name] = (spl_group_id, None, None, None)


def id_repository_remove_spl_group(id_repository, spl_group):
	spl_group_id, s1, s2, u =id_repository_get_spls(id_repository).pop(
		hyportage_data.spl_get_name(hyportage_data.spl_group_get_name(spl_group)))
	id_repository_get_ids(id_repository).pop(spl_group_id)


def id_repository_set_keywords(id_repository, keywords):
	ids, names = id_repository_get_keywords(id_repository)
	ids[:] = []
	ids.extend(keywords)
	names.clear()
	for idx, keyword in enumerate(keywords):
		names[keyword] = idx

##


def id_repository_to_save_format(id_repository):
	return {
		'ids_spl': id_repository_get_ids(id_repository),
		'spl_ids': {
			spl_name: { 'id': value[0], 'slot': value[1], 'subslot': value[2], 'iuses': value[3] }
			for spl_name, value in id_repository_get_spls(id_repository).iteritems() },
		'ids_keyword': id_repository_get_keywords(id_repository)[0],
		'keyword_ids': id_repository_get_keywords(id_repository)[1],
		'last_id': id_repository.id_current
	}


def id_repository_from_save_format(save_format):
	res = IDRepository()
	res.id_current = save_format['last_id']
	res.ids = 	save_format['ids_spl']
	res.spls = {
		spl_name: (value['id'], value['slot'], value['subslot'], value['iuses'])
		for spl_name, value in save_format['spl_ids'].iteritems() }
	res.keywords = (save_format['ids_keyword'], save_format['keyword_ids'])
	return res



