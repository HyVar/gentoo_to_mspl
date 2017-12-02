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

	def remove_spl(self, spl):
		spl_id, slot_id, subslot_id, iuses_ids = self.spls.pop(spl.name)

		self.ids.pop(spl_id)
		self.ids.pop(slot_id)
		self.ids.pop(subslot_id)
		for id_use in iuses_ids.values(): self.ids.pop(id_use)

	def add_spl(self, spl):
		spl_name = spl.name
		if spl_name in self.spls: self.remove_spl(spl)

		slot = spl.slot
		subslot = spl.subslot
		iuses = spl.iuses_core
		id_list = utils.new_ids(self, 3 + len(iuses))

		self.ids[id_list[0]] = ("package", spl_name)
		self.ids[id_list[1]] = ("slot", slot, spl_name)
		self.ids[id_list[2]] = ("subslot", subslot, spl_name)

		iuses_id = {}
		for idx, use in enumerate(iuses):
			self.ids[id_list[3 + idx]] = ("use", use, spl_name)
			iuses_id[use] = id_list[3 + idx]
			self.spls[spl_name] = (id_list[0], id_list[1], id_list[2], iuses_id)

	def add_spl_group(self, spl_group):
		spl_group_name = spl_group.name
		spl_group_id = utils.new_id(self)

		self.ids[spl_group_id] = ("package", spl_group_name)
		self.spls[spl_group_name] = (spl_group_id, None, None, None)

	def remove_spl_group(self, spl_group):
		spl_group_name = spl_group.name

		spl_group_id = self.spls[spl_group_name][0]
		self.spls.pop(spl_group_name)
		self.ids.pop(spl_group_id)



"""

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
	spl_name = spl.name
	slot = spl.slot
	subslot = spl.subslot
	iuses = spl.iuses_core
	id_list = utils.new_ids(id_repository, 3 + len(iuses))


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


def id_repository_extends_spl_iuse_list(id_repository, spl_name, iuse_list):
	ids = id_repository_get_ids(id_repository)
	spl_data = id_repository_get_spls(id_repository)[spl_name]
	core_iuse_list = spl_data[3].keys()

	for iuse in iuse_list:
		if iuse not in core_iuse_list:
			id = utils.new_id(id_repository)
			ids[id] = ("use", iuse, spl_name)
			spl_data[3][iuse] = id


def id_repository_remove_spl(id_repository, spl):
	ids = id_repository_get_ids(id_repository)
	spl_id, slot_id, subslot_id, iuses_ids = id_repository_get_spls(id_repository).pop(spl.name)

	ids.pop(spl_id)
	ids.pop(slot_id)
	ids.pop(subslot_id)
	for id_use in iuses_ids.values(): ids.pop(id_use)


def id_repository_add_spl_group(id_repository, spl_group):
	spl_group_name = spl_group.name
	spl_group_id = utils.new_id(id_repository)

	ids = id_repository_get_ids(id_repository)
	names = id_repository_get_spls(id_repository)

	ids[spl_group_id] = ("package", spl_group_name)
	names[spl_group_name] = (spl_group_id, None, None, None)


def id_repository_remove_spl_group(id_repository, spl_group):
	spl_group_id, s1, s2, u = id_repository_get_spls(id_repository).pop(
		hyportage_data.spl_get_name(hyportage_data.spl_group_get_name(spl_group)))
	id_repository_get_ids(id_repository).pop(spl_group_id)


def id_repository_set_keywords(id_repository, keywords):
	ids, names = id_repository_get_keywords(id_repository)
	ids[:] = []
	ids.extend(keywords)
	names.clear()
	for idx, keyword in enumerate(keywords):
		names[keyword] = idx

"""

