#!/usr/bin/python


import utils


"""
This file contains the class for the ID repository of hyportage.
This id repository maps all relevant data to unique IDs that can be put seamlessly as name of a z3 variable
"""


__author__ = "Michael Lienhardt"
__copyright__ = "Copyright 2017, Michael Lienhardt"
__license__ = "GPL3"
__version__ = "0.5"
__maintainer__ = "Michael Lienhardt"
__email__ = "michael.lienhardt@laposte.net"
__status__ = "Prototype"


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

	#####################################
	# GETTERS

	def get_id_from_spl_name(self, spl_name):
		return self.spls[spl_name][0]

	def id_from_use_flag(self, spl_name, use_flag):
		return self.spls[spl_name][3][use_flag]

	def data_from_id(self, id):
		return self.ids[id]

	def exists_use_flag(self, spl_name, use_flag):
		return use_flag in self.spls[spl_name][3]


def id_repository_create(): return IDRepository()



