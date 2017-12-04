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
		spl_id, iuses_ids = self.spls.pop(spl.name)

		self.ids.pop(spl_id)
		for id_use in iuses_ids.values(): self.ids.pop(id_use)

	def add_spl(self, spl):
		spl_name = spl.name
		iuses = spl.iuses_core
		if spl_name in self.spls:  # update previous data
			data = self.spls[spl_name]
			new_iuses = {iuse for iuse in iuses if iuse not in data[3]}
			id_list = utils.new_ids(self, len(new_iuses))
			for idx, iuse in enumerate(new_iuses):
				iuse_id = "u" + id_list[idx]
				data[1][iuse] = iuse_id
				self.ids[iuse_id] = ("use", iuse, spl_name)
		else:  # create new data
			id_list = utils.new_ids(self, 1 + len(iuses))
			spl_id = "p" + id_list[0]
			self.ids[spl_id] = ("package", spl_name)

			iuses_id = {}
			for idx, iuse in enumerate(iuses):
				iuse_id = "u" + id_list[1 + idx]
				self.ids[iuse_id] = ("use", iuse, spl_name)
				iuses_id[iuse] = iuse_id
			self.spls[spl_name] = (spl_id, iuses_id)


	#####################################
	# GETTERS

	def get_id_from_spl_name(self, spl_name):
		return self.spls[spl_name][0]

	def get_id_from_use_flag(self, spl_name, use_flag):
		return self.spls[spl_name][1][use_flag]

	def data_from_id(self, id):
		return self.ids[id]

	def exists_use_flag(self, spl_name, use_flag):
		return use_flag in self.spls[spl_name][1]


def id_repository_create(): return IDRepository()



