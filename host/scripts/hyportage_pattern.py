#!/usr/bin/python

import core_data

import hyportage_db


"""
This file contains the class for the hyportage pattern repository.
This structure is essential to compute which are the relevant USE flags of a package (without considering all the noise
added by the profile) and to provide utility functions that resolve a pattern into the corresponding set of spls 
"""


__author__ = "Michael Lienhardt"
__copyright__ = "Copyright 2017, Michael Lienhardt"
__license__ = "GPL3"
__version__ = "0.5"
__maintainer__ = "Michael Lienhardt"
__email__ = "michael.lienhardt@laposte.net"
__status__ = "Prototype"


######################################################################
# TRANSLATE ATOMS INTO HASHABLE PATTERNS (direct link to core_data)
######################################################################


parse_package_name = core_data.parse_package_name
pattern_create_from_atom = core_data.pattern_create_from_atom
pattern_to_save_format = core_data.pattern_to_save_format
pattern_from_save_format = core_data.pattern_from_save_format
pattern_to_atom = core_data.pattern_to_atom
pattern_get_package_group = core_data.pattern_get_package_group


def match_only_package_group(pattern, spl):
	return core_data.match_only_package_group(pattern, core_data.spl_core_get_spl_group_name(spl.core))


def match_spl_simple(pattern, spl):
	return core_data.match_spl_simple(pattern, spl.core)


def match_spl_full(pattern, spl):
	return core_data.match_spl_full(pattern, spl.core)


def pattern_is_package_group_specific(pattern):
	pattern_package_group = pattern_get_package_group(pattern)
	return (pattern_package_group[0] != "*") and (pattern_package_group[-1] != "*")


######################################################################
# PATTERN REPOSITORY MANIPULATION
######################################################################


######################################################################
# PATTERN ELEMENTS

spl_list_save_limit = 10


class PatternElement(object):
	def __init__(self, pattern):
		self.pattern = pattern
		self.containing_spl = {}
		self.__matched_spls = None

	#####################################
	# DATA UPDATE METHODS

	def add_containing_spl(self, spl, required_uses): self.containing_spl[spl] = required_uses

	def remove_containing_spl(self, spl): self.containing_spl.pop(spl)

	def reset_cache(self): self.__matched_spls = None

	#####################################
	# GENERATORS AND PROPERTIES

	def __generate_matched_spls(self):
		if pattern_is_package_group_specific(self.pattern):
			spl_group_name = pattern_get_package_group(self.pattern)
			if spl_group_name in hyportage_db.spl_groups:
				res = set(filter(self.match_self_pattern_simple, iter(hyportage_db.spl_groups[spl_group_name])))
			else: res = set()
		else:
				res = set(filter(self.match_self_pattern_full, hyportage_db.mspl.itervalues()))
		return res

	@property
	def required_uses(self): return {use for uses in self.containing_spl.itervalues() for use in uses}

	@property
	def matched_spls(self):
		if self.__matched_spls is not None: return self.__matched_spls
		else:
			res = self.__generate_matched_spls()
			if len(self.containing_spl) > spl_list_save_limit:
				self.__matched_spls = res
			return res

	@property
	def is_removable(self): return len(self.required_uses) == 0

	#####################################
	# MATCHING METHODS

	def match_self_pattern_simple(self, spl): return core_data.match_spl_simple(self.pattern, spl.core)

	def match_self_pattern_full(self, spl): return core_data.match_spl_full(self.pattern, spl.core)

	def contains(self, spl):
		if self.__matched_spls is not None: return spl in self.__matched_spls
		else: return match_spl_full(self.pattern, spl)


######################################################################
# PATTERN REPOSITORY

class PatternRepository(dict):
	def __init__(self):
		super(PatternRepository, self).__init__()
		self.mapping_local = {}
		self.mapping_external = {}

	def add_spl_dependencies(self, spl):
		pattern_added_list = []
		pattern_updated_list = []
		for pattern, required_uses in spl.dependencies.iteritems():
			if pattern in self:
				pel = self[pattern]
				old_required_uses = pel.containing_spl.get(spl)
				pel.add_containing_spl(spl, required_uses)
				if old_required_uses != pel.required_uses:
					pattern_updated_list.append(pattern)
			else:
				pel = PatternElement(pattern)
				self[pattern] = pel
				pel.add_containing_spl(spl, required_uses)
				pattern_added_list.append(pattern)
				if pattern_is_package_group_specific(pattern):
					spl_group_name = pattern_get_package_group(pattern)
					if spl_group_name in self.mapping_local:
						self.mapping_local[spl_group_name][pattern] = pel
					else:
						self.mapping_local[spl_group_name] = {pattern: pel}
				else:
					self.mapping_external[pattern] = pel
		return pattern_added_list, pattern_updated_list

	def remove_spl_dependencies(self, spl):
		pattern_updated_list = []
		pattern_removed_list = []
		for pattern in spl.dependencies.iterkeys():
			pel = self[pattern]
			required_uses = pel.required_uses
			pel.remove_containing_spl(spl)
			if pel.is_removable:
				pattern_removed_list.append(pel)
				self.pop(pattern)
				if pattern_is_package_group_specific(pattern):
					self.mapping_local[pattern_get_package_group(pattern)].pop(pattern)
				else:
					self.mapping_external.pop(pattern)
			elif required_uses != pel.required_uses:
				pattern_updated_list.append(pattern)
		return pattern_removed_list, pattern_updated_list

	def reset_cache(self, spl_group_name):
		reset_list = []
		mapping = self.mapping_local.get(spl_group_name)
		if mapping:
			for pattern, pel in mapping.iteritems():
				pel.reset_cache()
				reset_list.append(pattern)
		return reset_list

	def get_with_default(self, pattern):
		res = dict.get(self, pattern)
		if res is None: res = PatternElement(pattern)
		return res


def pattern_repository_create():
	return PatternRepository()


