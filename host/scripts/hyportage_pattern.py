#!/usr/bin/python

import core_data

import hyportage_db
import hyportage_data

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

# structure of a repository:
# ( {spl_group_name -> { pattern -> PatternElement} }
#   { pattern -> PatternElement } )

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

"""


# pattern repository element management

def pattern_repository_element_add_required_use(pattern_repository_element, spl, required_use):
	return pattern_repository_element.add_containing_spl(spl, required_use)


def pattern_repository_element_remove_required_use(pattern_repository_element, spl, required_use):
	return pattern_repository_element.remove_containing_spl(spl, required_use)


def pattern_repository_element_add_spl(pattern_repository_element, spl): pattern_repository_element.add_spl(spl)


def pattern_repository_element_remove_spl(pattern_repository_element, spl): pattern_repository_element.remove_spl(spl)


def pattern_repository_element_get_required_use(pattern_repository_element):
	return pattern_repository_element.required_uses()


def pattern_repository_element_get_required_use_required(pattern_repository_element):
	return pattern_repository_element.get_required_uses_required()


def pattern_repository_element_get_spls(pattern_repository_element, mspl, spl_groups):
	return pattern_repository_element.matched_spls(mspl, spl_groups)


def pattern_repository_element_get_spls_visible(pattern_repository_element, mspl, spl_groups):
	return pattern_repository_element.get_spls_visible(mspl, spl_groups)

##


def pattern_repository_element_set_in_profile_configuration(pattern_repository_element, boolean):
	pattern_repository_element.in_profile_configuration = boolean


def pattern_repository_element_set_in_user_configuration(pattern_repository_element, boolean):
	pattern_repository_element.in_user_configuration = boolean


def pattern_repository_element_is_useful(pattern_repository_element):
	return pattern_repository_element.is_useful()


def pattern_repository_element_contains(pattern_repository_element, spl):
	return pattern_repository_element.contains(spl)

##


def pattern_repository_element_to_save_format(pattern_repository_element):
	return {
		'in_profile_configuration': pattern_repository_element.in_profile_configuration,
		'in_user_configuration': pattern_repository_element.in_user_configuration,
		'containing_spl_names': [ hyportage_data.spl_get_name(spl) for spl in pattern_repository_element.containing_spl ],
		'required_use': pattern_repository_element.use_mapping,
		'matched_spls_names': [ hyportage_data.spl_get_name(spl) for spl in pattern_repository_element.matched_spls ]
	}


def pattern_repository_element_from_save_format(save_format, mspl):
	res = PatternElement()
	res.in_profile_configuration = save_format['in_profile_configuration']
	res.in_user_configuration = save_format['in_user_configuration']
	res.containing_spl = set([ mspl(spl_name) for spl_name in save_format['containing_spl_names']])
	res.use_mapping = save_format['required_use']
	res.__matched_spls = set([mspl(spl_name) for spl_name in save_format['matched_spls_names']])
	return res

"""



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
				required_uses = pel.required_uses
				pel.add_containing_spl(spl, required_uses)
				if required_uses != pel.required_uses:
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



def pattern_repository_create():
	return {}, {}, {}  # full pattern mapping, spl group local pattern mapping, non spl group local pattern mapping


def pattern_repository_add_pattern_from_spl(pattern_repository, spl):
	pattern_added = set()
	for pattern, required_use in hyportage_data.spl_get_dependencies(spl).iteritems():
		if pattern_is_package_group_specific(pattern):
			spl_group_name = pattern_get_package_group(pattern)
			if spl_group_name in pattern_repository[0]:
				added = pattern_repository_local_map_add_pattern_from_spl(
					pattern_repository[0][spl_group_name], spl, pattern, required_use)
			else:
				res = {}
				added = pattern_repository_local_map_add_pattern_from_spl(res, spl, pattern, required_use)
				pattern_repository[0][spl_group_name] = res
			if added:
				pattern_added.add(pattern)
		else:
			added = pattern_repository_local_map_add_pattern_from_spl(pattern_repository[1], spl, pattern, required_use)
			if added:
				pattern_added.add(pattern)
	return pattern_added


def pattern_repository_remove_pattern_from_spl(pattern_repository, spl):
	pattern_removed = set()
	for pattern, required_use in hyportage_data.spl_get_dependencies(spl).iteritems():
		if pattern_is_package_group_specific(pattern):
			removed = pattern_repository_local_map_remove_pattern_from_spl(
				pattern_repository[0][pattern_get_package_group(pattern)], spl, pattern, required_use)
			if removed: pattern_removed.add(pattern)
		else:
			removed = pattern_repository_local_map_remove_pattern_from_spl(pattern_repository[1], spl, pattern, required_use)
		if removed: pattern_removed.add(pattern)
	return pattern_removed


def pattern_repository_add_pattern_from_scratch(pattern_repository, pattern):
	if pattern_is_package_group_specific(pattern):
		spl_group_name = pattern_get_package_group(pattern)
		if spl_group_name in pattern_repository[0]:
			pattern_repository_local_map_add_pattern_from_scratch(pattern_repository[0][spl_group_name], pattern)
		else:
			res = {}
			pattern_repository_local_map_add_pattern_from_scratch(res, pattern)
			pattern_repository[0][spl_group_name] = res
	else:
		pattern_repository_local_map_add_pattern_from_scratch(pattern_repository[1], pattern)


##

def pattern_repository_add_spl(pattern_repository, spl):
	pattern_updated = set()
	package_group = hyportage_data.spl_get_group_name(spl)
	if package_group in pattern_repository[0]:
		pattern_updated.update(pattern_repository_local_map_add_spl(
			pattern_repository[0][package_group], spl, match_spl_simple))
	pattern_updated.update(pattern_repository_local_map_add_spl(pattern_repository[1], spl, match_spl_full))
	return pattern_updated


def pattern_repository_remove_spl(pattern_repository, spl):
	pattern_updated = set()
	package_group = hyportage_data.spl_get_group_name(spl)
	if package_group in pattern_repository[0]:
		pattern_updated.update(pattern_repository_local_map_remove_spl(
			pattern_repository[0][package_group], spl, match_spl_simple))
	pattern_updated.update(pattern_repository_local_map_remove_spl(pattern_repository[1], spl, match_spl_full))
	return pattern_updated


##

def is_pattern_in_pattern_repository(pattern_repository, pattern):  # not used
	if pattern_is_package_group_specific(pattern):
		return pattern in pattern_repository[0][pattern_get_package_group(pattern)]
	else: return pattern in pattern_repository[1]


def pattern_repository_get(pattern_repository, pattern):
	if pattern_is_package_group_specific(pattern):
		return pattern_repository_local_map_get(pattern_repository[0][pattern_get_package_group(pattern)], pattern)
	else: return pattern_repository_local_map_get(pattern_repository[1], pattern)


def pattern_repository_get_spl_required_use(pattern_repository, spl):
	package_group = hyportage_data.spl_get_group_name(spl)
	if package_group in pattern_repository[0]:
		res = pattern_repository_local_map_get_spl_required_use(pattern_repository[0][package_group], spl)
	else: res = set()
	res.update(pattern_repository_local_map_get_spl_required_use(pattern_repository[1], spl))
	return res


def pattern_repository_get_pattern_from_spl_group_name(pattern_repository, spl_group_name):
	res = pattern_repository[0].get(spl_group_name, set())
	for pattern in pattern_repository[1].keys():
		if match_only_package_group(pattern, spl_group_name): res.add(pattern)
	return res


class PatternIterator(object):
	def __init__(self, pattern_repository):
		self.repo = pattern_repository
		self.stage = 0
		self.iter_spl_groups = pattern_repository[0].iteritems()
		self.iter_pattern = self.iter_spl_groups.next()[1].iteritems()

	def __iter__(self): return self

	def next(self):
		while True:
			try:
				return self.iter_pattern.next()[0]
			except StopIteration:
				if self.stage == 1:
					raise StopIteration()
				else:
					try:
						self.iter_pattern = self.iter_spl_groups.next()[1].iteritems()
					except StopIteration:
						self.stage = 1
						self.iter_pattern = self.repo[1].iteritems()


def pattern_repository_get_patterns(pattern_repository):
	return PatternIterator(pattern_repository)


##

def pattern_repository_to_save_format(pattern_repository):
	return {
		'package_specific': {
			k: pattern_repository_local_map_to_save_format(local_map)
			for k, local_map in pattern_repository[0].iteritems() },
		'global_patterns': pattern_repository_local_map_to_save_format(pattern_repository[1]) }


def pattern_repository_from_save_format(save_format, mspl):
	return ( {
			k: pattern_repository_local_map_from_save_format(sf_local_map, mspl)
			for k, sf_local_map in save_format['package_specific'].iteritems() },
		pattern_repository_local_map_from_save_format(save_format['global_patterns'], mspl) )


