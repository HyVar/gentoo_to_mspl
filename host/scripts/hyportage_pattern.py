#!/usr/bin/python

import core_data
from core_data import match_only_package_group, match_spl_full, match_spl_simple

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
		self.in_profile_configuration = False
		self.in_user_configuration = False
		self.containing_spl = set()
		self.use_mapping = {}
		self.matched_spls = None
		self.matched_spls_visible = None

	def add_required_uses_from_spl(self, spl, required_use):
		self.containing_spl.add(spl)
		for use in required_use:
			if use in self.use_mapping:
				self.use_mapping[use] = self.use_mapping[use] + 1
			else:
				self.use_mapping[use] = 1

	def remove_required_uses_from_spl(self, spl, required_use):
		# logging.debug("Pattern element: Removing uses from " + hyportage_data.spl_get_name(spl))
		self.containing_spl.discard(spl)
		for use in required_use:
			if self.use_mapping[use] == 1: self.use_mapping.pop(use)
			else: self.use_mapping[use] = self.use_mapping[use] - 1

	def set_in_profile_configuration(self, in_profile_configuration):
		self.in_profile_configuration = in_profile_configuration

	def set_in_user_configuration(self, in_user_configuration):
		self.in_user_configuration = in_user_configuration

	def add_spl(self, spl):
		if self.matched_spls is not None: self.matched_spls.add(spl)
		if (self.matched_spls_visible is not None) and (hyportage_data.spl_is_visible(spl)):
			self.matched_spls_visible.add(spl)

	def remove_spl(self, spl):
		if self.matched_spls is not None: self.matched_spls.discard(spl)
		if self.matched_spls_visible is not None:
			self.matched_spls_visible.discard(spl)

	def get_required_uses(self): return self.use_mapping.keys()

	def match_self_pattern_simple(self, spl): return match_spl_simple(self.pattern, spl)
	def match_self_pattern_full(self, spl): return match_spl_full(self.pattern, spl)


	def get_spls(self, mspl, spl_groups):
		if self.matched_spls is not None:
			return self.matched_spls
		else:
			if pattern_is_package_group_specific(self.pattern):
				spl_group_name = pattern_get_package_group(self.pattern)
				if spl_group_name in spl_groups:  # fill the matched pattern
					res = set(filter(self.match_self_pattern_simple, hyportage_data.spl_group_get_references(spl_groups[spl_group_name])))
				else: res = set()
			else:
					res = set(filter(self.match_self_pattern_full, mspl.values()))
			if len(self.containing_spl) > spl_list_save_limit:
				self.matched_spls = res
			return res

	def get_spls_visible(self, mspl, spl_groups):
		if self.matched_spls_visible is not None:
			return self.matched_spls_visible
		else:
			if pattern_is_package_group_specific(self.pattern):
				spl_group_name = pattern_get_package_group(self.pattern)
				if spl_group_name in spl_groups:  # fill the matched pattern
					res = filter(self.match_self_pattern_simple, hyportage_data.spl_group_get_references(spl_groups[spl_group_name]))
				else: res = []
			else:
					res = filter(self.match_self_pattern_full, mspl.values())
			res = set(filter(hyportage_data.spl_is_visible, res))
			if len(self.containing_spl) > spl_list_save_limit:
				self.matched_spls_visible = res
			return res

	def contains(self, spl):
		if self.matched_spls is not None: return spl in self.matched_spls
		else: return match_spl_full(self.pattern, spl)

	def is_useful(self): return bool(self.containing_spl) or self.in_profile_configuration or self.in_user_configuration


# pattern repository element management

def pattern_repository_element_add_required_use(pattern_repository_element, spl, required_use):
	return pattern_repository_element.add_required_uses_from_spl(spl, required_use)


def pattern_repository_element_remove_required_use(pattern_repository_element, spl, required_use):
	return pattern_repository_element.remove_required_uses_from_spl(spl, required_use)


def pattern_repository_element_add_spl(pattern_repository_element, spl): pattern_repository_element.add_spl(spl)


def pattern_repository_element_remove_spl(pattern_repository_element, spl): pattern_repository_element.remove_spl(spl)


def pattern_repository_element_get_required_use(pattern_repository_element):
	return pattern_repository_element.get_required_uses()


def pattern_repository_element_get_spls(pattern_repository_element, mspl, spl_groups):
	return pattern_repository_element.get_spls(mspl, spl_groups)


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
	res.matched_spls = set([ mspl(spl_name) for spl_name in save_format['matched_spls_names']])
	return res


######################################################################
# PATTERN LOCAL MAPPING

def pattern_repository_local_map_add_pattern_from_spl(pattern_repository_local_map, spl, pattern, required_use):
	if pattern in pattern_repository_local_map:
		pattern_repository_element_add_required_use(pattern_repository_local_map[pattern], spl, required_use)
		return None
	else:
		el = PatternElement(pattern)
		pattern_repository_element_add_required_use(el, spl, required_use)
		pattern_repository_local_map[pattern] = el
		return el


def pattern_repository_local_map_remove_pattern_from_spl(pattern_repository_local_map, spl, pattern, required_use):
	pattern_repository_element = pattern_repository_local_map[pattern]
	pattern_repository_element_remove_required_use(pattern_repository_element, spl, required_use)
	if not pattern_repository_element_is_useful(pattern_repository_element):
		pattern_repository_local_map.pop(pattern)
		return True
	else: return False


##

def pattern_repository_local_map_add_pattern_from_configuration(pattern_repository_local_map, pattern, setter):
	if pattern in pattern_repository_local_map:
		setter(pattern_repository_local_map[pattern], True)
		return False
	else:
		res = PatternElement(pattern)
		setter(res, True)
		pattern_repository_local_map[pattern] = res
		return True


def pattern_repository_local_map_remove_pattern_from_configuration(pattern_repository_local_map, spl, pattern, setter):
	pattern_repository_element = pattern_repository_local_map[pattern]
	setter(pattern_repository_element, False)
	if not pattern_repository_element_is_useful(pattern_repository_element):
		pattern_repository_local_map.pop(pattern)
		return True
	else: return False


##

def pattern_repository_local_map_add_spl(pattern_repository_local_map, spl, match_function):
	pattern_updated = set()
	for pattern, element in pattern_repository_local_map.iteritems():
		if match_function(pattern, spl):
			pattern_repository_element_add_spl(element, spl)
			pattern_updated.add(pattern)
	return pattern_updated


def pattern_repository_local_map_remove_spl(pattern_repository_element, spl, match_function):
	pattern_updated = set()
	for pattern, element in pattern_repository_element.iteritems():
		if match_function(pattern, spl):
			pattern_repository_element_remove_spl(element, spl)
			pattern_updated.add(pattern)
	return pattern_updated


##

def pattern_repository_local_map_get(pattern_repository_element, pattern): return pattern_repository_element[pattern]


def pattern_repository_local_map_get_spl_required_use(pattern_repository_element, spl):
	res = set()
	for pattern, element in pattern_repository_element.iteritems():
		if pattern_repository_element_contains(element, spl):
			res.update(pattern_repository_element_get_required_use(element))
	return res


##

def pattern_repository_local_map_to_save_format(pattern_repository_element):
	return [ { 'pattern': pattern_to_save_format(pattern), 'data': pattern_repository_element_to_save_format(element) } for pattern, element in pattern_repository_element.iteritems() ]


def pattern_repository_local_map_from_save_format(save_format, mspl):
	return { pattern_from_save_format(save_formal_element['pattern']): pattern_repository_element_from_save_format(save_formal_element['data'], mspl)  for save_formal_element in save_format }


######################################################################
# PATTERN REPOSITORY

def pattern_repository_create():
	return {}, {}


def pattern_repository_add_pattern_from_spl(pattern_repository, mspl, spl_groups, spl):
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


def pattern_repository_add_pattern_from_configuration(pattern_repository, mspl, spl_groups, pattern, setter):
	added = False
	if pattern_is_package_group_specific(pattern):
		spl_group_name = pattern_get_package_group(pattern)
		if spl_group_name in pattern_repository[0]:
			added = pattern_repository_local_map_add_pattern_from_configuration(
				pattern_repository[0][spl_group_name], pattern, setter)
		else:
			res = {}
			added = pattern_repository_local_map_add_pattern_from_configuration(res, pattern, setter)
			pattern_repository[0][spl_group_name] = res
	else:
		added = pattern_repository_local_map_add_pattern_from_configuration(pattern_repository[1], pattern, setter)
	return added


def pattern_repository_remove_pattern_from_configuration(pattern_repository, pattern, setter):
	if pattern_is_package_group_specific(pattern):
		removed = pattern_repository_local_map_remove_pattern_from_configuration(
			pattern_repository[0][pattern_get_package_group(pattern)], pattern, setter)
	else:
		removed = pattern_repository_local_map_remove_pattern_from_spl(pattern_repository[1], pattern, setter)
	return removed


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

def is_pattern_in_pattern_repository(pattern_repository, pattern):
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


