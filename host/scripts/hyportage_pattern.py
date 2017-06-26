#!/usr/bin/python

import configuration

######################################################################
### TRANSLATE ATOMS INTO HASHABLE PATTERNS
######################################################################


parse_package_name = configuration.parse_package_name
pattern_create_from_atom = configuration.pattern_create_from_atom

def pattern_is_package_group_specific(pattern):
	pattern_package_group = pattern[1]
	return (pattern_package_group[0] != "*") and (pattern_package_group[-1] != "*")

def pattern_get_package_group(pattern):
	return pattern[1]



######################################################################
### MATCHING FUNCTIONS
######################################################################


def match_only_package_group(pattern, package_group):
	pattern_package_group = pattern[1]
	if pattern_package_group == "*/*":
		return True
	elif (pattern_package_group[0] != "*") and (pattern_package_group[-1] != "*"):
		return self.package_group == group_name
	elif pattern_package_group[0] != "*":
		pattern_subgroup = pattern_package_group[2:]
		els = package_group[1].split("/")
		return pattern_subgroup == els[-1]
	else:
		pattern_category = pattern_package_group[:-2]
		els = package_group[1].split("/")
		return pattern_category == els[-2]

def match_only_package_version(pattern, version_full, version):
	pattern_vop, pattern_version_full, pattern_version, pattern_has_star = pattern[0], pattern[2], pattern[3], pattern[4]

	if (pattern_version_full is None) or (pattern_vop is None):
		return True
	compare = compare_version(version_full, pattern_version_full)
	if pattern_vop == ">=":
		if compare < 0:
			return False
	elif pattern_vop == ">":
		if compare <= 0:
			return False
	elif pattern_vop == "~":
		if pattern_version != version:
			return False
	elif pattern_vop == "=":
		if pattern_has_star:
			if not version_full.startwith(pattern_version_full):
				return False
		else:
			if compare != 0:
				return False
	elif pattern_vop == "<=":
		if compare > 0:
			return False
	elif pattern_vop == "<":
		if compare >= 0:
			return False
	return True

def match_only_slot(pattern, slot, subslot):
	pattern_slot, pattern_subslot, pattern_sop = pattern[5], pattern[6], pattern[7]
	if pattern_slot:
		if pattern_slot != slot:
			return False
	if pattern_subslot:
		if pattern_subslot != subslot:
			return False
	return True


def match_package_path(pattern, package_name):
	package_group, version_full, version = parse_package_name(package_name)
	return match_only_package_group(pattern, package_group) and match_only_package_version(pattern, version_full, version)


def match_spl_full(pattern, spl):
	return match_only_package_group(pattern, spl['group']) and match_only_package_version(pattern, spl['version_full'], spl['version']) and match_only_slot(pattern, spl['slot'], spl['subslot'])

def match_spl_simple(pattern, spl):
	return match_only_package_version(pattern, spl['version_full'], spl['version']) and match_only_slot(pattern, spl['slot'], spl['subslot'])


######################################################################
### PATTERN REPOSITORY MANIPULATION
######################################################################

## repository factory

## pattern_repository_element: { pattern: (ref_count, set_of_spl) }
## pattern_repository: ( { package_group: pattern_repository_element } , pattern_repository_element )

def pattern_repository_create():
	return ({}, {}) # group specific: map group => pattern => list of matched spls, group non specific

## pattern management

def pattern_repository_element_add_pattern(pattern_repository_element, pattern):
	if pattern in pattern_repository_element:
		pattern_repository_element[pattern][0] = pattern_repository_element[pattern][0] + 1
	else:
		pattern_repository_element[pattern] = (1, set([])) # reference counting for cleaning the repository


def pattern_repository_add_pattern(pattern_repository, pattern):
	if pattern_is_package_group_specific(pattern):
		package_group = pattern_get_package_group(pattern)
		if package_group in pattern_repository[0]:
			pattern_repository_element_add_pattern(pattern_repository[0][package_group], pattern)
		else:
			res = {}
			pattern_repository_element_add_pattern(res, pattern)
			pattern_repository[0][package_group] = res
	else:
		pattern_repository_element_add_pattern(pattern_repository[1], pattern)


def pattern_repository_element_remove_pattern(pattern_repository_element, pattern):
	if pattern_repository_element[pattern][0] == 1:
		pattern_repository_element.pop(pattern)
	else:
		pattern_repository_element[pattern][0] = pattern_repository_element[pattern][0] - 1

def pattern_repository_remove_pattern(pattern_repository, pattern):
	if pattern_is_package_group_specific(pattern):
		pattern_repository_element_remove_pattern(pattern_repository[0][pattern_get_package_group(pattern)], pattern)
	else:
		pattern_repository_element_remove_pattern(pattern_repository[1], pattern)

## spl management

def pattern_repository_element_add_spl(pattern_repository_element, spl, match_function):
	for pattern, value in pattern_repository_element.iteritems():
		if match_function(pattern, spl):
			value[1].add(spl)


def pattern_repository_add_spl(pattern_repository, spl):
	package_group = spl['group']
	if package_group in pattern_repository[0]:
		pattern_repository_element_add_spl(pattern_repository[0][package_group], spl, match_spl_simple)
	pattern_repository_element_add_spl(pattern_repository[1], spl, match_spl_full)


def pattern_repository_element_remove_spl(pattern_repository_element, spl, match_function):
	for pattern, value in pattern_repository_element.iteritems():
		if match_function(pattern, spl):
			value[1].discard(spl)


def pattern_repository_remove_spl(pattern_repository, spl):
	package_group = spl['group']
	if package_group in pattern_repository[0]:
		pattern_repository_element_remove_spl(pattern_repository[0][package_group], spl, match_spl_simple)
	pattern_repository_element_remove_spl(pattern_repository[1], spl, match_spl_full)

## getter

def pattern_repository_element_get(pattern_repository_element, pattern):
	return pattern_repository_element[pattern][1]

def pattern_repository_get(pattern_repository, pattern):
	if pattern_is_package_group_specific(pattern):
		return pattern_repository_element_get(pattern_repository[0][pattern_get_package_group(pattern)], pattern)
	else:
		return pattern_repository_element_get(pattern_repository[1], pattern)

		