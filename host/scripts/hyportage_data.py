#!/usr/bin/python

import configuration
import hyportage_pattern

######################################################################
### HYPORTAGE ANNEX CREATION
######################################################################

## stores:
# - patterns in the profile configuration		: useful for pattern repository garbage collection
# - iuses declared in the profile configuration	:
# - patterns in the user configuration			: useful for pattern repository garbage collection
# - (user cannot declare new uses)
# - package list								: useful to know which packages to remove to obtain the current state
# - last id


def hyportage_annex_create():
	return (set([]), set([]), set([]), set([]), [0])


def hyportage_annex_get_profile_pattern(hyportage_annex): return hyportage_annex[0]
def hyportage_annex_get_profile_iuses(hyportage_annex): return hyportage_annex[1]
def hyportage_annex_get_user_pattern(hyportage_annex): return hyportage_annex[2]
def hyportage_annex_get_package_list(hyportage_annex): return hyportage_annex[3]
def hyportage_annex_get_last_id(hyportage_annex): return hyportage_annex[4][0]


def hyportage_annex_set_profile_configuration(hyportage_annex, profile_configuration):
	profile_patterns = hyportage_annex[0]
	profile_iuses = hyportage_annex[1]
	profile_patterns.clear()
	profile_iuses.clear()
	# profile data with patterns
	for pattern_set in configuration.configuration_get_required_package(profile_configuration).values():
		profile_patterns.update(pattern_set)
	profile_patterns.update(configuration.configuration_get_pattern_accept_keywords(profile_configuration).keys())
	profile_patterns.update(configuration.configuration_get_pattern_masked(profile_configuration).keys())
	profile_patterns.update(configuration.configuration_get_pattern_configuration(profile_configuration).keys())
	# profile data with iuses
	profile_iuses.update(configuration.configuration_get_iuse(profile_configuration)[0])

def hyportage_annex_set_user_configuration(hyportage_annex, user_configuration):
	user_patterns = hyportage_annex[2]
	user_patterns.clear()
	# user data with patterns
	for pattern_set in configuration.configuration_get_required_package(user_configuration).values():
		user_patterns.update(pattern_set)
	user_patterns.update(configuration.configuration_get_pattern_accept_keywords(user_configuration).keys())
	user_patterns.update(configuration.configuration_get_pattern_masked(user_configuration).keys())
	user_patterns.update(configuration.configuration_get_pattern_configuration(user_configuration).keys())

def hyportage_annex_update_package_list(hyportage_annex, to_add, to_remove):
	package_list = hyportage_annex[3]
	package_list.update(to_add)
	package_list.difference_update(to_remove)

def hyportage_annex_set_last_id(hyportage_annex, last_id):
	hyportage_annex[4][0] = last_id

##

def hyportage_annex_to_save_format(hyportage_annex):
	return {
		'profile_patterns': [ configuration.pattern_to_save_format(pattern) for pattern in hyportage_annex[0] ],
		'profile_iuses': list(hyportage_annex[1]),
		'user_patterns': [ configuration.pattern_to_save_format(pattern) for pattern in hyportage_annex[2] ],
		'package_list': list(hyportage_annex[3]),
		'last_id': hyportage_annex[4][0]
	}

def hyportage_annex_from_save_format(save_format):
	return (
		set([ configuration.pattern_from_save_format(sf) for sf in save_format['profile_patterns'] ]),
		set(save_format['profile_iuses']),
		set([ configuration.pattern_from_save_format(sf) for sf in save_format['user_patterns'] ]),
		set(save_format['package_list']),
		[ save_format['last_id'] ]
		)

######################################################################
### USE SELECTION AND CONFIGURATION MANIPULATION
######################################################################

def use_selection_create():
	return set([])

def use_selection_add(use_selection, use):
	use_selection.add(use)

def use_selection_addall(use_selection, uses):
	use_selection.update(uses)

def use_selection_remove(use_selection, use):
	use_selection.discard(use)

def use_selection_removeall(use_selection, uses):
	use_selection.difference_update(uses)

def use_selection_to_save_format(use_selection):
	return list(use_selection)

def use_selection_from_save_format(save_format):
	return set(save_format)

##

def use_selection_apply_configuration(use_selection, use_configuration):
	use_selection_addall(use_selection, use_configuration_get_positive(use_configuration))
	use_configuration_removeall(use_selection, use_configuration_get_negative(use_configuration))

def use_selection_from_iuse_list(iuse_list):
	res = (set([]), use_selection_create())
	for iuse in iuse_list:
		if iuse[0] == "+":
			iuse = iuse[1:]
			res[0].add(iuse)
			res[1].add(iuse)
		elif iuse[0] == "-":
			iuse = iuse[1:]
			res[0].add(iuse)
		else:
			res[0].add(iuse)
	return res

##

#def use_selection_to_save_format():
#def use_selection_from_save_format():

######################################################################
### RAW DEPENDENCIES MANIPULATION
######################################################################

def raw_dependencies_create():
	return (set([]), {})

def raw_dependencies_add_use(raw_dependencies, use):
	raw_dependencies[0].add(use)

def raw_dependencies_add_pattern(raw_dependencies, pattern):
	if pattern not in raw_dependencies[1]: raw_dependencies[1][pattern] = set([])

def raw_dependencies_add_pattern_use(raw_dependencies, pattern, use):
	raw_dependencies[1][pattern].add(use)

def raw_dependencies_get_patterns(raw_dependencies): return raw_dependencies[1].keys()


######################################################################
### SPL MANIPULATION
######################################################################

def spl_get_name(spl): return spl['name']
def spl_get_group(spl): return spl['group']
def spl_get_slot(spl): return spl['slot']
def spl_get_subslot(spl): return spl['subslot']
def spl_get_version_full(spl): return spl['versions_full']
def spl_get_iuses(spl): return spl['iuses']
def spl_get_raw_dependencies(spl): return spl['raw_dependencies']


######################################################################
### SPL GROUP MANIPULATION
######################################################################

def spl_group_add_spl(spl_group, spl):
	group_name, version_full, spl_name = (spl_get_group(spl), spl_get_version_full(spl), spl_get_name(spl) )
	group = spl_group.get(group_name)
	if group:
		group['implementations'][version_full] = spl_name
		group['dependencies'].append(spl_name)
		group['reference'].append(spl)
	else:
		group = {'implementations': {version_full: spl_name}, 'dependencies': [spl_name], 'reference': [spl] }
		spl_group[group_name] = group

def spl_group_replace_spl(spl_group, old_spl, new_spl):
	group_name = spl_get_group(spl)
	group = spl_group.get(spl_get_group(new_spl))
	group['reference'].remove(old_spl)
	group['reference'].append(new_spl)

def spl_group_remove_spl(spl_group, spl):
	group_name = spl_get_group(spl)
	group = spl_group.get(group_name)
	if group:
		if len(group['reference']) == 1:
			spl_group.pop(group_name)
		else:
			version_full, spl_name = (spl_get_version_full(spl), spl_get_name(spl) )
			group['implementations'].pop(version_full)
			group['dependencies'].remove(spl_name)
			group['reference'].remove(spl)
