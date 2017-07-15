#!/usr/bin/python

import core_data
import portage_data

import hyportage_pattern
import hyportage_ids
import hyportage_constraint_ast

######################################################################
# KEYWORDS MANIPULATION
######################################################################

keywords_create = core_data.set_configuration_create
keywords_copy = core_data.set_configuration_copy


def keywords_apply_configuration_pattern(spl, keywords, conf_keywords):
	for pattern, keyword_list in conf_keywords:
		if hyportage_pattern.match_spl_full(pattern, spl):
			keywords.update(keywords)

keywords_to_save_format = core_data.set_configuration_to_save_format
keywords_from_save_format = core_data.set_configuration_from_save_format


######################################################################
# IUSE MANIPULATION
######################################################################

iuses_create = core_data.set_configuration_create
iuses_copy = core_data.set_configuration_copy


def iuses_apply_configuration(iuses, conf_iuses): iuses.update(conf_iuses)


iuses_to_save_format = core_data.set_configuration_to_save_format
iuses_from_save_format = core_data.set_configuration_from_save_format


######################################################################
# USE SELECTION MANIPULATION
######################################################################


use_selection_create = core_data.set_configuration_create
use_selection_copy = core_data.set_configuration_copy
use_selection_add = core_data.set_configuration_add
use_selection_addall = core_data.set_configuration_addall
use_selection_remove = core_data.set_configuration_remove
use_selection_removeall = core_data.set_configuration_removeall
use_selection_to_save_format = core_data.set_configuration_to_save_format
use_selection_from_save_format = core_data.set_configuration_from_save_format

##


def use_selection_apply_configuration(use_selection, conf_use):
	use_selection_addall(use_selection, portage_data.use_configuration_get_positive(conf_use))
	use_selection_removeall(use_selection, portage_data.use_configuration_get_negative(conf_use))


def use_selection_apply_configuration_pattern(spl, use_selection, conf_use):
	for pattern, use_configuration in conf_use:
		if hyportage_pattern.match_spl_full(pattern, spl):
			use_selection_apply_configuration(use_selection, use_configuration)


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

######################################################################
# DEPENDENCIES MANIPULATION
######################################################################


def dependencies_create(): return set([]), {}


def dependencies_add_use(raw_dependencies, use):
	raw_dependencies[0].add(use)


def dependencies_add_pattern(raw_dependencies, pattern):
	if pattern not in raw_dependencies[1]: raw_dependencies[1][pattern] = set([])


def dependencies_add_pattern_use(raw_dependencies, pattern, use):
	raw_dependencies[1][pattern].add(use)


def dependencies_get_patterns(raw_dependencies): return raw_dependencies[1].keys()


######################################################################
# SPL AND MSPL MANIPULATION
######################################################################

def spl_get_name(spl): return spl['name']
def spl_get_group(spl): return spl['group']
def spl_get_slot(spl): return spl['slot']
def spl_get_subslot(spl): return spl['subslot']
def spl_get_version(spl): return spl['version']
def spl_get_version_full(spl): return spl['version_full']
def spl_get_dependencies(spl): return spl['dependencies']
def spl_is_deprecated(spl): return spl['deprecated']


def spl_get_fm_local(spl): return spl['fm_local']
def spl_get_fm_combined(spl): return spl['fm_combined']
def spl_get_smt_constraint(spl): return spl['smt_constraint']


def spl_get_required_iuses_local(spl): return spl['required_iuses_local']
def spl_get_required_iuses(spl): return spl['required_iuses']


def spl_get_keywords_default(spl): return spl['keywords_default']
def spl_get_keywords_profile(spl): return spl['keywords_profile']
def spl_get_keywords_user(spl): return spl['keywords_user']


def spl_get_iuses_default(spl): return spl['iuses_default']
def spl_get_iuses_profile(spl): return spl['iuses_profile']
def spl_get_iuses_user(spl): return spl['iuses_user']


def spl_get_use_selection_default(spl): return spl['use_selection_default']
def spl_get_use_selection_profile(spl): return spl['use_selection_profile']
def spl_get_use_selection_user(spl): return spl['use_selection_user']


def spl_get_mask_profile(spl): return spl['mask_profile']
def spl_get_mask_user(spl): return spl['mask_user']

##


def spl_set_keywords_profile(spl, keywords): spl['keywords_profile'] = keywords
def spl_set_iuses_profile(spl, new_iuses): spl['iuses_profile'] = new_iuses
def spl_set_use_selection_profile(spl, new_use_selection): spl['use_selection_profile'] = new_use_selection
def spl_set_mask_profile(spl, new_mask): spl['mask_profile'] = new_mask


def spl_set_keywords_user(spl, keywords): spl['keywords_user'] = keywords
def spl_set_iuses_user(spl, new_iuses): spl['iuses_user'] = new_iuses
def spl_set_use_selection_user(spl, new_use_selection): spl['use_selection_user'] = new_use_selection
def spl_set_mask_user(spl, new_mask): spl['mask_user'] = new_mask


def spl_reset_required_use(spl, pattern_repository):
	spl['required_use'] = list(set(
		spl['required_use_default'] +
		hyportage_pattern.pattern_repository_get_spl_required_use(pattern_repository, spl)))


def spl_set_smt_constraint(spl, smt_constraint): spl['smt_constraint'] = smt_constraint
##


def __spl_data_apply_configuration(spl, keywords, iuses, use_selection, mask, conf):
	# 1. get relevant data from the configuration
	conf_keywords = portage_data.configuration_get_pattern_accept_keywords(conf)
	conf_iuse_conf = portage_data.configuration_get_iuse_configuration(conf)
	conf_iuses = portage_data.iuse_configuration_get_iuses(conf_iuse_conf)
	conf_use_configuration = portage_data.iuse_configuration_get_use_configuration(conf_iuse_conf)
	conf_pattern_configuration = portage_data.configuration_get_pattern_configuration(conf)
	conf_mask = portage_data.configuration_get_pattern_masked(conf)
	# 2. accept keywords
	new_keywords = keywords_copy(keywords)
	keywords_apply_configuration_pattern(spl, new_keywords, conf_keywords)
	# 3. iuses
	new_iuses = set(iuses)
	iuses_apply_configuration(new_iuses, conf_iuses)
	# 4. use selection
	new_use_selection = use_selection_copy(use_selection)
	use_selection_apply_configuration(new_use_selection, conf_use_configuration)
	use_selection_apply_configuration_pattern(spl, new_use_selection, conf_pattern_configuration)
	# 5. mask
	new_mask = mask
	for pattern, sign in conf_mask:
		if hyportage_pattern.match_spl_full(pattern, spl):
			new_mask = sign
	# 6. bundle up the generated data
	return new_keywords, new_iuses, new_use_selection, new_mask


def spl_apply_profile_configuration(spl, conf):
	new_keywords, new_iuses, new_use_selection, new_mask = __spl_data_apply_configuration(
		spl,
		spl_get_keywords_default(spl),
		spl_get_iuses_default(spl),
		spl_get_use_selection_default(spl),
		False,
		conf)
	spl_set_keywords_profile(spl, new_keywords)
	spl_set_iuses_profile(spl, new_iuses)
	spl_set_use_selection_profile(spl, new_use_selection)
	spl_set_mask_profile(spl, new_mask)


def spl_apply_user_configuration(spl, conf):
	new_keywords, new_iuses, new_use_selection, new_mask = __spl_data_apply_configuration(
		spl,
		spl_get_keywords_profile(spl),
		spl_get_iuses_profile(spl),
		spl_get_use_selection_profile(spl),
		spl_get_mask_profile(spl),
		conf)
	spl_set_keywords_user(spl, new_keywords)
	spl_set_iuses_user(spl, new_iuses)
	spl_set_use_selection_user(spl, new_use_selection)
	spl_set_mask_user(spl, new_mask)

##


def spl_to_save_format(spl):
	return {
		'name': spl_get_name(spl),
		'group': spl_get_group(spl),
		'deprecated': spl_is_deprecated(spl),
		'version_full': spl_get_version_full(spl),
		'version': spl_get_version(spl),
		'slot': spl_get_slot(spl),
		'subslot': spl_get_subslot(spl),
		'fm_local': hyportage_constraint_ast.ast_require_to_save_format(spl_get_fm_local(spl)),
		'fm_combined': hyportage_constraint_ast.ast_depend_to_save_format(spl_get_fm_combined(spl)),
		'dependencies': spl_get_depedencies(spl),
		#
		'required_iuses_local': spl_get_required_iuses_local(spl),
		'required_iuses': spl_get_required_iuses(spl),
		#
		'keywords_default': spl_get_keywords_default(spl),
		'keywords_profile': spl_get_keywords_profile(spl),
		'keywords_user': spl_get_keywords_user(spl),
		#
		'iuses_default': spl_get_iuses_default(spl),
		'iuses_profile': spl_get_iuses_profile(spl),
		'iuses_user': spl_get_iuses_user(spl),
		#
		'use_selection_default': spl_get_use_selection_default(spl),
		'use_selection_profile': spl_get_use_selection_profile(spl),
		'use_selection_user': spl_get_use_selection_user(spl),
		#
		'smt_constraint': spl_get_smt_constraint(spl)
	}


def spl_from_save_format(save_format):
	return {
		'name': save_format['name'],
		'group': save_format['group'],
		'deprecated': save_format['deprecated'],
		'version_full': save_format['version_full'],
		'version': save_format['version'],
		'slot': save_format['slot'],
		'subslot': save_format['subslot'],
		'fm_local': hyportage_constraint_ast.ast_require_from_save_format(save_format['fm_local']),
		'fm_combined': hyportage_constraint_ast.ast_require_from_save_format(save_format['fm_combined']),
		'dependencies': save_format['dependencies'],
		#
		'required_iuses_local': save_format['required_iuses_local'],
		'required_iuses': save_format['required_iuses'],
		#
		'keywords_default': save_format['keywords_default'],
		'keywords_profile': save_format['keywords_profile'],
		'keywords_user': save_format['keywords_user'],
		#
		'iuses_default': save_format['iuses_default'],
		'iuses_profile': save_format['iuses_profile'],
		'iuses_user': save_format['iuses_user'],
		#
		'use_selection_default': save_format['use_selection_default'],
		'use_selection_profile': save_format['use_selection_profile'],
		'use_selection_user': save_format['use_selection_user'],
		#
		'smt_constraint': save_format['smt_constraint']
	}

##

def mspl_create(): return {}


class MSPLToSaveFormatGenerator(object):
	def __init__(self, mspl):
		self.items = mspl.iteritems()

	def __iter__(self):
		return self

	def __next__(self):
		return self.next()

	def next(self):
		key, value = self.items.next()
		return spl_to_save_format(value)


def mspl_to_save_format(mspl):
	return MSPLToSaveFormatGenerator(mspl)


def mspl_from_save_format(save_format):
	mspl = {}
	spl_group = {}
	for el in save_format:
		spl = spl_from_save_format(el)
		mspl[spl_get_name(spl)] = spl
		spl_group_add_spl(spl_group, spl)
	return mspl, spl_group


######################################################################
# SPL GROUP MANIPULATION
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


######################################################################
# FULL SPL DATA MANIPULATION
######################################################################


def hyportage_to_save_format(pattern_repository, id_repository, mspl, spl_group):
	return {
		'pattern_repository': hyportage_pattern.pattern_repository_to_save_format(pattern_repository),
		'id_repository': hyportage_ids.id_repository_to_save_format(id_repository),
		'mspl': mspl_to_save_format(mspl),
	}


def hyportage_from_save_format(save_format):
	mspl, spl_group = mspl_from_save_format(save_format['mspl'])
	return (
		hyportage_pattern.pattern_repository_from_save_format(save_format['pattern_repository'], mspl),
		hyportage_ids.id_repository_from_save_format(save_format['id_repository']),
		mspl,
		spl_group
	)
