import core_data
import portage_data
import hyportage_data
import hyportage_pattern

__author__ = "Michael Lienhardt & Jacopo Mauro"
__copyright__ = "Copyright 2017, Michael Lienhardt & Jacopo Mauro"
__license__ = "ISC"
__version__ = "0.5"
__maintainer__ = "Michael Lienhardt & Jacopo Mauro"
__email__ = "michael.lienhardt@laposte.net & mauro.jacopo@gmail.com"
__status__ = "Prototype"


"""
This file contains the data structure declaration, and the related getter/setters and manipulation functions,
for the annex data necessary for a correct incremental update of the mspl database.
The data structure is called "core_configuration"
"""

######################################################################
# DATA STRUCTURE
######################################################################

def core_configuration_create():
	return (
		set(),       # the set of patterns used in the profile configuration
		set(),       # the set of patterns used in the user configuration
		set(),       # implicit iuse list
		["no-arch"]  # the architecture of the system
	)

##

def core_configuration_get_profile_patterns(core_configuration): return core_configuration[0]
def core_configuration_get_user_patterns(core_configuration): return core_configuration[1]
def core_configuration_get_implicit_iuse(core_configuration): return core_configuration[2]
def core_configuration_get_arch(core_configuration): return core_configuration[3][0]


##

def core_configuration_set_profile_patterns(core_configuration, patterns):
	data = core_configuration_get_profile_patterns(core_configuration)
	data.clear()
	data.update(patterns)


def core_configuration_set_user_patterns(core_configuration, patterns):
	data = core_configuration_get_user_patterns(core_configuration)
	data.clear()
	data.update(patterns)


def core_configuration_set_implicit_iuse(core_configuration, iuses):
	data = core_configuration_get_implicit_iuse(core_configuration)
	data.clear()
	data.update(iuses)


def core_configuration_set_arch(core_configuration, arch): core_configuration[3][0] = arch


##

def core_configuration_to_save_format(core_configuration):
	return {
		'patterns_profile': [ core_data.pattern_to_save_format(pattern) for pattern in core_configuration_get_profile_patterns(core_configuration) ],
		'patterns_user':    [ core_data.pattern_to_save_format(pattern) for pattern in core_configuration_get_user_patterns(core_configuration) ],
		'iuses': list(core_configuration_get_implicit_iuse(core_configuration)),
		'arch': core_configuration_get_arch(core_configuration)
	}


def core_configuration_from_save_format(save_format):
	return (
		set([core_data.pattern_from_save_format(sf) for sf in save_format['patterns_profile']]),
		set([core_data.pattern_from_save_format(sf) for sf in save_format['patterns_user']]),
		set(save_format['profile_iuses']),
		set(save_format['iuses']),
		[ save_format['arch'] ]
		)


######################################################################
# BASE CONFIGURATION APPLICATION FUNCTIONS
######################################################################


def keywords_initialize(spl, arch):
	keyword_default = arch in hyportage_data.spl_get_keywords_list(spl)
	hyportage_data.spl_set_keywords_default(spl, keyword_default)


def keywords_apply_configuration_pattern(spl, pattern_repository, conf_keywords):
	res = False
	for pattern, keyword_list in conf_keywords:
		if spl in hyportage_pattern.pattern_repository_element_get_spls(
				hyportage_pattern.pattern_repository_get(pattern_repository, pattern)):
			res = res or any(keyword in set(hyportage_data.spl_get_keywords_list(spl)) for keyword in keyword_list)
	return res


def iuses_apply_configuration(iuses, conf_iuses):
	hyportage_data.iuses_addall(iuses, conf_iuses)


def use_selection_apply_configuration(use_selection, conf_use):
	hyportage_data.use_selection_apply_configuration(use_selection, conf_use)


def use_selection_apply_configuration_pattern(spl, pattern_repository, use_selection, conf_use):
	for pattern, use_configuration in conf_use:
		if spl in hyportage_pattern.pattern_repository_element_get_spls(
				hyportage_pattern.pattern_repository_get(pattern_repository, pattern)):
			use_selection_apply_configuration(use_selection, use_configuration)


##

def __spl_data_apply_configuration(spl, pattern_repository, iuses, use_selection, mask, conf):
	# 1. get relevant data from the configuration
	conf_keywords = portage_data.configuration_get_pattern_accept_keywords(conf)
	conf_iuse_conf = portage_data.configuration_get_iuse_configuration(conf)
	conf_iuses = portage_data.iuse_configuration_get_iuses(conf_iuse_conf)
	conf_use_configuration = portage_data.iuse_configuration_get_use_configuration(conf_iuse_conf)
	conf_pattern_configuration = portage_data.configuration_get_pattern_configuration(conf)
	conf_mask = portage_data.configuration_get_pattern_masked(conf)
	# 2. accept keywords
	keyword_visible = keywords_apply_configuration_pattern(spl, pattern_repository, conf_keywords)
	# 3. iuses
	new_iuses = set(iuses)
	iuses_apply_configuration(new_iuses, conf_iuses)
	# 4. use selection
	new_use_selection = hyportage_data.use_selection_copy(use_selection)
	use_selection_apply_configuration(new_use_selection, conf_use_configuration)
	use_selection_apply_configuration_pattern(spl, pattern_repository, new_use_selection, conf_pattern_configuration)
	# 5. mask
	new_mask = mask
	for pattern, sign in conf_mask:
		if hyportage_pattern.match_spl_full(pattern, spl):
			new_mask = sign
	# 6. bundle up the generated data
	return keyword_visible, new_iuses, new_use_selection, new_mask


def spl_apply_profile_configuration(spl, pattern_repository, conf):
	keyword_visible, new_iuses, new_use_selection, new_mask = __spl_data_apply_configuration(
		spl, pattern_repository,
		hyportage_data.spl_get_iuses_default(spl),
		hyportage_data.spl_get_use_selection_default(spl),
		False, conf)
	keyword_visible = keyword_visible or hyportage_data.spl_get_keywords_default(spl)
	hyportage_data.spl_set_keywords_profile(spl, keyword_visible)
	hyportage_data.spl_set_iuses_profile(spl, new_iuses)
	hyportage_data.spl_set_use_selection_profile(spl, new_use_selection)
	hyportage_data.spl_set_mask_profile(spl, new_mask)


def spl_apply_user_configuration(spl, pattern_repository, conf):
	keyword_visible, new_iuses, new_use_selection, new_mask = __spl_data_apply_configuration(
		spl, pattern_repository,
		hyportage_data.spl_get_iuses_profile(spl),
		hyportage_data.spl_get_use_selection_profile(spl),
		hyportage_data.spl_get_mask_profile(spl), conf)
	keyword_visible = keyword_visible or hyportage_data.spl_get_keywords_profile(spl)
	updated_visibility = keyword_visible != hyportage_data.spl_get_keywords_user(spl)
	hyportage_data.spl_set_keywords_user(spl, keyword_visible)
	updated_data = new_iuses != hyportage_data.spl_get_iuses_user(spl)
	hyportage_data.spl_set_iuses_user(spl, new_iuses)
	updated_data = updated_data or (new_use_selection != hyportage_data.spl_get_use_selection_user(spl))
	hyportage_data.spl_set_use_selection_user(spl, new_use_selection)
	updated_visibility = updated_visibility or (new_mask != hyportage_data.spl_get_mask_user(spl))
	hyportage_data.spl_set_mask_user(spl, new_mask)
	return updated_data, updated_visibility


######################################################################
# FULL CONFIGURATION MANIPULATION
######################################################################

def get_configuration_pattern(conf):
	def extract_pattern_from_list(list):
		return [ el[0] for el in list]
	conf_pattern_required = portage_data.configuration_get_pattern_required(conf)
	conf_pattern_accept_keywords = portage_data.configuration_get_pattern_accept_keywords(conf)
	conf_pattern_masked = portage_data.configuration_get_pattern_masked(conf)
	conf_pattern_configuration = portage_data.configuration_get_pattern_configuration(conf)
	res = set.union(*conf_pattern_required.values())
	res.update(extract_pattern_from_list(conf_pattern_accept_keywords))
	res.update(extract_pattern_from_list(conf_pattern_masked))
	res.update(extract_pattern_from_list(conf_pattern_configuration))
	return res


def configuration_update_pattern(pattern_repository, mspl, spl_groups, core_conf_patterns, new_configuration, setter):
	pattern_added = set()
	pattern_removed = set()

	conf_patterns = get_configuration_pattern(new_configuration)
	for pattern in conf_patterns - core_conf_patterns:
		added = hyportage_pattern.pattern_repository_add_pattern_from_configuration(
			pattern_repository, mspl, spl_groups, pattern, setter)
		if added: pattern_added.add(pattern)
	for pattern in core_conf_patterns - conf_patterns:
		removed = hyportage_pattern.pattern_repository_remove_pattern_from_configuration(
			pattern_repository, pattern, setter)
		if removed: pattern_removed.add(pattern)
	core_conf_patterns.clear()
	core_conf_patterns.update(conf_patterns)
	return pattern_added, pattern_removed


def apply_configurations(
		pattern_repository, mspl, spl_added_full,
		profile_configuration, user_configuration, must_apply_profile, must_apply_user):
	if must_apply_profile:
		for spl in mspl.values():
			spl_apply_profile_configuration(spl, pattern_repository, profile_configuration)
	else:
		for spl in spl_added_full:  # apply the configurations only on the new spls
			spl_apply_profile_configuration(spl, pattern_repository, profile_configuration)
	spl_modified_data = set(spl_added_full)
	spl_modified_visibility = set(spl_added_full)
	if must_apply_profile or must_apply_user:
		for spl in mspl.values():
			updated_data, updated_visibility = spl_apply_user_configuration(spl, pattern_repository, user_configuration)
			if updated_data: spl_modified_data.add(spl)
			if updated_visibility: spl_modified_visibility.add(spl)
	else:
		for spl in spl_added_full:  # apply the configurations only on the new spls
			spl_apply_user_configuration(spl, pattern_repository, user_configuration)
	return spl_modified_data, spl_modified_visibility


