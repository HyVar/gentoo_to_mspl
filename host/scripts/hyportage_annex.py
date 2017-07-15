
import portage_data

######################################################################
# HYPORTAGE ANNEX CREATION
######################################################################

## stores:
# - patterns in the profile configuration		: useful for pattern repository garbage collection
# - iuses declared in the profile configuration	:
# - patterns in the user configuration			: useful for pattern repository garbage collection
# - (user cannot declare new uses)
# - package list								: useful to know which packages to remove to obtain the current state
# - last id


def hyportage_annex_create():
	return set([]), set([]), set([]), set([]), [0]


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
	for pattern_set in portage_data.configuration_get_pattern_required(profile_configuration).values():
		profile_patterns.update(pattern_set)
	profile_patterns.update(portage_data.configuration_get_pattern_accept_keywords(profile_configuration).keys())
	profile_patterns.update(portage_data.configuration_get_pattern_masked(profile_configuration).keys())
	profile_patterns.update(portage_data.configuration_get_pattern_configuration(profile_configuration).keys())
	# profile data with iuses
	profile_iuses.update(portage_data.configuration_get_iuse(profile_configuration)[0])


def hyportage_annex_set_user_configuration(hyportage_annex, user_configuration):
	user_patterns = hyportage_annex[2]
	user_patterns.clear()
	# user data with patterns
	for pattern_set in portage_data.configuration_get_required_package(user_configuration).values():
		user_patterns.update(pattern_set)
	user_patterns.update(portage_data.configuration_get_pattern_accept_keywords(user_configuration).keys())
	user_patterns.update(portage_data.configuration_get_pattern_masked(user_configuration).keys())
	user_patterns.update(portage_data.configuration_get_pattern_configuration(user_configuration).keys())


def hyportage_annex_update_package_list(hyportage_annex, to_add, to_remove):
	package_list = hyportage_annex[3]
	package_list.update(to_add)
	package_list.difference_update(to_remove)


def hyportage_annex_set_last_id(hyportage_annex, last_id):
	hyportage_annex[4][0] = last_id

##


def hyportage_annex_to_save_format(hyportage_annex):
	return {
		'profile_patterns': [portage_data.pattern_to_save_format(pattern) for pattern in hyportage_annex[0]],
		'profile_iuses': list(hyportage_annex[1]),
		'user_patterns': [portage_data.pattern_to_save_format(pattern) for pattern in hyportage_annex[2]],
		'package_list': list(hyportage_annex[3]),
		'last_id': hyportage_annex[4][0]
	}


def hyportage_annex_from_save_format(save_format):
	return (
		set([portage_data.pattern_from_save_format(sf) for sf in save_format['profile_patterns']]),
		set(save_format['profile_iuses']),
		set([portage_data.pattern_from_save_format(sf) for sf in save_format['user_patterns']]),
		set(save_format['package_list']),
		[ save_format['last_id'] ]
		)

