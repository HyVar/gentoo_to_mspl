import core_data
import portage_data
import hyportage_data
import hyportage_pattern


def core_configuration_create():
	return (
		set(),  # the set of patterns used in the profile configuration
		set(),  # the set of patterns used in the user configuration
		set(),  # implicit iuse list
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
	hyportage_data.spl_set_keywords_default(keyword_default)


def keywords_apply_configuration_pattern(spl, pattern_repository, conf_keywords):
	res = False
	for pattern, keyword_list in conf_keywords:
		if spl in hyportage_pattern.pattern_repository_get(pattern_repository, pattern)[1]:
			res = res or bool(keyword_list & hyportage_data.spl_get_keywords_list(spl))
	return res


def iuses_apply_configuration(iuses, conf_iuses):
	pass  # non need to update the iuse list


def use_selection_apply_configuration(use_selection, conf_use):
	hyportage_data.use_selection_addall(use_selection, core_data.use_configuration_get_positive(conf_use))
	hyportage_data.use_selection_removeall(use_selection, core_data.use_configuration_get_negative(conf_use))


def use_selection_apply_configuration_pattern(spl, pattern_repository, use_selection, conf_use):
	for pattern, use_configuration in conf_use:
		if spl in hyportage_pattern.pattern_repository_get(pattern_repository, pattern)[1]:
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


def apply_configurations(core_configuration, conf_profile, conf_user, is_conf_profile_new, is_conf_user_new, new_spls, mspl, pattern_repository):
	# 1. update the pattern repository
	if is_conf_profile_new:
		conf_patterns = get_configuration_pattern(conf_profile)
		core_conf_patterns = core_configuration_get_profile_patterns(core_configuration)
		for pattern in conf_patterns - core_conf_patterns:
			hyportage_pattern.pattern_repository_add_pattern(pattern_repository, pattern)
		for pattern in core_conf_patterns - conf_patterns:
			hyportage_pattern.pattern_repository_remove_pattern(pattern_repository, pattern)
		core_conf_patterns.clear()
		core_conf_patterns.update(conf_patterns)
	if is_conf_user_new:
		conf_patterns = get_configuration_pattern(conf_user)
		core_conf_patterns = core_configuration_get_user_patterns(core_configuration)
		for pattern in conf_patterns - core_conf_patterns:
			hyportage_pattern.pattern_repository_add_pattern(pattern_repository, pattern)
		for pattern in core_conf_patterns - conf_patterns:
			hyportage_pattern.pattern_repository_remove_pattern(pattern_repository, pattern)
		core_conf_patterns.clear()
		core_conf_patterns.update(conf_patterns)
	# 2. update the arch if necessary
	if is_conf_profile_new:
		core_configuration_set_arch(core_configuration, portage_data.configuration_get_arch(conf_profile))
	arch = core_configuration_get_arch(core_configuration)
	# 3. update the spls
	for spl in new_spls:
		keywords_initialize(spl, arch)
		spl_apply_profile_configuration(spl, pattern_repository, conf_profile)
		spl_apply_user_configuration(spl, pattern_repository, conf_user)
	if (not is_conf_profile_new) and (not is_conf_user_new):  # the configuration was not updated, and only the new_spls must be managed then.
		return new_spls, new_spls  # return the set of modified spls, and the set of spls with a modified keyword set/mask
	if is_conf_profile_new:
		for spl in mspl.values():
			spl_apply_profile_configuration(spl, pattern_repository, conf_profile)
	spl_modified_data = set(new_spls)
	spl_modified_visibility = set(new_spls)
	if is_conf_profile_new or is_conf_user_new:
		for spl in mspl.values():
			updated_data, updated_visibility = spl_apply_user_configuration(spl, pattern_repository, conf_user)
			if updated_data: spl_modified_data.add(spl)
			if updated_visibility: spl_modified_visibility.add(spl)
	return spl_modified_data, spl_modified_visibility




######################################################################
# HYPORTAGE ANNEX CREATION
######################################################################

# wouldn't it be possible to simply store the two configurations here, and compute diff?
# we need to know for each element if it is different
# well, ok, for each elements,

## stores:
# - patterns in the profile configuration		: useful for pattern repository garbage collection
# - iuses declared in the profile configuration	: useful to update the iuse list of the packages
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



