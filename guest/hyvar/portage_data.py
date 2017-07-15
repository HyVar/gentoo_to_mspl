#!/usr/bin/python


import core_data


wildcardpattern = "*/*"

######################################################################
# KEYWORD SET (the list of declared keywords)
# See the /usr/portage/profiles/arch.list for a list of keywords
######################################################################

keyword_set_create = core_data.set_configuration_create
keyword_set_add = core_data.set_configuration_add
keyword_set_remove = core_data.set_configuration_remove
keyword_set_to_save_format = core_data.set_configuration_to_save_format
keyword_set_from_save_format = core_data.set_configuration_from_save_format


######################################################################
# PROVIDED PACKAGE
# packages stated to be installed, outside portage
# https://wiki.gentoo.org/wiki//etc/portage/profile/package.provided
######################################################################

provided_package_configuration_create = core_data.set_configuration_create
provided_package_configuration_add = core_data.set_configuration_add
provided_package_configuration_remove = core_data.set_configuration_remove
provided_package_configuration_to_save_format = core_data.set_configuration_to_save_format
provided_package_configuration_from_save_format = core_data.set_configuration_from_save_format


######################################################################
# PACKAGE REQUIREMENT
# mapping between package sets and set of required package
# https://dev.gentoo.org/~zmedico/portage/doc/man/portage.5.html
# https://wiki.gentoo.org/wiki//etc/portage/sets
######################################################################


def required_pattern_element_to_save_format(required_pattern_element):
	return core_data.set_configuration_to_save_format(required_pattern_element, core_data.pattern_to_save_format)


def required_pattern_element_from_save_format(save_format):
	return core_data.set_configuration_from_save_format(save_format, core_data.pattern_from_save_format)

##

required_pattern_create = core_data.dict_configuration_create


def required_pattern_add(required_package, package_set, pattern):
	return core_data.dict_configuration_add(required_package, package_set, pattern, core_data.set_configuration_create, core_data.set_configuration_add)


def required_pattern_remove(required_package, package_set, pattern):
	return core_data.dict_configuration_remove(required_package, package_set, pattern, core_data.set_configuration_remove)


def required_pattern_to_save_format(required_package):
	return core_data.dict_configuration_to_save_format(required_package, core_data.identity, required_pattern_element_to_save_format)


def required_pattern_from_save_format(save_format):
	return core_data.dict_configuration_from_save_format(save_format, core_data.identity, required_pattern_element_from_save_format)


######################################################################
# PACKAGE ACCEPTED KEYWORDS
# state for which keywords a package can be installed
# https://dev.gentoo.org/~zmedico/portage/doc/man/portage.5.html
# https://wiki.gentoo.org/wiki//etc/portage/package.accept_keywords
######################################################################

def required_package_element_to_save_format(x): return { 'pattern': core_data.pattern_to_save_format(x[0]), 'keyword': x[1] }


def required_package_element_from_save_format(x): return core_data.pattern_from_save_format(x['pattern']), x['keyword']

##

pattern_accept_keywords_create = core_data.list_configuration_create


def pattern_accept_keywords_add(pattern_accept_keywords, pattern, keywords):
	return core_data.list_configuration_add(pattern_accept_keywords, (pattern, keywords))


def pattern_accept_keywords_to_save_format(pattern_accept_keywords):
	return core_data.list_configuration_to_save_format(pattern_accept_keywords, required_package_element_to_save_format)


def pattern_accept_keywords_from_save_format(save_format):
	return core_data.list_configuration_from_save_format(save_format, required_package_element_from_save_format)


######################################################################
# MASKED PACKAGES
# which packages can be installed, which cannot
# https://dev.gentoo.org/~zmedico/portage/doc/man/portage.5.html
# https://wiki.gentoo.org/wiki//etc/portage/package.mask
######################################################################

def pattern_masked_element_to_save_format(x):
	return { 'pattern': core_data.pattern_to_save_format(x[0]), 'sign': x[1] }


def pattern_masked_element_from_save_format(x):
	return core_data.pattern_from_save_format(x['pattern']), x['sign']

##

pattern_masked_create = core_data.list_configuration_create


def pattern_masked_add(pattern_masked, pattern):
	return core_data.list_configuration_add(pattern_masked, (pattern, True))


def pattern_masked_remove(pattern_masked, pattern):
	return core_data.list_configuration_add(pattern_masked, (pattern, False))


def pattern_masked_to_save_format(pattern_masked):
	return core_data.list_configuration_to_save_format(pattern_masked, pattern_masked_element_to_save_format)


def pattern_masked_from_save_format(save_format):
	return core_data.list_configuration_from_save_format(save_format, pattern_masked_element_from_save_format)


######################################################################
# BASE USE RELATED CONFIGURATION MANIPULATION
# base information about which use flags are selected, and which are not
# as this information is actually operation, we need to store both positive and negative operation
# https://dev.gentoo.org/~zmedico/portage/doc/man/portage.5.html
# https://wiki.gentoo.org/wiki//etc/portage/package.use
######################################################################


def use_configuration_create(positive=[], negative=[]):
	return set(positive), set(negative)


def use_configuration_get_positive(use_configuration):
	return use_configuration[0]


def use_configuration_get_negative(use_configuration):
	return use_configuration[1]


def use_configuration_add(use_configuration, use):
	use_configuration[0].add(use)
	use_configuration[1].discard(use)


def use_configuration_remove(use_configuration, use):
	use_configuration[0].discard(use)
	use_configuration[1].add(use)


def use_configuration_apply_configuration(use_configuration, use_configuration2):
	use_configuration[0].update(use_configuration2[0])
	use_configuration[1].difference_update(use_configuration2[0])
	use_configuration[0].difference_update(use_configuration2[1])
	use_configuration[1].update(use_configuration2[1])


def use_configuration_create_from_uses_list(uses_list):
	res = use_configuration_create()
	for use in uses_list:
		if use[0] == "-":
			use_configuration_remove(res, use[1:])
		else:
			use_configuration_add(res, use)
	return res


def use_configuration_invert(use_configuration):
	new_positive = list(use_configuration[1])
	new_negative = list(use_configuration[0])
	use_configuration[0].clear()
	use_configuration[0].update(new_positive)
	use_configuration[1].clear()
	use_configuration[1].update(new_negative)


def use_configuration_to_save_format(use_configuration):
	return { 'positive': list(use_configuration[0]), 'negative': list(use_configuration[1]) }


def use_configuration_from_save_format(save_format):
	return set(save_format['positive']), set(save_format['negative'])


######################################################################
# IUSE CONFIGURATION
# global and implicit iuse flag declaration and configuration
# https://dev.gentoo.org/~zmedico/portage/doc/man/portage.5.html
######################################################################

def iuse_configuration_create():
	return core_data.set_configuration_create(), use_configuration_create()


def iuse_configuration_get_iuses(iuse_configuration): return iuse_configuration[0]


def iuse_configuration_get_use_configuration(iuse_configuration): return iuse_configuration[1]

##


def iuse_configuration_update(iuse_configuration, use):
	core_data.set_configuration_add(iuse_configuration[0], use)


def iuse_configuration_add(iuse_configuration, use):
	core_data.set_configuration_add(iuse_configuration[0], use)
	use_configuration_add(iuse_configuration[1], use)


def iuse_configuration_remove(iuse_configuration, use):
	core_data.set_configuration_add(iuse_configuration[0], use)
	use_configuration_remove(iuse_configuration[1], use)


def iuse_configuration_apply_configuration(iuse_configuration, iuse_configuration2):
	core_data.set_configuration_addall(iuse_configuration[0], iuse_configuration2[0])
	use_configuration_apply_configuration(iuse_configuration[1], iuse_configuration2[1])


def iuse_configuration_to_save_format(iuse_configuration):
	res = use_configuration_to_save_format(iuse_configuration[1])
	res['iuse'] = core_data.set_configuration_to_save_format(iuse_configuration[0])
	return res


def iuse_configuration_from_save_format(save_format):
	return ( core_data.set_configuration_from_save_format(save_format['iuse']), use_configuration_from_save_format(save_format) )


def iuse_configuration_create_from_iuses_list(iuses_list):
	res = iuse_configuration_create()
	for iuse in iuses_list:
		if iuse[0] == "+":
			iuse_configuration_add(res, iuse[1:])
		elif iuse[0] == "-":
			iuse_configuration_remove(res, iuse[1:])
		else:
			iuse_configuration_update(res, iuse)
	return res


######################################################################
# PACKAGE USE
# https://dev.gentoo.org/~zmedico/portage/doc/man/portage.5.html
# https://wiki.gentoo.org/wiki//etc/portage/package.use
######################################################################

def pattern_configuration_element_to_save_format(x):
	return { 'pattern': core_data.pattern_to_save_format(x[0]), 'use': use_configuration_to_save_format(x[1]) }


def pattern_configuration_element_from_save_format(x):
	return ( core_data.pattern_from_save_format(x['pattern']), use_configuration_from_save_format(x['use']) )

##

pattern_configuration_create = core_data.list_configuration_create


def pattern_configuration_add(pattern_configuration, pattern, use_configuration):
	return core_data.list_configuration_add(pattern_configuration, (pattern, use_configuration))


def pattern_configuration_to_save_format(pattern_configuration):
	return core_data.list_configuration_to_save_format(pattern_configuration, pattern_configuration_element_to_save_format)


def pattern_configuration_from_save_format(save_format):
	return core_data.list_configuration_from_save_format(save_format, pattern_configuration_element_from_save_format)


######################################################################
# INSTALLED PACKAGE
######################################################################

package_installed_create = core_data.dict_configuration_create


def package_installed_add(package_installed, package_name, use_configuration):
	return core_data.dict_configuration_add(package_installed, package_name, use_configuration, use_configuration_create, use_configuration_add)


def package_installed_set(package_installed, package_name, use_configuration):
	return core_data.dict_configuration_set(package_installed, package_name, use_configuration)


def package_installed_to_save_format(package_installed):
	return core_data.dict_configuration_to_save_format(package_installed, use_configuration_to_save_format)


def package_installed_from_save_format(save_format):
	return core_data.dict_configuration_from_save_format(save_format, use_configuration_from_save_format)


######################################################################
# FULL CONFIGURATION MANIPULATION
######################################################################


def configuration_create():
	return (
		["no-arch"],
		provided_package_configuration_create(),
		required_pattern_create(),
		pattern_accept_keywords_create(),
		pattern_masked_create(),
		iuse_configuration_create(),
		pattern_configuration_create()
		)


def configuration_get_arch(configuration): return configuration[0][0]
def configuration_get_provided_package(configuration): return configuration[1]
def configuration_get_pattern_required(configuration): return configuration[2]
def configuration_get_pattern_accept_keywords(configuration): return configuration[3]
def configuration_get_pattern_masked(configuration): return configuration[4]
def configuration_get_iuse_configuration(configuration): return configuration[5]
def configuration_get_pattern_configuration(configuration): return configuration[6]


def configuration_set_arch(configuration, arch): configuration[0][0] = arch



def configuration_to_save_format(configuration):
	return {
		'arch': configuration[0],
		'provided_package': provided_package_configuration_to_save_format(configuration_get_provided_package(configuration)),
		'required_package': required_pattern_to_save_format(configuration_get_pattern_required(configuration)),
		'package_accept_keywords': pattern_accept_keywords_to_save_format(configuration_get_pattern_accept_keywords(configuration)),
		'package_mask': pattern_masked_to_save_format(configuration_get_pattern_masked(configuration)),
		'iuse': iuse_configuration_to_save_format(configuration_get_iuse_configuration(configuration)),
		'package_use': pattern_configuration_to_save_format(configuration_get_pattern_configuration(configuration))
		}


def configuration_from_save_format(save_format):
	return (
		save_format['arch'],
		provided_package_configuration_from_save_format(save_format['provided_package']),
		required_pattern_from_save_format(save_format['required_package']),
		pattern_accept_keywords_from_save_format(save_format['package_accept_keywords']),
		pattern_masked_from_save_format(save_format['package_mask']),
		iuse_configuration_from_save_format(save_format['iuse']),
		pattern_configuration_from_save_format(save_format['package_use'])
		)
