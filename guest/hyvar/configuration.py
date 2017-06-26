#!/usr/bin/python

identity = lambda x: x
wildcardpattern = "*/*"


######################################################################
### TRANSLATE ATOMS INTO HASHABLE PATTERNS
######################################################################

def parse_package_name(package_name):
	"""
	this function splits a portage package name into relevant information
	"""
	filename_split = package_name.split("-")
	version_full, version = None, None
	end = None
	if len(filename_split) > 1:
		check1 = filename_split[-1]
		check2 = filename_split[-2]
		if check1[0] == 'r' and check2[0].isdigit():
			revision = check1
			version = check2
			version_full = version + "-" + revision
			end = -2
		elif check1[0].isdigit():
			version = check1
			version_full = version
			end = -1
	package_group = "-".join(filename_split[:end])
	return (package_group, version_full, version)


def pattern_create_from_atom(atom):
	#print("parsing atom " + str(atom))
	# 1. version operator
	vop = None
	begin = 0
	if atom[0] in "=<>~":
		if atom[1] == "=":
			vop = atom[:2]
			begin = 2
		else:
			vop = atom[0]
			begin = 1
	# 2. slots
	sop = None
	slot = None
	subslot = None
	slot_position = atom.find(":")
	if slot_position != -1:
		slots = atom[slot_position+1:].split("/")
		atom = atom[begin:slot_position]
		slot = slots[0]
		if slot == "*":
			sop = "*"
			slot = None
		elif slot == "=":
			sop = "="
			slot = None
		elif slot[-1] == "=":
			sop = "="
			slot = slot[:-1]
		elif len(slots) > 1:
			subslot = slots[1]

	# 3. version
	package_group, version_full, version = parse_package_name(atom)
	has_star = False
	if (version_full is not None) and (version_full[-1] == "*"):
		has_star = True
		version_full =  version_full[:-1]
		if version[-1] == "*": version = version[:-1]
	return (vop, package_group, version_full, version, has_star, slot, subslot, sop)


def pattern_to_save_format(pattern):
	return {
		'vop': pattern[0],
		'package_group': pattern[1],
		'version_full': pattern[2],
		'version': pattern[3],
		'has_star': pattern[4],
		'slot': pattern[5],
		'subslot': pattern[6],
		'sop': pattern[7]
	}

def pattern_from_save_format(save_format):
	return (
		save_format['vop'], save_format['package_group'], save_format['version_full'], save_format['version'],
		save_format['has_star'], save_format['slot'], save_format['subslot'], save_format['sop']
		)

######################################################################
### GENERIC CONFIGURATION MANIPULATION
######################################################################

# generic set configuration

def set_configuration_create():
	return set([])

def set_configuration_add(set_configuration, el):
	set_configuration.add(el)

def set_configuration_apply_configuration(set_configuration, set_configuration2):
	set_configuration.update(set_configuration2)


def set_configuration_remove(set_configuration, el):
	set_configuration.discard(el)

def set_configuration_to_save_format(set_configuration, el_to_save_format):
	return [ el_to_save_format(el) for el in set_configuration ]

def set_configuration_from_save_format(save_format, el_from_save_format):
	return set([ el_from_save_format(el) for el in save_format ])

# generic list configuration
# everything with patterns must use ordered lists

def list_configuration_create():
	return list([])

def list_configuration_add(list_configuration, el):
	list_configuration.append(el)

def list_configuration_apply_configuration(list_configuration, list_configuration2):
	list_configuration.extend(list_configuration2)

def list_configuration_to_save_format(list_configuration, el_to_save_format):
	return [ el_to_save_format(el) for el in list_configuration ]

def list_configuration_from_save_format(save_format, el_from_save_format):
	return [ el_from_save_format(el) for el in save_format ]

# generic dict configuration

def dict_configuration_create():
	return {}

def dict_configuration_add(dict_configuration, key, value, create_function, update_function):
	to_update = dict_configuration.get(key)
	if not to_update:
		to_update = create_function()
		dict_configuration[key] = to_update
	update_function(to_update, value)

def dict_configuration_remove(dict_configuration, key, value, remove_function):
	to_update = dict_configuration.get(key)
	if to_update:
		remove_function(to_update, value)

def dict_configuration_set(dict_configuration, key, values):
	dict_configuration[key] = values

def dict_configuration_to_save_format(dict_configuration, key_to_save_format, value_to_save_format):
	return [ [ key_to_save_format(k), value_to_save_format(v) ] for k, v in dict_configuration.iteritems() ]

def dict_configuration_from_save_format(save_format, key_to_save_format, value_to_save_format):
	return { key_from_save_format(p[0]): value_from_save_format(p[1]) for p in save_format.iteritems() }


######################################################################
### BASE CONFIGURATION MANIPULATION
######################################################################


### PROVIDED PACKAGE
# packages stated to be installed, outside portage
# https://wiki.gentoo.org/wiki//etc/portage/profile/package.provided

provided_package_configuration_create = set_configuration_create
provided_package_configuration_add = set_configuration_add
provided_package_configuration_remove = set_configuration_remove
provided_package_configuration_to_save_format = set_configuration_to_save_format
provided_package_configuration_from_save_format = set_configuration_from_save_format


### PACKAGE REQUIREMENT
# mapping between package sets and set of required package
# https://dev.gentoo.org/~zmedico/portage/doc/man/portage.5.html
# https://wiki.gentoo.org/wiki//etc/portage/sets

required_pattern_element_to_save_format = lambda required_pattern_element: set_configuration_to_save_format(required_pattern_element, pattern_to_save_format)
required_pattern_element_from_save_format = lambda save_format: set_configuration_from_save_format(save_format, pattern_from_save_format)

required_pattern_create = dict_configuration_create
required_pattern_add = lambda required_package, package_set, pattern: dict_configuration_add(required_package, package_set, pattern, set_configuration_create, set_configuration_add)
required_pattern_remove = lambda required_package, package_set, pattern: dict_configuration_remove(required_package, package_set, pattern, set_configuration_remove)
required_pattern_to_save_format = lambda required_package: dict_configuration_to_save_format(required_package, identity, required_pattern_element_to_save_format)
required_pattern_from_save_format = lambda save_format: dict_configuration_from_save_format(save_format, identity, required_pattern_element_from_save_format)


### PACKAGE ACCEPTED KEYWORDS
# state for which keywords a package can be installed
# https://dev.gentoo.org/~zmedico/portage/doc/man/portage.5.html
# https://wiki.gentoo.org/wiki//etc/portage/package.accept_keywords

required_package_element_to_save_format = lambda x: { 'pattern': pattern_to_save_format(x[0]), 'keyword': x[1] }
required_package_element_from_save_format = lambda x: ( pattern_from_save_format(x['pattern']), x['keyword'] )

pattern_accept_keywords_create = list_configuration_create
pattern_accept_keywords_add = lambda pattern_accept_keywords, pattern, keywords: list_configuration_add(pattern_accept_keywords, (pattern, keywords))
pattern_accept_keywords_to_save_format = lambda pattern_accept_keywords: list_configuration_to_save_format(pattern_accept_keywords, required_package_element_to_save_format)
pattern_accept_keywords_from_save_format = lambda save_format: list_configuration_from_save_format(save_format, required_package_element_from_save_format)

### MASKED PACKAGES
# which packages can be installed, which cannot
# https://dev.gentoo.org/~zmedico/portage/doc/man/portage.5.html
# https://wiki.gentoo.org/wiki//etc/portage/package.mask

pattern_masked_element_to_save_format = lambda x: { 'pattern': pattern_to_save_format(x[0]), 'sign': x[1] }
pattern_masked_element_from_save_format = lambda x: ( pattern_from_save_format(x['pattern']), x['sign'] )

pattern_masked_create = list_configuration_create
pattern_masked_add = lambda pattern_masked, pattern: list_configuration_add(pattern_masked, (pattern, "+"))
pattern_masked_remove = lambda pattern_masked, pattern: list_configuration_add(pattern_masked, (pattern, "-"))
pattern_masked_to_save_format = lambda pattern_masked: list_configuration_to_save_format(pattern_masked, pattern_masked_element_to_save_format)
pattern_masked_from_save_format = lambda save_format: list_configuration_from_save_format(save_format, pattern_masked_element_from_save_format)



######################################################################
### USE RELATED CONFIGURATION MANIPULATION
######################################################################

## base use configuration

def use_configuration_create(positive=[], negative=[]):
	return ( set(positive), set(negative) )

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

def use_configuration_to_save_format(use_configuration):
	 return { 'positive': list(use_configuration[0]), 'negative': list(use_configuration[1]) }

def use_configuration_from_save_format(save_format):
	return ( set(save_format['positive']), set(save_format['negative']) )


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

### IUSE CONFIGURATION

def iuse_configuration_create():
	return ( set_configuration_create(), use_configuration_create() )

def iuse_configuration_update(iuse_configuration, use):
	set_configuration_add(iuse_configuration[0], use)

def iuse_configuration_add(iuse_configuration, use):
	set_configuration_add(iuse_configuration[0], use)
	use_configuration_add(iuse_configuration[1], use)

def iuse_configuration_remove(iuse_configuration, use):
	set_configuration_add(iuse_configuration[0], use)
	use_configuration_remove(iuse_configuration[1], use)

def iuse_configuration_apply_configuration(iuse_configuration, iuse_configuration2):
	set_configuration_apply_configuration(use_configuration[0], iuse_configuration2[0])
	use_configuration_apply_configuration(use_configuration[1], iuse_configuration2[1])

def iuse_configuration_to_save_format(iuse_configuration):
	res = use_configuration_to_save_format(iuse_configuration[1])
	res['iuse'] = set_configuration_to_save_format(iuse_configuration[0])
	return res

def iuse_configuration_from_save_format(save_format):
	return ( set_configuration_from_save_format(save_format['iuse']), use_configuration_from_save_format(save_format) )

def iuse_configuration_create_from_iuses_list(iuses_list):
	res = iuse_configuration_create()
	for iuse in iuses_list:
		if iuse[0] == "+":
			iuse_configuration_add(res, iuse[1:])
		elif iuse[0] == "-":
			iuse_configuration_remove(res, use[1:])
		else:
			iuse_configuration_update(res, use)
	return res


### PACKAGE USE

pattern_configuration_element_to_save_format = lambda x: { 'pattern': pattern_to_save_format(x[0]), 'use': use_configuration_to_save_format(x[1]) }
pattern_configuration_element_from_save_format = lambda x: ( pattern_from_save_format(x['pattern']), use_configuration_from_save_format(x['use']) )

pattern_configuration_create = list_configuration_create
pattern_configuration_add = lambda pattern_configuration, pattern, use_configuration: list_configuration_add(pattern_configuration, (pattern, use_configuration))
pattern_configuration_to_save_format = lambda pattern_configuration: list_configuration_to_save_format(pattern_configuration, pattern_configuration_element_to_save_format)
pattern_configuration_from_save_format = lambda save_format: list_configuration_from_save_format(save_format, pattern_configuration_element_from_save_format)

### INSTALLED PACKAGE

package_installed_create = dict_configuration_create
package_installed_add = lambda package_installed, package_name, use_configuration: dict_configuration_add(package_installed, package_name, use_configuration, use_configuration_create, use_configuration_add)
package_installed_set = lambda package_installed, package_name, use_configuration: dict_configuration_set(package_installed, package_name, use_configuration)
package_installed_to_save_format = lambda package_installed: dict_configuration_to_save_format(package_installed, use_configuration_to_save_format)
package_installed_from_save_format = lambda save_format: dict_configuration_from_save_format(save_format, use_configuration_from_save_format)


######################################################################
### USE RELATED CONFIGURATION MANIPULATION
######################################################################



def configuration_create():
	return (
		["no-arch"],
		provided_package_configuration_create(),
		required_package_create(),
		pattern_accept_keywords_create(),
		pattern_masked_create(),
		iuse_configuration_create(),
		pattern_configuration_create()
		)

def configuration_set_arch(configuration, arch):
	configuration[0][0] = arch

configuration_get_provided_package = lambda configuration: configuration[1]
configuration_get_required_package = lambda configuration: configuration[2]
configuration_get_pattern_accept_keywords = lambda configuration: configuration[3]
configuration_get_pattern_masked = lambda configuration: configuration[4]
configuration_get_iuse = lambda configuration: configuration[5]
configuration_get_pattern_configuration = lambda configuration: configuration[6]

def configuration_to_save_format(configuration):
	return {
		'arch': configuration[0],
		'provided_package': provided_package_configuration_to_save_format(configuration_get_provided_package(configuration)),
		'required_package': required_package_to_save_format(configuration_get_required_package(configuration)),
		'package_accept_keywords': pattern_accept_keywords_to_save_format(configuration_get_pattern_accept_keywords(configuration)),
		'package_mask': pattern_masked_to_save_format(configuration_get_pattern_masked(configuration)),
		'iuse': iuse_configuration_to_save_format(configuration_get_iuse(configuration)),
		'pattern_use': pattern_configuration_to_save_format(configuration_get_pattern_configuration(configuration))
		}

def configuration_from_save_format(save_format):
	return (
		save_format['arch'],
		provided_package_configuration_to_save_format(save_format['provided_package']),
		required_package_to_save_format(save_format['required_package']),
		pattern_accept_keywords_to_save_format(save_format['package_accept_keywords']),
		pattern_masked_to_save_format(save_format['package_mask']),
		iuse_configuration_to_save_format(save_format['iuse']),
		pattern_configuration_to_save_format(save_format['pattern_use'])
		)
