#!/usr/bin/python

__author__ = "Michael Lienhardt and Jacopo Mauro"
__copyright__ = "Copyright 2017, Michael Lienhardt and Jacopo Mauro"
__license__ = "ISC"
__version__ = "0.1"
__maintainer__ = "Michael Lienhardt and Jacopo Mauro"
__email__ = "michael lienhardt@laposte.net & mauro.jacopo@gmail.com"
__status__ = "Prototype"


def identity(x): return x


######################################################################
# TRANSLATE ATOMS INTO HASHABLE PATTERNS
######################################################################

def parse_package_name(package_name):
	"""
	this function splits a portage package name into relevant information
	:param package_name: the package name to be split
	:return: a tuple containing the group name of this package, its full version and its core version
	"""
	"""
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
	return package_group, version_full, version


def pattern_create_from_atom(atom):
	"""
	creates a pattern from a portage atom
	:param atom: the string of the atom
	:return: the corresponding pattern
	"""
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
	else:
		atom = atom[begin:]

	# 3. version
	package_group, version_full, version = parse_package_name(atom)
	has_star = False
	if (version_full is not None) and (version_full[-1] == "*"):
		has_star = True
		version_full = version_full[:-1]
		if version[-1] == "*":
			version = version[:-1]
	# return vop, package_group, version_full, version, has_star, slot, subslot, sop
	return vop, package_group, version_full, version, has_star, slot, subslot


def pattern_to_atom(pattern):
	"""
	translates a pattern into its corresponding portage atom
	:param pattern: the pattern to translate
	:return: the equivalent atom string
	"""
	atom = ""
	if pattern[0]: atom += pattern[0]
	atom += pattern[1]
	if pattern[2]: atom += "-" + pattern[2]
	if pattern[4]: atom += "*"
	if pattern[5] or pattern[6]:# or pattern[7]:
		atom += ":"
		if pattern[5]: atom += pattern[5]
		if pattern[6]: atom += "/" + pattern[6]
		# if pattern[7]: atom += pattern[7]
	return atom


def pattern_to_save_format(pattern):
	"""
	translates a pattern into a json-friendly dictionary
	:param pattern: the pattern to translate
	:return: the equivalent dictionary
	"""
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
	"""
	translates a json-friendly representation of a pattern into a real pattern
	:param save_format: the dictionary to translate
	:return: the corresponding pattern
	"""
	return (
		save_format['vop'], save_format['package_group'], save_format['version_full'], save_format['version'],
		save_format['has_star'], save_format['slot'], save_format['subslot'], save_format['sop']
		)

######################################################################
# GENERIC CONFIGURATION MANIPULATION
######################################################################

# generic set configuration


def set_configuration_create(): return set([])


def set_configuration_copy(set_configuration): return set(set_configuration)


def set_configuration_add(set_configuration, el): set_configuration.add(el)


def set_configuration_addall(set_configuration, set_configuration2):
	set_configuration.update(set_configuration2)


def set_configuration_remove(set_configuration, el): set_configuration.discard(el)


def set_configuration_removeall(set_configuration, set_configuration2):
	set_configuration.difference_update(set_configuration2)


def set_configuration_to_save_format(set_configuration, el_to_save_format):
	return [ el_to_save_format(el) for el in set_configuration ]


def set_configuration_to_save_format_simple(set_configuration): return list(set_configuration)



def set_configuration_from_save_format(save_format, el_from_save_format):
	return set([ el_from_save_format(el) for el in save_format ])


def set_configuration_from_save_format_simple(save_format): return set(save_format)


# generic list configuration
# everything with patterns must use ordered lists


def list_configuration_create(): return list([])


def list_configuration_add(list_configuration, el): list_configuration.append(el)


def list_configuration_apply_configuration(list_configuration, list_configuration2):
	list_configuration.extend(list_configuration2)


def list_configuration_to_save_format(list_configuration, el_to_save_format):
	return [ el_to_save_format(el) for el in list_configuration ]


def list_configuration_from_save_format(save_format, el_from_save_format):
	return [ el_from_save_format(el) for el in save_format ]

# generic dict configuration


def dict_configuration_create(): return {}


def dict_configuration_add_el(dict_configuration, key, value, create_function, update_function):
	to_update = dict_configuration.get(key)
	if not to_update:
		to_update = create_function()
		dict_configuration[key] = to_update
	update_function(to_update, value)


def dict_configuration_remove_el(dict_configuration, key, value, remove_function):
	to_update = dict_configuration.get(key)
	if to_update:
		remove_function(to_update, value)


def dict_configuration_add(dict_configuration, key, values):
	dict_configuration[key] = values


def dict_configuration_remove(dict_configuration, key):
	dict_configuration.pop(key)


def dict_configuration_to_save_format(dict_configuration, key_to_save_format, value_to_save_format):
	return [ [ key_to_save_format(k), value_to_save_format(v) ] for k, v in dict_configuration.iteritems() ]


def dict_configuration_from_save_format(save_format, key_from_save_format, value_from_save_format):
	return { key_from_save_format(p[0]): value_from_save_format(p[1]) for p in save_format }


######################################################################
# BASE USE RELATED CONFIGURATION MANIPULATION
# base information about which use flags are selected, and which are not
# as this information is actually operation, we need to store both positive and negative operation
# https://dev.gentoo.org/~zmedico/portage/doc/man/portage.5.html
# https://wiki.gentoo.org/wiki//etc/portage/package.use
######################################################################


def use_selection_create(positive=[], negative=[]):
	return set(positive), set(negative)


def use_selection_copy(use_selection):
	return set(use_selection[0]), set(use_selection[1])


def use_selection_get_positive(use_selection):
	return use_selection[0]


def use_selection_get_negative(use_selection):
	return use_selection[1]


def use_selection_add(use_selection, use):
	use_selection[0].add(use)
	use_selection[1].discard(use)


def use_selection_remove(use_selection, use):
	use_selection[0].discard(use)
	use_selection[1].add(use)


def use_selection_apply_configuration(use_selection, use_configuration):
	use_selection[0].update(use_configuration[0])
	use_selection[1].difference_update(use_configuration[0])
	use_selection[0].difference_update(use_configuration[1])
	use_selection[1].update(use_configuration[1])


def use_selection_create_from_uses_list(uses_list):
	res = use_selection_create()
	for use in uses_list:
		if use[0] == "-":
			use_selection_remove(res, use[1:])
		else:
			use_selection_add(res, use)
	return res


def use_selection_create_from_iuses_list(iuses_list):
	iuse_list = set([])
	use_selection = use_selection_create()
	for iuse in iuses_list:
		if iuse[0] == "+":
			iuse = iuse[1:]
			iuse_list.add(iuse)
			use_selection_add(use_selection, iuse)
		elif iuse[0] == "-":
			iuse = iuse[1:]
			iuse_list.add(iuse)
			use_selection_remove(use_selection, iuse)
		else:
			iuse_list.add(iuse)
	return iuse_list, use_selection


def use_selection_invert(use_selection):
	new_positive = list(use_selection[1])
	new_negative = list(use_selection[0])
	use_selection[0].clear()
	use_selection[0].update(new_positive)
	use_selection[1].clear()
	use_selection[1].update(new_negative)


def use_selection_to_save_format(use_selection):
	return { 'positive': list(use_selection[0]), 'negative': list(use_selection[1])}


def use_selection_from_save_format(save_format):
	return set(save_format['positive']), set(save_format['negative'])


######################################################################
# INSTALLED PACKAGE
######################################################################


package_installed_create = dict_configuration_create


def package_installed_set(package_installed, package_name, use_selection):
	return dict_configuration_add(package_installed, package_name, use_selection)


def package_installed_to_save_format(package_installed):
	return dict_configuration_to_save_format(package_installed, identity, use_selection_to_save_format)


def package_installed_from_save_format(save_format):
	return dict_configuration_from_save_format(save_format, identity, use_selection_from_save_format)


