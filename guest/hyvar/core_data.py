#!/usr/bin/python
import re

__author__ = "Michael Lienhardt and Jacopo Mauro"
__copyright__ = "Copyright 2017, Michael Lienhardt and Jacopo Mauro"
__license__ = "ISC"
__version__ = "0.1"
__maintainer__ = "Michael Lienhardt and Jacopo Mauro"
__email__ = "michael lienhardt@laposte.net & mauro.jacopo@gmail.com"
__status__ = "Prototype"


def identity(x): return x


######################################################################
# SPL CORE FUNCTIONS
######################################################################

def parse_package_name(package_name):
	"""
	this function splits a portage package name into relevant information
	:param package_name: the package name to be split
	:return: a tuple containing the group name of this package, its full version and its core version
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


def spl_core_create(parsed_package_name, slot, subslot):
	return parsed_package_name[0], parsed_package_name[1], parsed_package_name[2], slot, subslot


def spl_core_get_spl_group_name(spl_core):
	return spl_core[0]


def spl_core_get_version_full(spl_core):
	return spl_core[1]


def spl_core_get_version(spl_core):
	return spl_core[2]


def spl_core_get_slot(spl_core):
	return spl_core[3]


def spl_core_get_subslot(spl_core):
	return spl_core[4]


######################################################################
# TRANSLATE ATOMS INTO HASHABLE PATTERNS
######################################################################

def pattern_create_from_atom(atom):
	"""
	creates a pattern from a portage atom.
	Note that we don't need to distinguish between `=` and `~` slot operation,
	as they are only used to trigger compilation.
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


def pattern_get_package_group(pattern):
	"""
	return the spl group name at the core of this pattern
	:param pattern: the input pattern
	:return: the spl group name of the input pattern
	"""
	return pattern[1]


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
# MATCHING FUNCTIONS
######################################################################

def compare_version(s1, s2):
	i, len1, len2 = 0, len(s1), len(s2)
	maximum = min(len1, len2)
	while (i < maximum) and (s1[i] == s2[i]):
		i = i + 1
	if i == maximum:
		return len1 - len2
	else:
		if s1[i].isdigit() and s2[i].isdigit():
			n1 = int(re.search("\d+", s1[i:]).group(0))
			n2 = int(re.search("\d+", s2[i:]).group(0))
			return n1 - n2
		else:
			return ord(s1[i]) - ord(s2[i])


def match_only_package_group(pattern, package_group):
	pattern_package_group = pattern_get_package_group(pattern)
	if pattern_package_group == "*/*":
		return True
	elif (pattern_package_group[0] != "*") and (pattern_package_group[-1] != "*"):
		return pattern_package_group == package_group
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
			if not version_full.startswith(pattern_version_full):
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
	pattern_slot, pattern_subslot = pattern[5], pattern[6]
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


def match_spl_full(pattern, spl_core):
	return match_only_package_group(pattern, spl_core_get_spl_group_name(spl_core)) and match_spl_simple(pattern, spl_core)


def match_spl_simple(pattern, spl):
	return (
		match_only_package_version(pattern, spl_core_get_version_full(spl), spl_core_get_version(spl))
		and match_only_slot(pattern, spl_core_get_slot(spl), spl_core_get_subslot(spl))
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


def list_configuration_update(list_configuration, list_configuration2):
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
# SET MANIPULATION DATA
#  (to manipulate list operation as in use.force, or package.mask)
######################################################################

######################################################################
# for USE flags
#  use.force, use.mask, use.stable.force and use.stable.mask
def use_set_construction_create():
	return set(), set()


def use_set_construction_create_from_use_list(use_list):
	res = use_set_construction_create()
	for guarded_use_flag in use_list:
		use_set_construction_add(res, guarded_use_flag)
	return res


def use_set_construction_add(use_set_construction, guarded_use_flag):
	if guarded_use_flag[0] == "-":
		use_set_construction[0].discard(guarded_use_flag)
		use_set_construction[1].add(guarded_use_flag)
	else:
		use_set_construction[0].add(guarded_use_flag)
		use_set_construction[1].discard(guarded_use_flag)


def use_set_construction_update(use_set_construction, other):
	use_set_construction[0].difference_update(other[1])  # remove the remove list
	use_set_construction[0].update(other[0])  # add the add list
	use_set_construction[1].difference_update(other[0])  # remove the add list
	use_set_construction[1].update(other[1])  # add the remove list


def use_set_construction_apply(use_set_construction, use_set):
	use_set.difference_update(use_set_construction[1])
	use_set.update(use_set_construction[0])


def use_set_construction_get(use_set_construction):
	return use_set_construction[0]


######################################################################
# for pattern list
#  package.mask, package.unmask
def pattern_set_construction_create():
	return []


def pattern_set_construction_add(pattern_set_construction, guarded_atom):
	if guarded_atom[0] == "-":
		pattern_set_construction.append( ('-', pattern_create_from_atom(guarded_atom[1:])) )
	else:
		pattern_set_construction.append( ('+', pattern_create_from_atom(guarded_atom)) )


def pattern_set_construction_update(pattern_set_construction, other):
	pattern_set_construction.extend(other)


def pattern_set_construction_contains(pattern_set_construction, spl_core):
	res = False
	for sign, pattern in pattern_set_construction.iteritems():
		if match_spl_full(pattern, spl_core):
			res = sign == "+"
	return res


######################################################################
# for per pattern USE flags
#  package.use.force, package.use.mask, package.use.stable.force and package.use.stable.mask
def pattern_use_set_construction_create():
	return []


def pattern_use_set_construction_add(pattern_use_set_construction, pattern, use_set_construction):
	pattern_use_set_construction.append( (pattern, use_set_construction) )


def pattern_use_set_construction_update(pattern_use_set_construction, other):
	pattern_use_set_construction.extend(other)


def pattern_use_set_construction_apply(pattern_use_set_construction, spl_core, use_set):
	for pattern, use_set_construction in pattern_use_set_construction.iteritems():
		if match_spl_full(pattern, spl_core):
			use_set_construction_apply(use_set_construction, use_set)


def pattern_use_set_construction_get(pattern_use_set_construction, spl_core):
	res = set()
	pattern_use_set_construction_apply(pattern_use_set_construction, spl_core, res)
	return res


######################################################################
# BASE USE SELECTION MANIPULATION
# base information about which use flags are selected, and which are not
# as this information is actually operation, we need to store both positive and negative operation
# https://dev.gentoo.org/~zmedico/portage/doc/man/portage.5.html
# https://wiki.gentoo.org/wiki//etc/portage/package.use
######################################################################

######################################################################
# for USE flags
#  in make.defaults, make.conf and environment's USE variable
def use_selection_create(positive=[], negative=[]):
	return set(positive), set(negative)


def use_selection_create_from_use_list(uses_list):
	res = use_selection_create()
	for use in uses_list:
		if use[0] == "-":
			use_selection_remove(res, use[1:])
		else:
			use_selection_add(res, use)
	return res


def use_selection_create_for_domain(use_selection, domain):
	return (use_selection[0] & domain), (domain - use_selection[0])


def use_selection_copy(use_selection):
	return set(use_selection[0]), set(use_selection[1])


def use_selection_get_positive(use_selection):
	return use_selection[0]


def use_selection_get_negative(use_selection):
	return use_selection[1]


def use_selection_get_uses(use_selection):
	return use_selection[0] | use_selection[1]


def use_selection_add(use_selection, use):
	use_selection[0].add(use)
	use_selection[1].discard(use)


def use_selection_remove(use_selection, use):
	use_selection[0].discard(use)
	use_selection[1].add(use)


def use_selection_update(use_selection, use_configuration):
	use_selection[0].update(use_configuration[0])
	use_selection[1].difference_update(use_configuration[0])
	use_selection[0].difference_update(use_configuration[1])
	use_selection[1].update(use_configuration[1])


def use_selection_to_save_format(use_selection):
	return {'positive': list(use_selection[0]), 'negative': list(use_selection[1])}


def use_selection_from_save_format(save_format):
	return set(save_format['positive']), set(save_format['negative'])


######################################################################
# for per package USE flags
#  in package.use

def pattern_configuration_element_to_save_format(x):
	return { 'pattern': pattern_to_save_format(x[0]), 'use': use_selection_to_save_format(x[1])}


def pattern_configuration_element_from_save_format(x):
	return pattern_from_save_format(x['pattern']), use_selection_from_save_format(x['use'])


pattern_use_selection_create = list_configuration_create


def pattern_use_selection_add(pattern_configuration, pattern, use_configuration):
	list_configuration_add(pattern_configuration, (pattern, use_configuration))


pattern_use_selection_update = list_configuration_update


def pattern_use_selection_to_save_format(pattern_configuration):
	return list_configuration_to_save_format(pattern_configuration, pattern_configuration_element_to_save_format)


def pattern_use_selection_from_save_format(save_format):
	return list_configuration_from_save_format(save_format, pattern_configuration_element_from_save_format)


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


######################################################################
# UTILITY FUNCTIONS
#  (to manipulate list operation as in use.force, or package.mask)
######################################################################

def extract_data_from_iuse_list(iuses_list):
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


######################################################################
# MAIN CONFIG CLASS
######################################################################

class Config(object):
	def __init__(self):
		self._use_order = None
		self.__env_d = None
		self.__repo = None
		self.__defaults = None
		self.__conf = None
		self.__pkg = None
		self.__keyword_list = None
		self.__installed_packages = None
		self.__world = None

	@property
	def use_order(self): return self._use_order

	@use_order.setter
	def use_order(self, data): self._use_order = data

	@property
	def env_d(self): return self.__env_d

	@env_d.setter
	def env_d(self, data): self.__env_d = data

	@property
	def repo(self): return self.__repo

	@repo.setter
	def repo(self, data): self.__repo = data

	@property
	def defaults(self): return self.__defaults

	@defaults.setter
	def defaults(self, data): self.__defaults = data

	@property
	def conf(self): return self.__conf

	@conf.setter
	def conf(self, data): self.__conf = data

	@property
	def pkg(self): return self.__pkg

	@pkg.setter
	def pkg(self, data): self.__pkg = data

	@property
	def keyword_list(self): return self.__keyword_list

	@keyword_list.setter
	def keyword_list(self, data): self.__keyword_list = data

	@property
	def installed_packages(self): return self.__installed_packages

	@installed_packages.setter
	def installed_packages(self, data): self.__installed_packages = data

	@property
	def world(self): return self.__world

	@world.setter
	def world(self, data): self.__world = data


######################################################################
# GETTERS



