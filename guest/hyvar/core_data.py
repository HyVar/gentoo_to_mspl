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


def spl_core_create(package_group, version_full, version, slot, subslot):
	return package_group, version_full, version, slot, subslot


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
# DICTIONARY TO SET BASE CLASS
######################################################################

class DictSet(object):
	def __init__(self):
		self.data = {}

	def add(self, key, val):
		if key in self.data:
			self.data[key].add(val)
		else:
			self.data[key] = {val}

	def update(self, dict_set):
		for k, v in dict_set.data.iteritems():
			if k in self.data:
				self.data[k].update(v)
			else: self.data[k] = v


######################################################################
# SET MANIPULATION STRUCTURE
######################################################################

class SetManipulation(object):
	def __init__(self):
		self.positive = set()
		self.negative = set()
		self.remove_all = False

	def add(self, element):
		if element[0] == "-":
			if element[1] != "*":
				element = element[1:]
				self.positive.discard(element)
				if not self.remove_all:
					self.negative.add(element)
			else:
				self.positive.clear()
				self.negative.clear()
				self.remove_all = True
		else:
			self.positive.add(element)
			self.negative.discard(element)

	def add_all(self, elements):
		for element in elements: self.add(element)
		return self

	def update(self, set_manipulation):
		if set_manipulation.remove_all:
			self.positive = set_manipulation.positive
			self.negative.clear()
			self.remove_all = True
		else:
			self.positive.difference_update(set_manipulation.negative)
			self.positive.update(set_manipulation.positive)
			if not self.remove_all:
				self.negative.update(set_manipulation.negative)
				self.negative.difference_update(self.positive)

	def get_elements(self):	return self.positive | self.negative

	def apply(self, s):
		if self.remove_all:
			s.clear()
			s.update(self.positive)
		else:
			s.difference_update(self.negative)
			s.update(self.positive)

	def init(self):
		return self.positive.copy()


class SetManipulationPattern(object):
	def __init__(self):
		self.list = []

	def add(self, pattern, set_manipulation):
		self.list.append( (pattern, set_manipulation) )

	def update(self, set_manipulation_pattern):
		self.list.extend(set_manipulation_pattern.list)

	def apply(self, spl_core, s):
		for pattern, set_manipulation in self.list:
			if match_spl_full(pattern, spl_core):
				set_manipulation.apply(s)

	def init(self, spl_core):
		res = set()
		self.apply(spl_core, res)
		return res


class PatternListManipulation(list):
	def add(self, string):
		if string[0] == "-":
			self.append( (False, pattern_create_from_atom(string[1:])) )
		else:
			self.append( (True, pattern_create_from_atom(string[1:])) )

	def add_all(self, elements):
		for element in elements: self.add(element)
		return self

	update = list.extend

	def contains(self, spl_core):
		res = False
		for add, pattern in self:
			if match_spl_full(pattern, spl_core):
				res = add
		return res


######################################################################
# CONFIGURATION CLASS
######################################################################


class UseSelectionConfig(object):
	def __init__(
			self,
			use=SetManipulation(), use_force=SetManipulation(), use_mask=SetManipulation(),
			use_stable_force=SetManipulation(), use_stable_mask=SetManipulation(),
			pattern_use=SetManipulationPattern(), pattern_use_force=SetManipulationPattern(),
			pattern_use_mask=SetManipulationPattern(),
			pattern_use_stable_force=SetManipulationPattern(), pattern_use_stable_mask=SetManipulationPattern()):
		self.use = use
		self.use_force = use_force
		self.use_mask = use_mask
		self.use_stable_force = use_stable_force
		self.use_stable_mask = use_stable_mask

		self.pattern_use = pattern_use
		self.pattern_use_force = pattern_use_force
		self.pattern_use_mask = pattern_use_mask
		self.pattern_use_stable_force = pattern_use_stable_force
		self.pattern_use_stable_mask = pattern_use_stable_mask

	def update(self, config):
		self.use.update(config.use)
		self.use_force.update(config.use_force)
		self.use_mask.update(config.use_mask)
		self.use_stable_force.update(config.use_stable_force)
		self.use_stable_mask.update(config.use_stable_mask)

		self.pattern_use.update(config.pattern_use)
		self.pattern_use_force.update(config.pattern_use_force)
		self.pattern_use_mask.update(config.pattern_use_mask)
		self.pattern_use_stable_force.update(config.pattern_use_stable_force)
		self.pattern_use_stable_mask.update(config.pattern_use_stable_mask)

	def apply(self, spl_core, is_stable, s):
		self.use.apply(s)
		self.pattern_use.apply(spl_core, s)

		force = self.use_force.init()
		self.pattern_use_force.apply(force)
		if is_stable:
			tmp = self.use_stable_force.init()
			self.pattern_use_stable_force.apply(spl_core, tmp)
			force.update(tmp)

		mask = self.use_mask.init()
		if is_stable:
			tmp = self.use_stable_mask.init()
			self.pattern_use_stable_mask.apply(spl_core, tmp)
			mask.update(tmp)

		s.update(force)
		s.difference_update(mask)

	def init(self, spl_core, is_stable):
		res = set()
		self.apply(spl_core, is_stable, res)
		return res

	def __eq__(self, o):
		if isinstance(o, self.__class__):
			return (
				self.use == o.use and
				self.use_force == o.use_force and
				self.use_mask == o.use_mask and
				self.use_stable_force == o.use_stable_force and
				self.use_stable_mask == o.use_stable_mask and
				self.pattern_use == o.pattern_use and
				self.pattern_use_force == o.pattern_use_force and
				self.pattern_use_mask == o.pattern_use_mask and
				self.pattern_use_stable_force == o.pattern_use_stable_force and
				self.pattern_use_stable_mask == o.pattern_use_stable_mask
			)
		else: return False


# BUG: pattern_mask* is not a SetManipulation, but a list (as patterns can have a non empty intersection, even if not being equal)
class MSPLConfig(object):
	def __init__(
			self, arch=None,
			use_declaration_eapi4=set(), use_declaration_eapi5=set(), use_declaration_hidden_from_user=set(),
			use_selection_config=UseSelectionConfig(),
			pattern_required=DictSet(), pattern_provided=set(),
			pattern_mask=PatternListManipulation(), pattern_unmask=PatternListManipulation(),
			accept_keywords=SetManipulation(), pattern_keywords=SetManipulationPattern(), pattern_accept_keywords=SetManipulationPattern()):
		self.arch = arch

		# sets of USE flags
		self.use_declaration_eapi4 = use_declaration_eapi4
		self.use_declaration_eapi5 = use_declaration_eapi5
		self.use_declaration_hidden_from_user = use_declaration_hidden_from_user

		# set manipulation (with equivalent pattern set manipulation)
		self.use_selection_config = use_selection_config
		self.use_selection_config_init = None

		# mapping from package set name and set of pattern
		self.pattern_required = pattern_required
		# sets of pattern
		self.pattern_provided = pattern_provided

		# set manipulation (with equivalent pattern set manipulation)
		self.pattern_mask = pattern_mask
		self.pattern_unmask = pattern_unmask

		self.accept_keywords = accept_keywords
		self.pattern_keywords = pattern_keywords
		self.pattern_accept_keywords = pattern_accept_keywords

		# form incremental updates
		self.new_masks = True
		self.new_use_declaration_eapi4 = True
		self.new_use_declaration_eapi5 = True
		self.new_keywords_config = True
		self.new_use_flag_config = True

	def update(self, config):
		if config.arch:
			self.arch = config.arch

		self.use_declaration_eapi4.update(config.use_declaration_eapi4)
		self.use_declaration_eapi5.update(config.use_declaration_eapi5)
		self.use_declaration_hidden_from_user.update(config.use_declaration_hidden_from_user)

		self.use_selection_config.update(config.use_selection_config)

		self.pattern_required.update(config.pattern_required)
		self.pattern_provided.update(config.pattern_provided)

		self.pattern_mask.update(config.pattern_mask)
		self.pattern_unmask.update(config.pattern_unmask)

		self.accept_keywords.update(config.accept_keywords)
		self.pattern_keywords.update(config.pattern_keywords)
		self.pattern_accept_keywords.update(config.pattern_accept_keywords)

	def update_pattern_use(self, pattern_use): self.use_selection_config.pattern_use.update(pattern_use)

	def update_pattern_accept_keywords(self, pattern_accept_keywords):
		self.pattern_accept_keywords.update(pattern_accept_keywords)

	def update_pattern_keywords(self, pattern_keywords): self.pattern_keywords.update(pattern_keywords)
	
	def update_pattern_mask(self, pattern_mask): self.pattern_mask.update(pattern_mask)
	
	def update_pattern_unmask(self, pattern_unmask): self.pattern_unmask.update(pattern_unmask)
	
	def update_pattern_required(self, pattern_required): self.pattern_required.update(pattern_required)

	def close_init_phase(self):
		self.use_selection_config_init = self.use_selection_config
		self.use_selection_config = UseSelectionConfig()

	def get_unmasked(self, spl_core):
		return self.pattern_unmask.contains(spl_core) and (not self.pattern_mask.contains(spl_core))

	def get_stability_status(self, spl_core, unmasked, keywords_default):
		if unmasked:
			keywords = keywords_default.copy()
			self.pattern_keywords.apply(spl_core, keywords)
			accept_keywords = {self.arch} if self.arch else set()
			self.accept_keywords.apply(accept_keywords)
			self.pattern_accept_keywords.apply(spl_core, accept_keywords)
			matched = keywords & accept_keywords
			installable = bool(matched)
			is_stable = not bool(filter(lambda x: x[0] == '~', matched))
		else:
			installable = False
			is_stable = False
		return installable, is_stable

	def get_use_flags(self, spl_core, unmasked, is_stable, use_manipulation):
		if unmasked:
			use_flags = self.use_selection_config_init.init(spl_core, is_stable)
			use_manipulation.apply(use_flags)
			self.use_selection_config.apply(spl_core, is_stable, use_flags)
		else:
			use_flags = set()
		return use_flags

	def apply(self, spl_core, use_manipulation, keywords_default):
		# 1. check if the package is masked
		unmasked = self.get_unmasked(spl_core)
		# 2. check if installable and stable
		installable, is_stable = self.get_stability_status(spl_core, unmasked, keywords_default)
		# 3. compute the USE flag configuration (i.e., product)
		use_flags = self.get_use_flags(spl_core, unmasked, is_stable, use_manipulation)
		# 4. return the result
		return unmasked, installable, is_stable, use_flags

	def set_old_config(self, old_config):
		self.new_masks = (self.pattern_mask != old_config.pattern_mask) or (self.pattern_unmask != old_config.pattern_unmask)
		self.new_use_declaration_eapi4 = (self.use_declaration_eapi4 != old_config.use_declaration_eapi4)
		self.new_use_declaration_eapi5 = (self.use_declaration_eapi5 != old_config.use_declaration_eapi5)

		self.new_keywords_config = (self.arch != old_config.arch)
		if not self.new_keywords_config:
			self.new_keywords_config = (self.accept_keywords != old_config.accept_keywords)
		if not self.new_keywords_config:
			self.new_keywords_config = (self.pattern_keywords != old_config.pattern_keywords)
		if not self.new_keywords_config:
			self.new_keywords_config = (self.pattern_accept_keywords != old_config.pattern_accept_keywords)

		self.new_use_flag_config = (self.use_selection_config != old_config.use_selection_config)
		if not self.new_use_flag_config:
			self.new_use_flag_config = (self.use_selection_config_init != old_config.use_selection_config_init)



######################################################################
# MAIN SYSTEM CLASS
######################################################################

# we need the use before the package (use, use.force, use.mask, use.stable.force, package.use, package), and the config after
# plus the other data: keyword list, installed packages, and world


class Config(object):
	def __init__(self):
		self.mspl_config = MSPLConfig()
		self.keyword_list = None
		self.installed_packages = None
		self.world = None


	def close_init_phase(self): self.mspl_config.close_init_phase()












######################################################################
# DEPRECATED
######################################################################





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
# GETTERS



