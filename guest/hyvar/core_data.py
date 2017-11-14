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

class dictSet(dict):
	"""
	This class is used as a container for
		- required patterns (mapping between set names to sets of patterns)
		- installed packages (mapping between package names to use flag selection)
	"""
	def add(self, key, val):
		if key in self:
			self[key].add(val)
		else:
			self[key] = {val}

	def set(self, key, values):
		self[key] = values

	def update_set(self, dict_set):
		for k, v in dict_set.iteritems():
			if k in self:
				self[k].update(v)
			else: self[k] = v


######################################################################
# SET MANIPULATION STRUCTURE
######################################################################

class SetManipulation(object):
	"""
	this class is used for encoding
		- use flag manipulation (use in make.default, use.force, use.mask, use.stable.force and use.stable.mask)
		- keyword list manipulation
	As checked in the tests, "-*" is a valid atom in these files, and so it is included in this class
	"""
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
	"""
	this class is used for all the set manipulation files that are guarded by a specific pattern
		- use flag manipulation for specific patterns (package.use, package.use.force, etc)
		- keyword manipulation for specific patterns (package.keywords, package.accept_keywords)
	"""
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
	"""
	this class is used for simple list of patterns:
		- package masking (package.mask, package.unmask)
	"""
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
	"""
	This class stores all the kind of use flag manipulation in portage:
		- use variable in make.default
		- use.force, use.mask, use.stable.force, use.stable.mask
		- package.use, package.use.force, package.use.mask, package.use.stable.force and package.use.stable.mask
	Additionally, this class have a method to apply these manipulations on a use flag selection
	"""
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

	def apply(self, spl_core, is_stable, selection):
		self.use.apply(selection)
		self.pattern_use.apply(spl_core, selection)

		force = self.use_force.init()
		self.pattern_use_force.apply(spl_core, force)
		if is_stable:
			tmp = self.use_stable_force.init()
			self.pattern_use_stable_force.apply(spl_core, tmp)
			force.update(tmp)

		mask = self.use_mask.init()
		if is_stable:
			tmp = self.use_stable_mask.init()
			self.pattern_use_stable_mask.apply(spl_core, tmp)
			mask.update(tmp)

		selection.update(force)
		selection.difference_update(mask)

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


class MSPLConfig(object):
	"""
	This class contains all the information related to package/spl configuration
		- architecture for the hardware
		- use flag implicit declaration (for eapi4 and less, and for eapi5 and more)
		- use flags that are hidden from the user (can be useful for consistent output to the user)
		- use flag manipulation (before and after the manipulation specified in the package itself)
		- package requirement
		- packages provided outside of portage
		- keywords and visibility (mask) manipulation
	This class also contains a method "combine" to add the information contained in another MSPLConfig object into this
	one and is used to compute this data incrementally from the different configuration files in portage.
	Finally, we have the "apply" method that compute relevant data (visibility and use flag selection) for a package.
	"""
	def __init__(
			self, arch=None,
			use_declaration_eapi4=set(), use_declaration_eapi5=set(), use_declaration_hidden_from_user=set(),
			use_selection_config=UseSelectionConfig(),
			pattern_required=dictSet(), pattern_provided=set(),
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
		self.pattern_required_flat = None
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

		self.pattern_required.update_set(config.pattern_required)
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
	
	def update_pattern_required(self, pattern_required): self.pattern_required.update_set(pattern_required)

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

	def set_required_patterns(self):
		self.pattern_required_flat = {el for k, v in self.pattern_required.iteritems() for el in v}

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


class Config(object):
	"""
	This class contains the full configuration of portage.
	In addition to the MSPL configuration, this class contains:
		- the list of keywords declared in portage
		- the list of installed package, with their use flag selection
		- the world list, that lists all the patterns required by the user,
			accumulated during his previous "emerge" calls.
		- the use flag manipulation stated by the user in the environment
	Consequently, this class have an "apply" wrapper method around the "apply" method of the MSPL configuration,
	that also apply the use flag manipulation from the environment
	"""
	def __init__(self):
		self.mspl_config = MSPLConfig()
		self.keyword_list = None
		self.installed_packages = None
		self.world = None
		self.use_manipulation_env = None
		self.pattern_required_flat = None

	def set_use_manipulation_env(self, use_flag_manipulation):
		self.use_manipulation_env = SetManipulation()
		self.use_manipulation_env.add_all(use_flag_manipulation)

	def apply(self, spl_core, use_manipulation, keywords_default):
		unmasked, installable, is_stable, use_flags = self.mspl_config.apply(spl_core, use_manipulation, keywords_default)
		if installable:
			use_flags = self.use_manipulation_env.apply(use_flags)
		return unmasked, installable, is_stable, use_flags

	def close_init_phase(self): self.mspl_config.close_init_phase()

	def set_required_patterns(self):
		self.mspl_config.set_required_patterns()
		self.pattern_required_flat = self.mspl_config.pattern_required_flat | self.world






