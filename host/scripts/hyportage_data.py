#!/usr/bin/python

import core_data

import hyportage_constraint_ast
import hyportage_ids
import hyportage_pattern
import hyportage_configuration

######################################################################
# KEYWORDS MANIPULATION
######################################################################

keywords_create = core_data.set_configuration_create
keywords_copy = core_data.set_configuration_copy

keywords_to_save_format = core_data.set_configuration_to_save_format
keywords_from_save_format = core_data.set_configuration_from_save_format


######################################################################
# IUSE MANIPULATION
######################################################################

iuses_create = core_data.set_configuration_create
iuses_copy = core_data.set_configuration_copy

iuses_add = core_data.set_configuration_add
iuses_addall = core_data.set_configuration_addall

iuses_to_save_format = core_data.set_configuration_to_save_format_simple
iuses_from_save_format = core_data.set_configuration_from_save_format_simple


######################################################################
# USE SELECTION MANIPULATION
######################################################################


use_selection_create = core_data.use_selection_create
use_selection_copy = core_data.use_selection_copy
use_selection_create_from_iuses_list = core_data.use_selection_create_from_iuses_list
use_selection_add = core_data.use_selection_add
use_selection_remove = core_data.use_selection_remove
use_selection_apply_configuration = core_data.use_selection_apply_configuration
use_selection_to_save_format = core_data.use_selection_to_save_format
use_selection_from_save_format = core_data.use_selection_from_save_format


##

######################################################################
# DEPENDENCIES MANIPULATION
######################################################################


dependencies_create = core_data.dict_configuration_create


def dependencies_add_pattern(raw_dependencies, pattern):
	if pattern not in raw_dependencies: raw_dependencies[pattern] = set([])


def dependencies_add_pattern_use(raw_dependencies, pattern, use):
	raw_dependencies[pattern].add(use)


def dependencies_get_patterns(raw_dependencies): return raw_dependencies.keys()


##

def dependencies_to_save_format(dependencies):
	return core_data.dict_configuration_to_save_format(
		dependencies, hyportage_pattern.pattern_to_save_format, core_data.set_configuration_to_save_format_simple)


def dependencies_from_save_format(save_format):
	return core_data.dict_configuration_from_save_format(
		save_format, hyportage_pattern.pattern_from_save_format, core_data.set_configuration_from_save_format_simple)


######################################################################
# SPL AND MSPL MANIPULATION
######################################################################

class SPL(object):
	def __init__(
			self,
			name, group, deprecated,
			version_full, version,
			slot, subslot,
			fm_local, fm_combined,
			dependencies, required_iuses_local, keywords_list,
			iuses_default, use_selection_default):
		self.name                  = name
		self.group                 = group
		self.deprecated            = deprecated
		self.version_full          = version_full
		self.version               = version
		self.slot                  = slot
		self.subslot               = subslot
		self.slots                 = (slot, subslot)
		self.fm_local              = fm_local               # the part of the feature model related to local features, i.e., portage's REQUIRED_USE
		self.fm_combined           = fm_combined            # the part of the feature model relatd to external dependencies, i.e., portage's DEPEND + RDEPEND + PDEPEND
		self.smt_constraint        = None                   # translation of the full feature model into z3 constraints
		self.dependencies          = dependencies           # mapping from pattern dependencies to list of features they must have declared
		self.required_iuses_local  = required_iuses_local   # list of local features mentioned in local constraints
		self.required_iuses        = None                   # list of features that must be declared in this spl
		self.iuses_default         = iuses_default          # list of features declared in this spl by default
		self.iuses_profile         = None                   # previous list extended with features implicitly declared by portage
		self.iuses_user            = None                   # previous list extended with features implicitly declared by user
		self.keywords_list         = keywords_list          # list of architectures valid for this spl
		self.keywords_default      = None                   # boolean stating if this spl can be installed by default on the current architecture
		self.keywords_profile      = None                   # boolean stating if this spl can be installed, considering the default portage information
		self.keywords_user         = None                   # boolean stating if this spl can be installed, considering both default and user configuration
		self.use_selection_default = use_selection_default  # default use selection
		self.use_selection_profile = None                   # use selection considering default portage information
		self.use_selection_user    = None                   # use selection considering both default and user configuration
		self.mask_profile          = None                   # if portage states that this spl is masked or not
		self.mask_user             = None                   # if this spl is masked, considering both default and user configuration
		self.visited               = False                  # if the spl was visited in a graph traversal
		# self.has_several_parents   = False                  # if there are two paths to access this spl during graph traversal

	def __hash__(self): return hash(self.name)

	def __eq__(self, other):
		if isinstance(other, (str, unicode)):
			# need to compare the object also with a string to be able to retrieve mspl[x] when x is a string
			return self.name == other
		else:
			return self.name == other.name


def spl_get_name(spl): return spl.name
def spl_get_group_name(spl): return spl.group
def spl_get_slot(spl): return spl.slot
def spl_get_subslot(spl): return spl.subslot
def spl_get_slots(spl): return spl.slots
def spl_get_version(spl): return spl.version
def spl_get_version_full(spl): return spl.version_full
def spl_get_dependencies(spl): return spl.dependencies
def spl_is_deprecated(spl): return spl.deprecated


def spl_get_fm_local(spl): return spl.fm_local
def spl_get_fm_combined(spl): return spl.fm_combined
def spl_get_smt_constraint(spl): return spl.smt_constraint


def spl_get_required_iuses_local(spl): return spl.required_iuses_local
def spl_get_required_iuses(spl): return spl.required_iuses


def spl_get_keywords_list(spl): return spl.keywords_list
def spl_get_keywords_default(spl): return spl.keywords_default
def spl_get_keywords_profile(spl): return spl.keywords_profile
def spl_get_keywords_user(spl): return spl.keywords_user


def spl_get_iuses_default(spl): return spl.iuses_default
def spl_get_iuses_profile(spl): return spl.iuses_profile
def spl_get_iuses_user(spl): return spl.iuses_user


def spl_get_use_selection_default(spl): return spl.use_selection_default
def spl_get_use_selection_profile(spl): return spl.use_selection_profile
def spl_get_use_selection_user(spl): return spl.use_selection_user


def spl_get_mask_profile(spl): return spl.mask_profile
def spl_get_mask_user(spl): return spl.mask_user


def spl_is_visible(spl): return spl_get_keywords_user(spl) and (not spl_get_mask_user(spl))


def spl_is_visited(spl): return spl.visited

##


def spl_set_keywords_default(spl, keywords): spl.keywords_default = keywords
def spl_set_keywords_profile(spl, keywords): spl.keywords_profile = keywords
def spl_set_iuses_profile(spl, new_iuses): spl.iuses_profile = new_iuses
def spl_set_use_selection_profile(spl, new_use_selection): spl.use_selection_profile = new_use_selection
def spl_set_mask_profile(spl, new_mask): spl.mask_profile = new_mask


def spl_set_keywords_user(spl, keywords): spl.keywords_user = keywords
def spl_set_iuses_user(spl, new_iuses): spl.iuses_user = new_iuses
def spl_set_use_selection_user(spl, new_use_selection): spl.use_selection_user = new_use_selection
def spl_set_mask_user(spl, new_mask): spl.mask_user = new_mask


def spl_reset_required_iuses(spl, pattern_repository):
	spl.required_iuses = list(set.intersection(spl_get_iuses_user(spl), set.union(
		spl.required_iuses_local,
		hyportage_pattern.pattern_repository_get_spl_required_use(pattern_repository, spl))))


def spl_set_smt_constraint(spl, smt_constraint): spl.smt_constraint = smt_constraint

##


def spl_to_save_format(spl):
	return {
		'name': spl_get_name(spl),
		'group': spl_get_group_name(spl),
		'deprecated': spl_is_deprecated(spl),
		'version_full': spl_get_version_full(spl),
		'version': spl_get_version(spl),
		'slot': spl_get_slot(spl),
		'subslot': spl_get_subslot(spl),
		'fm_local': hyportage_constraint_ast.ast_require_to_save_format(spl_get_fm_local(spl)),
		'fm_combined': hyportage_constraint_ast.ast_depend_to_save_format(spl_get_fm_combined(spl)),
		'dependencies': dependencies_to_save_format(spl_get_dependencies(spl)),
		#
		'required_iuses_local': list(spl_get_required_iuses_local(spl)),
		'required_iuses': list(spl_get_required_iuses(spl)),
		#
		'keywords_list': list(spl_get_keywords_list(spl)),
		'keywords_default': spl_get_keywords_default(spl),
		'keywords_profile': spl_get_keywords_profile(spl),
		'keywords_user': spl_get_keywords_user(spl),
		#
		'iuses_default': list(spl_get_iuses_default(spl)),
		'iuses_profile': list(spl_get_iuses_profile(spl)),
		'iuses_user': list(spl_get_iuses_user(spl)),
		#
		'use_selection_default': use_selection_to_save_format(spl_get_use_selection_default(spl)),
		'use_selection_profile': use_selection_to_save_format(spl_get_use_selection_profile(spl)),
		'use_selection_user': use_selection_to_save_format(spl_get_use_selection_user(spl)),
		#
		'mask_profile': spl_get_mask_profile(spl),
		'mask_user': spl_get_mask_user(spl),
		#
		'smt_constraint': spl_get_smt_constraint(spl),
	}


def spl_from_save_format(save_format):
	res = SPL(
			save_format['name'], save_format['group'], save_format['deprecated'],
			save_format['version_full'], save_format['version'],
			save_format['slot'], save_format['subslot'],
			hyportage_constraint_ast.ast_require_from_save_format(save_format['fm_local']), hyportage_constraint_ast.ast_require_from_save_format(save_format['fm_combined']),
			dependencies_from_save_format(save_format['dependencies']), set(save_format['required_iuses_local']), set(save_format['keywords_list']),
			set(save_format['iuses_default']), use_selection_from_save_format(save_format['use_selection_default'])
		)
	spl_set_keywords_default(res, save_format['keywords_default'])
	spl_set_keywords_profile(res, save_format['keywords_profile'])
	spl_set_keywords_user(res, save_format['keywords_user'])

	spl_set_iuses_profile(res, save_format['iuses_profile'])
	spl_set_iuses_user(res, save_format['iuses_user'])

	spl_set_use_selection_profile(res, use_selection_from_save_format(save_format['use_selection_profile']))
	spl_set_use_selection_user(res, use_selection_from_save_format(save_format['use_selection_user']))

	spl_set_mask_profile(res, save_format['mask_profile'])
	spl_set_mask_user(res, save_format['mask_user'])

	res.required_use = set(save_format['required_iuses'])
	spl_set_smt_constraint(res, save_format['smt_constraint'])

	return res

##

mspl_create = core_data.dict_configuration_create


def mspl_add_spl(mspl, spl):
	mspl[spl_get_name(spl)] = spl

def mspl_remove_spl(mspl, spl):
	mspl.pop(spl_get_name(spl))

def mspl_update_spl(mspl, old_spl, new_spl):
	mspl[spl_get_name(old_spl)] = new_spl

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
	return [spl_to_save_format(value) for value in mspl.values()]


def mspl_from_save_format(save_format):
	mspl = {}
	spl_groups = {}
	for el in save_format:
		spl = spl_from_save_format(el)
		mspl[spl_get_name(spl)] = spl
		spl_groups_add_spl(spl_groups, spl)
	return mspl, spl_groups


######################################################################
# SPL GROUP MANIPULATION
######################################################################


class SPLGroup(object):
	def __init__(self, group_name, spl):
		self.name = group_name                            # name of the group
		self.references = [spl]                           # list of spls contained in this group
		self.slots_mapping = {spl_get_slots(spl): [spl]}  # mapping listings all spls stored in one slot
		self.smt_constraint = None                        # z3 constraint encoding this group

	def add_spl(self, spl):
		self.references.append(spl)
		slots = spl_get_slots(spl)
		if slots in self.slots_mapping:
			self.slots_mapping[slots].append(spl)
		else:
			self.slots_mapping[slots] = [spl]

	def replace_spl(self, old_spl, new_spl):
		self.add_spl(new_spl)
		self.remove_spl(old_spl)

	def remove_spl(self, spl):
		self.references.remove(spl)
		slots = spl_get_slots(spl)
		if len(self.slots_mapping[slots]) == 1:
			self.slots_mapping.pop(slots)
		else:
			self.slots_mapping[slots].remove(spl)


spl_groups_create = core_data.dict_configuration_create


def spl_groups_add_spl(spl_groups, spl):
	group_name, version_full, spl_name = (spl_get_group_name(spl), spl_get_version_full(spl), spl_get_name(spl))
	group = spl_groups.get(group_name)
	if group:
		group.add_spl(spl)
		return None
	else:
		group = SPLGroup(group_name, spl)
		spl_groups[group_name] = group
		return group


def spl_groups_replace_spl(spl_groups, old_spl, new_spl):
	group = spl_groups.get(spl_get_group_name(new_spl))
	group.replace_spl(old_spl, new_spl)


def spl_groups_remove_spl(spl_groups, spl):
	group_name = spl_get_group_name(spl)
	group = spl_groups.get(group_name)
	if group:
		if len(group['reference']) == 1:
			return spl_groups.pop(group_name)
		else:
			group.remove_spl(spl)
			return None


def spl_group_get_references(spl_group): return spl_group.references


def spl_group_get_name(spl_group): return spl_group.name


def spl_group_get_slot_mapping(spl_group): return spl_group.slots_mapping


def spl_group_set_smt_constraint(spl_group, smt_constraint): spl_group.smt_constraint = smt_constraint


def spl_group_get_smt_constraint(spl_group): return spl_group.smt_constraint

######################################################################
# FULL SPL DATA MANIPULATION
######################################################################

# hyportage data contains:
#  - pattern repository
#  - id repository
#  - mspl
#  - spl_groups
#  - current configuration


def hyportage_data_to_save_format(pattern_repository, id_repository, mspl, spl_groups, core_configuration, installed_spls):
	return {
		'pattern_repository': hyportage_pattern.pattern_repository_to_save_format(pattern_repository),
		'id_repository': hyportage_ids.id_repository_to_save_format(id_repository),
		'mspl': mspl_to_save_format(mspl),
		'spl_groups': { k: spl_group_get_smt_constraint(v) for k, v in spl_groups.iteritems()},
		'core_configuration': hyportage_configuration.core_configuration_to_save_format(core_configuration),
		'installed_spls': core_data.package_installed_to_save_format(installed_spls)
	}


def hyportage_data_from_save_format(save_format):
	mspl, spl_groups = mspl_from_save_format(save_format['mspl'])
	for spl_group_name, spl_group in spl_groups.iteritems():
		spl_group_set_smt_constraint(spl_group, save_format['spl_groups'][spl_group_name])
	return (
		hyportage_pattern.pattern_repository_from_save_format(save_format['pattern_repository'], mspl),
		hyportage_ids.id_repository_from_save_format(save_format['id_repository']),
		mspl,
		spl_groups,
		hyportage_configuration.core_configuration_from_save_format(save_format['core_configuration']),
		core_data.package_installed_from_save_format(save_format['installed_spls'])
	)
