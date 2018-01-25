#!/usr/bin/python


import core_data

import hyportage_db
import smt_encoding
import hyportage_constraint_ast


"""
This file contains the classes for the two main hyportage data: SPL and SPL_Groups
"""


__author__ = "Michael Lienhardt & Jacopo Mauro"
__copyright__ = "Copyright 2017, Michael Lienhardt & Jacopo Mauro"
__license__ = "GPL3"
__version__ = "0.5"
__maintainer__ = "Michael Lienhardt & Jacopo Mauro"
__email__ = "michael.lienhardt@laposte.net & mauro.jacopo@gmail.com"
__status__ = "Prototype"


######################################################################
# SPL AND MPL MANIPULATION
######################################################################


class GETDependenciesVisitor(hyportage_constraint_ast.ASTVisitor):
	def __init__(self):
		super(hyportage_constraint_ast.ASTVisitor, self).__init__()
		self.local = set()
		self.dependencies = core_data.dictSet()
		self.pattern = None

	def visitRequiredSIMPLE(self, ctx): self.local.add(ctx['use'])

	def visitCondition(self, ctx): self.local.add(ctx['use'])

	def visitDependSIMPLE(self, ctx):
		#print("found dependency: " + ctx['atom'])
		self.pattern = ctx['atom']
		self.dependencies.add_key(self.pattern)
		if "selection" in ctx: map(self.visitSelection, ctx['selection'])

	def visitSelection(self, ctx):
		use = ctx['use']
		#print("  found use flag: " + use)
		self.dependencies.add(self.pattern, use)
		if 'suffix' in ctx: self.local.add(use)


class SPL(object):
	"""
	This class contains all the information related to a package/SPL.
	Moreover, it contains some method to construct important data, like the smt constraint for the use default selection
	"""
	def __init__(
			self, eapi, name, core, deprecated,
			iuses_default, use_manipulation_default,  fm_local, fm_combined,
			keyword_set, license):
		"""
		The constructor of the class
		:param eapi: the EAPI of the spl/package. This information is necessary to compute the full list of use flags of the package
		:param name: the full name of the package, including its category, version and revision if present
		:param core: the core data of the package, as defined in core_data.py. it's the split of the package name into relevant information for pattern matching
		:param deprecated: boolean stating if the package is deprecated (i.e., is installed but not part of the portage tree anymore)
		:param iuses_default: the use flags declared in the IUSE variable (without the implicit ones from the profile)
		:param use_manipulation_default: the use manipulation declared in the IUSE variable
		:param fm_local: the AST corresponding to the USE_REQUIRED variable
		:param fm_combined: the AST corresponding to the conjunction of the DEPEND, RDEPEND and PDEPEND variables
		:param keyword_set: the keywords of the package
		:param license: the licence of the package
		"""
		#######################
		# core data
		self.eapi                     = eapi
		self.name                     = name
		self.core                     = core
		self.is_deprecated               = deprecated
		#######################
		# feature model
		self.iuses_default            = iuses_default             # list of features declared in this spl by default
		self.use_manipulation_default = use_manipulation_default  # default use selection
		self.fm_local                 = fm_local                  # the part of the feature model related to local features, i.e., portage's REQUIRED_USE
		self.fm_combined              = fm_combined               # the part of the feature model relatd to external dependencies, i.e., portage's DEPEND + RDEPEND + PDEPEND
		##
		self.__dependencies            = None                     # mapping from pattern dependencies to list of features they must have declared
		self.__revert_dependencies     = core_data.dictSet()      # which patterns refer to this SPL, with which features
		self.__required_iuses_local    = None                     # list of local features mentioned in local constraints
		self.__required_iuses          = None                     #
		self.__iuses_full              = None                     # full use flag list
		self.__iuses_visible           = None                     # visible use flag list
		self.__iuses_core              = None                     # use flag that are relevant in the constraints
		self.__use_selection_full      = None                     # selected product of this SPL
		self.__use_selection_core      = None                     # selected product of this SPL, only considering the use flags relevant for the constraints
		#######################
		# SMT
		self.__smt_constraint          = None                     # translation of the full feature model into z3 constraints
		#######################
		# visibility
		self.keyword_set             = keyword_set                # list of architectures valid for this SPL
		self.license                 = license                    # the licence of this SPL
		##
		self.__unmasked                = None                     # if portage states that this spl is masked or not
		self.__unmasked_keyword        = None                     # if the keyword configuration of this package masks it
		self.__unmasked_license        = None                     # if the licence configuration of this package masks it
		self.__installable             = None                     # if this package is installable
		self.__is_stable               = None                     # if this package is stable
		#######################
		# graph traversal
		self.visited = False
		#######################
		# initial setup
		self.generate_dependencies_and_requirements()

	def __hash__(self): return hash(self.name)

	def __eq__(self, other):
		if isinstance(other, SPL):
			return self.name == other.name
		else:
			return False

	#####################################
	# GENERATORS AND PROPERTIES

	@property
	def group_name(self): return core_data.spl_core_get_spl_group_name(self.core)

	@property
	def slot(self): return core_data.spl_core_get_slot(self.core)

	@property
	def subslot(self): return core_data.spl_core_get_subslot(self.core)

	def generate_dependencies_and_requirements(self):
		visitor = GETDependenciesVisitor()
		visitor.visitRequired(self.fm_local)
		visitor.visitDepend(self.fm_combined)
		self.__dependencies = visitor.dependencies
		self.__required_iuses_local = visitor.local

	def generate_visibility_data(self):
		self.__unmasked_keyword, self.__unmasked_license, self.__installable, self.__is_stable =\
			hyportage_db.mspl_config.get_stability_status(self.core, self.unmasked, self.keyword_set, self.license)

	@property
	def dependencies(self):
		if self.__dependencies is None: self.generate_dependencies_and_requirements()
		return self.__dependencies

	@property
	def required_iuses_local(self):
		if self.__required_iuses_local is None: self.generate_dependencies_and_requirements()
		return self.__required_iuses_local

	@property
	def required_iuses_external(self):
		return {use for use_set in self.__revert_dependencies.itervalues() for use in use_set}

	@property
	def required_iuses(self):
		if self.__required_iuses is None:
			self.__required_iuses = self.required_iuses_local | self.required_iuses_external
		return self.__required_iuses

	@property
	def iuses_full(self):
		if self.__iuses_full is None:
			if self.eapi < 5:
				self.__iuses_full = self.iuses_default | hyportage_db.mspl_config.use_declaration_eapi4
			else:
				self.__iuses_full = self.iuses_default |  hyportage_db.mspl_config.use_declaration_eapi5
		return self.__iuses_full

	@property
	def iuses_visible(self):
		if self.__iuses_visible is None:
			self.__iuses_visible = self.iuses_full - hyportage_db.mspl_config.use_declaration_hidden_from_user
		return self.__iuses_visible

	@property
	def iuses_core(self):
		if self.__iuses_core is None: self.__iuses_core = self.required_iuses & self.iuses_full
		return self.__iuses_core

	@property
	def use_selection_full(self):
		if self.__use_selection_full is None:
			if hyportage_db.installed_packages.get(self.name) is not None:  # TODO: this if is not true with the --newuse option
				self.__use_selection_full = hyportage_db.installed_packages[self.name]
			else:
				self.__use_selection_full = hyportage_db.mspl_config.get_use_flags(
					self.core, self.unmasked, self.__is_stable, self.use_manipulation_default) & self.iuses_full
		return self.__use_selection_full

	@property
	def use_selection_core(self):
		if self.__use_selection_core is None:
			self.__use_selection_core = self.use_selection_full & self.iuses_core
		return self.__use_selection_core

	##

	@property
	def smt(self):
		if self.__smt_constraint is None:
			self.__smt_constraint = smt_encoding.convert_spl(
				hyportage_db.pattern_repository, hyportage_db.id_repository,
				hyportage_db.mspl, hyportage_db.spl_groups, self, hyportage_db.simplify_mode)
		return self.__smt_constraint

	@property
	def smt_false(self):
		return [smt_encoding.smt_to_string(smt_encoding.get_spl_smt_not(hyportage_db.id_repository, self.name))]

	@property
	def smt_use_selection(self):
		return smt_encoding.convert_use_flag_selection(
				hyportage_db.id_repository, self.name, self.iuses_core, self.use_selection_core)

	@property
	def smt_use_exploration(self):
		use_useful = self.iuses_core
		force, mask = hyportage_db.mspl_config.get_use_force_mask(self.core, self.__is_stable)
		force.intersection_update(use_useful)
		force.update(self.use_selection_core & hyportage_db.mspl_config.use_declaration_hidden_from_user)
		mask.intersection_update(use_useful)
		return smt_encoding.convert_use_flag_selection(hyportage_db.id_repository, self.name, force | mask, force)

	##

	@property
	def unmasked(self):
		if self.__unmasked is None:
			self.__unmasked = hyportage_db.mspl_config.get_unmasked(self.core)
		return self.__unmasked

	@property
	def unmasked_keyword(self):
		if self.__unmasked_keyword is None:
			self.generate_visibility_data()
		return self.__unmasked_keyword

	@property
	def unmasked_license(self):
		if self.__unmasked_license is None:
			self.generate_visibility_data()
		return self.__unmasked_license

	@property
	def installable(self):
		if self.__installable is None:
			self.generate_visibility_data()
		return self.__installable

	@property
	def is_stable(self):
		if self.__is_stable is None:
			self.generate_visibility_data()
		return self.__is_stable

	#####################################
	# DATA UPDATE METHODS

	def reset_required_iuses(self):
		self.__required_iuses = None
		self.reset_iuses_full()

	def reset_iuses_full(self):
		self.__iuses_full         = None
		self.__iuses_visible      = None
		self.__iuses_core         = None
		self.__use_selection_full = None
		self.__use_selection_core = None

	def reset_use_selection(self):
		self.__use_selection_full = None
		self.__use_selection_core = None

	def reset_smt(self):
		self.__smt_constraint = None

	def reset_unmasked_other(self):
		self.__unmasked_keyword = None
		self.__unmasked_license = None
		self.__installable = None
		self.__is_stable = None

	def reset_unmasked(self):
		self.__unmasked = None
		self.reset_unmasked_other()

	def update_revert_dependencies(self, pattern, uses):
		self.__revert_dependencies[pattern] = uses
		if (self.__required_iuses is not None) and (not uses.issubset(self.__required_iuses)):
			self.reset_required_iuses()
			return True
		return False

	def reset_revert_dependencies(self, pattern):
		self.__revert_dependencies.pop(pattern)
		# I don't reset the __required_iuses field, because it would cause too much computation (recomputing the list,
		#  the constraints and the constraints of the revert dependencies) for just having a possibly smaller list


##

MSPL = dict


def mspl_create(): return {}


def mspl_add_spl(mspl, spl):
	mspl[spl.name] = spl


def mspl_remove_spl(mspl, spl):
	mspl.pop(spl.name)


def mspl_update_spl(mspl, old_spl, new_spl):
	mspl[old_spl.name] = new_spl


######################################################################
# KEYWORDS MANIPULATION
######################################################################


def get_core_keyword(keyword):
	if (keyword[0] in ['-', '~']) and (keyword[1] != '*'): return keyword[1:]
	elif keyword[0] != '*': return keyword


def keywords_get_core_set(keywords):
	res = {get_core_keyword(keyword) for keyword in keywords}
	res.discard(None)
	return res


######################################################################
# SPL GROUP MANIPULATION
######################################################################


class SPLGroup(object):
	"""
	This class stores all the information related to an spl group,
	i.e., the "software" folder containing the .ebuild files for all the software's version.
	"""
	def __init__(self, name):
		"""
		The constructor of the class
		:param group_name: the name of the group
		:param spl: the first spl known to be part of this group
		"""
		self.name = name                            # name of the group
		self.spls = []                              # the spls of this group
		self.slots_mapping = core_data.dictSet()    # mapping listings all spls stored in one slot
		self.__smt_constraint = None                # z3 constraint encoding this group

	def __hash__(self): return hash(self.name)

	def __eq__(self, other):
		if isinstance(other, SPLGroup):
			return self.name == other.name
		else: return False

	def __iter__(self): return iter(self.spls)

	def add_spl(self, spl):
		"""
		adds an spl to this group
		:param spl: the added spl
		:return: None
		"""
		self.spls.append(spl)
		self.slots_mapping.add(spl.slot, spl)

	def remove_spl(self, spl):
		self.spls.remove(spl)
		self.slots_mapping.remove_with_key(spl.slot, spl)

	def replace_spl(self, old_spl, new_spl):
		self.add_spl(new_spl)
		self.remove_spl(old_spl)

	#####################################
	# GENERATORS AND PROPERTIES

	@property
	def smt(self):
		if self.__smt_constraint is None:
			self.__smt_constraint = smt_encoding.convert_spl_group(hyportage_db.id_repository, self, hyportage_db.simplify_mode)
		return self.__smt_constraint

	#####################################
	# DATA UPDATE METHODS

	def reset_smt(self):
		self.__smt_constraint = None


"""
Finally, the spl_groups structure lists all the spl groups in the hyportage structure,
and is a simple mapping from spl group names to the corresponding spl group.
"""

SPL_GROUPS = dict


def spl_groups_create(): return {}


def spl_groups_add_spl(spl_groups, spl):
	group = spl_groups.get(spl.group_name)
	if group:
		group.add_spl(spl)
		return None
	else:
		group = SPLGroup(spl.group_name)
		group.add_spl(spl)
		spl_groups[spl.group_name] = group
		return group


def spl_groups_replace_spl(spl_groups, old_spl, new_spl):
	group = spl_groups.get(new_spl.group_name)
	group.replace_spl(old_spl, new_spl)


def spl_groups_remove_spl(spl_groups, spl):
	group_name = spl.group_name
	group = spl_groups.get(group_name)
	if group:
		if len(group.references) == 1:
			return spl_groups.pop(group_name)
		else:
			group.remove_spl(spl)
			return None




