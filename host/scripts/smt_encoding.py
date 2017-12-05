#!/usr/bin/python


import logging
import itertools
import z3

import hyportage_constraint_ast


"""
This file contains the functions that computes the constraints for spls, spl_groups and use flag selection
"""


__author__ = "Michael Lienhardt & Jacopo Mauro"
__copyright__ = "Copyright 2017, Michael Lienhardt & Jacopo Mauro"
__license__ = "GPL3"
__version__ = "0.5"
__maintainer__ = "Michael Lienhardt & Jacopo Mauro"
__email__ = "michael.lienhardt@laposte.net & mauro.jacopo@gmail.com"
__status__ = "Prototype"


def cleanup():
	global smt_false, smt_true, smt_or, smt_and, smt_not, smt_implies
	smt_false = None
	smt_true  = None
	smt_or    = None
	smt_and   = None
	smt_not   = None
	smt_implies = None


######################################################################
# 1. SMT UTILITY FUNCTIONS
######################################################################


smt_false = z3.BoolVal(False)
smt_true  = z3.BoolVal(True)
smt_variable = z3.Bool

smt_or  = z3.Or
smt_and = z3.And
smt_not = z3.Not
smt_implies = z3.Implies


def get_int_from_bool_list(fs): return z3.Sum([z3.If(b, 1, 0) for b in fs])


def get_no_two_true_expressions_num(fs):
	return get_int_from_bool_list(fs) <= 1


def get_exactly_one_true_expressions_num(fs):
	return get_int_from_bool_list(fs) == 1


##

def get_no_two_true_expressions_bool_core(fs):
	constraints = []
	for f1, f2 in itertools.combinations(fs, 2):
		constraints.append(smt_not(smt_and([f1, f2])))
	return constraints


def get_no_two_true_expressions_bool(fs):
	return smt_and(get_no_two_true_expressions_bool_core(fs))


def get_exactly_one_true_expressions_bool(fs):
	constraints = get_no_two_true_expressions_bool_core(fs)
	constraints.append(smt_or(fs))
	return smt_and(constraints)


##

smt_no_two_true_expressions = get_no_two_true_expressions_bool
smt_exactly_one_true_expressions = get_exactly_one_true_expressions_bool

##

def smt_to_string(constraint, status="unknown", name="benchmark", logic=""):
	v = (z3.Ast * 0)()
	return z3.Z3_benchmark_to_smtlib_string(
		constraint.ctx_ref(), name, logic, status, "", 0, v, constraint.as_ast()).replace(
		"\n", " ").replace("(check-sat)", "").replace("; benchmark (set-info :status unknown)", "").strip()


def smt_list_to_strings(constraints, status="unknown", name="benchmark", logic=""):
	return map(lambda c: smt_to_string(c, status, name, logic), constraints)


######################################################################
# 2. SMT VARIABLE MANIPULATION
######################################################################

def get_spl_smt(id_repository, spl_name):
	"""returns the variable corresponding to the spl name in input"""
	return smt_variable(id_repository.get_id_from_spl_name(spl_name))


def get_spl_smt_not(id_repository, spl_name):
	"""returns the constraint forbidding to install the spl in input"""
	return smt_not(get_spl_smt(id_repository, spl_name))


def get_spl_smt_list(id_repository, spl_names):
	return map(lambda spl_name: get_spl_smt(id_repository, spl_name), spl_names)

##


def get_use_smt(id_repository, spl_name, use_flag):
	"""returns the variable corresponding to the use flag name in input"""
	return smt_variable(id_repository.get_id_from_use_flag(spl_name, use_flag))


def get_use_smt_not(id_repository, spl_name, use_flag):
	"""returns the constraint forbidding to select the use flag in input"""
	return smt_not(get_use_smt(id_repository, spl_name, use_flag))


def get_use_smt_list(id_repository, spl_name, use_flags):
	return map(lambda use_flag: get_use_smt(id_repository, spl_name, use_flag), use_flags)


##

def get_spl_hyvarrec(id_repository, spl_name):
	return "feature[" + id_repository.get_id_from_spl_name(spl_name) + "]"


def get_use_hyvarrec(id_repository, spl_name, use_flag):
	return "feature[" + id_repository.get_id_from_use_flag(spl_name, use_flag) + "]"


######################################################################
# 3. CONSTRAINT TRANSLATION
######################################################################


def decompact_selection_list(id_repository, local_spl_name, spl_name, selection_list):
	"""
	generate the constraint corresponding to local_spl_name depending to spl_name,
	possibly with a use flag selection specified
	:param id_repository is the id repository used for translating names into the corresponding variables
	:param local_spl_name is the spl containing the constraint
	:param spl_name is the spl for which the use flag selection is specified
	:param selection_list is the use flag selection specified for the spl_name
	:returns the constraint corresponding to the specified dependency
	"""
	res = [get_spl_smt(id_repository, spl_name)]
	for selection in selection_list:
		use_flag = selection['use']
		if id_repository.exists_use_flag(spl_name, use_flag):
			use_smt = get_use_smt(id_repository, spl_name, use_flag)
			if "prefix" in selection:  # two cases: "-" (not selected), or "!" (compact form)
				if selection['prefix'] == "-":
					res.append(smt_not(use_smt))
				else:  # selection['prefix'] == "!"
					local_use_smt = get_use_smt(id_repository, local_spl_name, use_flag)
					if selection['suffix'] == "=":
						res.append(local_use_smt == smt_not(use_smt))
					else:  # selection['suffix'] == "?"
						res.append(smt_implies(smt_not(local_use_smt), use_smt))
			elif "suffix" in selection:
				local_use_smt = get_use_smt(id_repository, local_spl_name, use_flag)
				if selection['suffix'] == "=":
					res.append(local_use_smt == use_smt)
				else:  # selection['suffix'] == "?"
					res.append(smt_implies(local_use_smt, use_smt))
			else:
				res.append(use_smt)
		elif "default" in selection:
			prefix = "prefix" in selection
			default = selection['default']
			if "suffix" in selection:
				local_use_smt = get_use_smt(id_repository, local_spl_name, use_flag)
				suffix = selection['suffix']
				if (((suffix == "?") and (not prefix) and (default == "-"))
						or ((suffix == "=") and (((not prefix) and (default == "-")) or (prefix and (default == "+"))))):
					res.append(smt_not(local_use_smt))
				if (((suffix == "?") and prefix and (default == "+"))
						or ((suffix == "=") and (((not prefix) and (default == "+")) or (prefix and (default == "-"))))):
					res.append(local_use_smt)
			else:
				if (default == "+" and "prefix" in selection) or (default == "-" and "prefix" not in selection):
					return [smt_false]  # FALSE, this spl cannot be installed
		else:
			return [smt_false]  # FALSE, this spl cannot be installed
	return res


##############################################
# visitor to convert the AST into SMT formulas
##############################################

class ASTtoSMTVisitor(hyportage_constraint_ast.ASTVisitor):
	"""
	This class implements a translator from the fm_local and fm_combined AST to SMT constraints
	"""

	def __init__(self, pattern_repository, id_repository, mspl, spl_groups, spl_name):
		"""
		The constructor of this class
		:param pattern_repository: the pattern_repository of hyportage
		:param id_repository: the id_repository of hyportage
		:param mspl: the mspl of hyportage
		:param spl_groups: the spl_groups of hyportage
		:param spl_name: the name of the spl whose constraints will be translated
		"""
		super(hyportage_constraint_ast.ASTVisitor, self).__init__()
		self.id_repository = id_repository
		self.pattern_repository = pattern_repository
		self.mspl = mspl
		self.spl_groups = spl_groups
		self.spl_name = spl_name

	def visitRequired(self, ctx):
		return map(self.visitRequiredEL, ctx)

	def visitRequiredSIMPLE(self, ctx):
		use_smt = get_use_smt(self.id_repository, self.spl_name, ctx["use"])
		if "not" in ctx: use_smt = smt_not(use_smt)
		return use_smt

	def visitRequiredCONDITION(self, ctx):
		formulas = self.visitRequired(ctx['els'])
		# assert (self.id_repository["flag"][self.spl_name][ctx['condition']['use']])  # flag must exists
		use_smt = get_use_smt(self.id_repository, self.spl_name, ctx['condition']['use'])
		if 'not' in ctx['condition']: use_smt = smt_not(use_smt)
		return smt_implies(use_smt, smt_and(formulas))

	def visitRequiredCHOICE(self, ctx):
		formulas = map(self.visitRequiredEL, ctx['els'])
		if ctx["choice"] == "||":  # or
			return smt_or(formulas)
		elif ctx["choice"] == "??":  # one-max
			if len(formulas) > 1:
				return smt_no_two_true_expressions(formulas)
			else:
				return smt_true
		elif ctx["choice"] == "^^":  # xor
			if len(formulas) > 1:
				return smt_exactly_one_true_expressions(formulas)
			elif len(formulas) == 1:
				return formulas[0]
			return smt_false  # no formula to be satisfied

	def visitRequiredINNER(self, ctx):
		return smt_and(self.visitRequired(ctx['els']))

	def visitDepend(self, ctx):
		return map(self.visitDependEL, ctx)

	def visitDependSIMPLE(self, ctx):
		spls = self.pattern_repository[ctx['atom']].matched_spls
		spl_name_list = [spl.name for spl in spls]
		if spl_name_list:
			# decompact compact forms
			if "selection" in ctx:
				formulas = [
					decompact_selection_list(self.id_repository, self.spl_name, external_spl_name, ctx['selection'])
					for external_spl_name in spl_name_list]
				formula = smt_or([smt_and(formula) for formula in formulas])
			else:
				formula = smt_or(get_spl_smt_list(self.id_repository, spl_name_list))
		else:
			formula = smt_false

		if "not" in ctx:
			return smt_not(formula)
		return formula

	def visitDependCONDITION(self, ctx):
		formulas = self.visitDepend(ctx['els'])
		use_smt = get_use_smt(self.id_repository, self.spl_name, ctx['condition']['use'])
		if 'not' in ctx['condition']:
			use_smt = smt_not(use_smt)
		return smt_implies(use_smt, smt_and(formulas))

	def visitDependCHOICE(self, ctx):
		formulas = map(self.visitDependEL, ctx['els'])
		if ctx["choice"] == "||":  # or
			return smt_or(formulas)
		elif ctx["choice"] == "??":  # one-max
			if len(formulas) > 1:
				return smt_no_two_true_expressions(formulas)
			else:
				return smt_true
		elif ctx["choice"] == "^^":  # xor
			if len(formulas) > 1:
				return smt_exactly_one_true_expressions(formulas)
			elif len(formulas) == 1:
				return formulas[0]
			return smt_false # no formula to be satisfied

	def visitDependINNER(self, ctx):
		return smt_and(self.visitDepend(ctx['els']))


######################################################################
# 4. SMT CONSTRAINT GENERATION FOR SPLs, SPL GROUPs, USE FLAG LIST AND PATTERN LIST
######################################################################


def simplify_constraints(spl_name, constraints, simplify_mode):
	"""
	This function simplifies the SMT constraint in input following the simplify_mode
	:param spl_name: the name of the spl from which the constraint has been extracted
	:param constraints: the extracted constraint (actually, a list of constraints)
	:param simplify_mode: mode of simplification.
		"default" means that
	:return:
	"""
	if simplify_mode == "default":
		formula = z3.simplify(smt_and(constraints))
		if z3.is_false(formula):
			logging.warning("Dependencies in package " + spl_name + " make it uninstallable.")
		return [formula]
	elif simplify_mode == "individual":
		formulas = []
		for c in constraints:
			formula = z3.simplify(c)
			if z3.is_false(formula):
				logging.warning("Dependencies in package " + spl_name + " make it uninstallable.")
				return [smt_false]
			formulas.append(formula)
		return formulas


def convert_spl(pattern_repository, id_repository, mspl, spl_groups, spl, simplify_mode):
	spl_name = spl.name
	spl_smt = get_spl_smt(id_repository, spl_name)
	#logging.debug("Processing spl " + spl_name)
	constraints = []
	# print("processing (" + str(spl_name) + ", " + str(spl_id) + ")")
	# 1. convert feature model
	visitor = ASTtoSMTVisitor(pattern_repository, id_repository, mspl, spl_groups, spl_name)
	constraints.extend(visitor.visitRequired(spl.fm_local))
	constraints.extend(visitor.visitDepend(spl.fm_combined))
	#for constraint in visitor.visitDepend(spl.fm_combined):
	#	constraints.append(smt_implies(spl_smt, constraint))

	return smt_list_to_strings(
		map(lambda c: smt_implies(spl_smt, c), simplify_constraints(spl_name, constraints, simplify_mode)))


def convert_spl_group(id_repository, spl_group, simplify_mode):
	spl_group_name = spl_group.name
	#logging.debug("Processing spl group " + spl_group_name)
	constraints = []

	# two installed spl should have different slots or subslots
	for spls in spl_group.slots_mapping.itervalues():
		if len(spls) > 1:
			spl_smt_list = get_spl_smt_list(id_repository, [spl.name for spl in spls])
			constraints.append(smt_no_two_true_expressions(spl_smt_list))

	return smt_list_to_strings(simplify_constraints(spl_group_name, constraints, simplify_mode))


def convert_use_flag_selection(id_repository, spl_name, use_flags, use_selection):
	use_unselection = use_flags - use_selection
	constraint = [get_use_smt(id_repository, spl_name, use) for use in use_selection]
	constraint.extend([get_use_smt_not(id_repository, spl_name, use) for use in use_unselection])
	return smt_list_to_strings(constraint)


def convert_patterns(pattern_repository, id_repository, patterns):
	spls = set()
	constraints = []
	for pattern in patterns:
		new_spls = pattern_repository.get_with_default(pattern).matched_spls
		spls.update(new_spls)
		#print(core_data.pattern_to_atom(pattern) + " => " + str([spl.name for spl in new_spls]))
		constraints.append(smt_or([get_spl_smt(id_repository, spl.name) for spl in new_spls]))
	return spls, smt_list_to_strings(constraints)


def convert_installed_spls(id_repository, domain_spls, installed_spls):
	uninstalled_spls = [spl.name for spl in domain_spls if spl.name not in installed_spls]
	constraint = [get_spl_smt(id_repository, spl_name) for spl_name in installed_spls]
	constraint.extend([get_spl_smt_not(id_repository, spl_name) for spl_name in uninstalled_spls])
	return smt_list_to_strings(constraint)