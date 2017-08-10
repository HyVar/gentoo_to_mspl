######################################################################
### FUNCTIONS FOR MSPL TRANSLATION
### Assumes that the compact form have been already decompacted
######################################################################

import re
import logging
import z3


import hyportage_constraint_ast
import hyportage_data
import hyportage_ids
import hyportage_pattern


# function to encode SMT expression into SMTLIB
def toSMT2(f, status="unknown", name="benchmark", logic=""):
	v = (z3.Ast * 0)()
	return z3.Z3_benchmark_to_smtlib_string(f.ctx_ref(), name, logic, status, "", 0, v, f.as_ast()).replace(
		"\n", " ").replace("(check-sat)", "").replace("; benchmark (set-info :status unknown)", "").strip()


##############################################
# auxiliary functions
##############################################


def get_smt_spl_name(id_repository, spl_name):
	return z3.Bool("p" + (hyportage_ids.id_repository_get_id_from_spl_name(id_repository, spl_name)))


def get_hyvar_spl_name(id_repository, spl_name):
	return "feature[p" + (hyportage_ids.id_repository_get_id_from_spl_name(id_repository, spl_name)) + "]"


def get_smt_spl_names(id_repository, spl_names):
	return map(lambda spl_name: get_smt_spl_name(id_repository, spl_name), spl_names)


def get_smt_use(id_repository, spl_name, use_flag):
	return z3.Bool("u" + (hyportage_ids.id_repository_get_id_from_use_flag(id_repository, spl_name, use_flag)))


def get_smt_uses(id_repository, spl_name, use_flags):
	return map(lambda use_flag: get_smt_use(id_repository, spl_name, use_flag), use_flags)


def get_hyvar_use(id_repository, spl_name, use_flag):
	return "feature[u" + (hyportage_ids.id_repository_get_id_from_use_flag(id_repository, spl_name, use_flag)) + "]"


#def get_smt_context():
#    return z3.Int(utils.CONTEXT_VAR_NAME)


#def get_no_two_true_expressions(fs):
#	return z3.And([z3.Not(z3.And(fs[i], fs[j])) for i in range(len(fs)) for j in range(len(fs)) if i < j])


def get_int_from_boo_list(fs): return z3.Sum([z3.If(b, 1, 0) for b in fs])


def get_no_two_true_expressions(fs):
	return get_int_from_boo_list(fs) <= 1


def get_extactly_one_true_expressions(fs):
	return get_int_from_boo_list(fs) == 1


def decompact_selection_list(id_repository, local_spl_name, spl_name, selection_list):
	"""Expands the compact forms in uses dependencies"""
	res = []
	for selection in selection_list:
		use_flag = selection['use']
		if hyportage_ids.id_repository_exists_use_flag(id_repository, spl_name, use_flag):
			use_id = get_smt_use(id_repository, spl_name, use_flag)
			if "prefix" in selection:
				if selection['prefix'] == "-":
					res.append(z3.Not(use_id))
				else:  # selection['prefix'] == "!"
					local_use_id = get_smt_use(id_repository, local_spl_name, use_flag)
					if selection['suffix'] == "=":
						res.append(local_use_id == z3.Not(use_id))
					else:  # selection['suffix'] == "?"
						res.append(z3.Implies(z3.Not(local_use_id), use_id))
			elif "suffix" in selection:
				local_use_id = get_smt_use(id_repository, local_spl_name, use_flag)
				if selection['suffix'] == "=":
					res.append(local_use_id == use_id)
				else:  # selection['suffix'] == "?"
					res.append(z3.Implies(local_use_id, use_id))
			else:
				res.append(use_id)
	return res
	# I don't deal with default value in this first approximation


"""
def decompact_atom(ctx):

	def get_use(ctx, prefix=""): # replace the prefix of the context with a default one. What for?
		use = {"use": ctx["use"]}
		if prefix:
			use['prefix'] = prefix
		if "preference" in ctx:
			use["preference"] = ctx["preference"]
		return use

	def get_dcondition(ctx, use):
		new_ctx = {
			'type': "dcondition",
			'condition': get_use(use),
			'els': [{'type': "dsimple", 'atom': {x: ctx[x] for x in ctx if x != "selection"}}]}
		new_ctx['els'][0]['atom']['decompacted'] = ""
		return new_ctx

	# decompact the comapct atoms
	assert "selection" in ctx
	condELs = []
	normal_sels = []
	for i in ctx["selection"]:
		if "prefix" in i and i["prefix"] == "!":
			if "suffix" in i:
				if i["suffix"] == "?":
					# app - misc / foo[!bar?]    bar? (app - misc / foo) !bar? (app - misc / foo[-bar])
					first = get_dcondition(ctx, i)
					second = get_dcondition(ctx ,i)
					second["condition"]["not"] = ""
					second["els"][0]["atom"]["selection"] = [get_use(i, "-")]
					condELs.extend([first, second])
				elif i["suffix"] == "=":
					# app - misc / foo[!bar =]    bar? (app - misc / foo[-bar]) !bar? (app - misc / foo[bar])
					first = get_dcondition(ctx, i)
					second = get_dcondition(ctx, i)
					first["els"][0]["atom"]["selection"] = [get_use(i, "-")]
					second["els"][0]["atom"]["selection"] = [get_use(i)]
					second["condition"]["not"] = ""
					condELs.extend([first, second])
			else:
				raise Exception("Find prefix ! but not suffix ? or = for use " + i["use"])
		elif "suffix" in i:
			if i["suffix"] == "?":
				# app - misc / foo[bar?]    bar? (app - misc / foo[bar]) !bar? (app - misc / foo)
				first = get_dcondition(ctx,i)
				second = get_dcondition(ctx,i)
				first["els"][0]["atom"]["selection"] = [get_use(i)]
				second["condition"]["not"] = ""
				condELs.extend([first, second])
			elif i["suffix"] == "=":
				# app - misc / foo[bar =]    bar? (app - misc / foo[bar]) !bar? (app - misc / foo[-bar])
				first = get_dcondition(ctx,i)
				second = get_dcondition(ctx,i)
				first["els"][0]["atom"]["selection"] = [get_use(i)]
				second["els"][0]["atom"]["selection"] = [get_use(i, "-")]
				second["condition"]["not"] = ""
				condELs.extend([first, second])
		else:
			normal_sels.append(i)
	return condELs, normal_sels
"""


##############################################
# visitor to convert the AST into SMT formulas
##############################################

class ASTtoSMTVisitor(hyportage_constraint_ast.ASTVisitor):

	def __init__(self, pattern_repository, id_repository, spl_name):
		super(hyportage_constraint_ast.ASTVisitor, self).__init__()
		self.id_repository = id_repository
		self.spl_name = spl_name
		self.pattern_repository = pattern_repository

	# def CombineValue(self, value1, value2):
	#     return value1

	def visitRequired(self, ctx):
		return z3.And(map(self.visitRequiredEL, ctx))

	def visitRequiredSIMPLE(self, ctx):
		# assert ctx["use"] in self.id_repository["flag"][self.spl_name]
		res = get_smt_use(self.id_repository, self.spl_name, ctx["use"])
		if "not" in ctx:
			res = z3.Not(res)
		return res

	def visitRequiredCONDITION(self, ctx):
		formulas = self.visitRequired(ctx['els'])
		# assert (self.id_repository["flag"][self.spl_name][ctx['condition']['use']])  # flag must exists
		use = get_smt_use(self.id_repository, self.spl_name, ctx['condition']['use'])
		if 'not' in ctx['condition']:
			use = z3.Not(use)
		return z3.Implies(use, z3.And(formulas))

	def visitRequiredCHOICE(self, ctx):
		formulas = map(self.visitRequiredEL, ctx['els'])
		if ctx["choice"] == "||":  # or
			return z3.Or(formulas)
		elif ctx["choice"] == "??":  # one-max
			if len(formulas) > 2:
				return get_no_two_true_expressions(formulas)
			else:
				return z3.BoolVal(True)
		elif ctx["choice"] == "^^":  # xor
			if len(formulas) > 1:
				return get_extactly_one_true_expressions(formulas)
			elif len(formulas) == 1:
				return formulas[0]
			return z3.BoolVal(False)  # no formula to be satisfied

	def visitRequiredINNER(self, ctx):
		return z3.And(self.visitRequired(ctx['els']))

	def visitDepend(self, ctx):
		return z3.And(map(self.visitDependEL, ctx))

	def visitDependSIMPLE(self, ctx):
		def aux_visit_single_pkg_single_select(spl_name, sel):
			if hyportage_ids.id_repository_exists_use_flag(self.id_repository, spl_name, sel["use"]):
				# the package considered did not declared the use
				if "prefix" in sel and sel["prefix"] == "-":
					if "preference" in sel:
						if sel["preference"] == "+":
							return z3.BoolVal(False)
					# preference - or absent
					return get_smt_spl_name(self.id_repository, spl_name)
				else: # prefix + or absent
					if "preference" in sel:
						if sel["preference"] == "+":
							return get_smt_spl_name(self.id_repository, spl_name)
					# preference - or absent
					return z3.BoolVal(False)
			else:  # package declared the use
				if "prefix" in sel and sel["prefix"] == "-":
					return z3.And(
						get_smt_spl_name(self.id_repository, spl_name),
						z3.Not(get_smt_use(self.id_repository, spl_name, sel["use"])))
				else: # prefix + or absent
					return z3.And(
						get_smt_spl_name(self.id_repository, spl_name),
						get_smt_use(self.id_repository, spl_name, sel["use"]))

		def aux_visit_select(spl_names, sel):
			return z3.Or([aux_visit_single_pkg_single_select(x, sel) for x in spl_names])

		#print(str(ctx['atom']))
		spls = hyportage_pattern.pattern_repository_element_get_spls_visible(
			hyportage_pattern.pattern_repository_get(self.pattern_repository, ctx['atom']))
		spl_names = [hyportage_data.spl_get_name(spl) for spl in spls]
		if spl_names:
			# decompact compact forms
			if "selection" in ctx:
				formulas = [
					(get_smt_spl_name(self.id_repository, spl_name),
					decompact_selection_list(self.id_repository, self.spl_name, spl_name, ctx['selection']))
					for spl_name in spl_names ]
				formula = z3.Or([z3.And(formula + [spl_id]) for spl_id, formula in formulas])
			else:
				formula = z3.Or(get_smt_spl_names(self.id_repository, spl_names))
		else:
			formula = z3.BoolVal(False)

		if "not" in ctx:
			return z3.Not(formula)
		return formula

	def visitDependCONDITION(self, ctx):
		formulas = self.visitDepend(ctx['els'])
		# assert self.id_repository["flag"][self.spl_name][ctx['condition']['use']]  # flag must exists
		use = get_smt_use(self.id_repository, self.spl_name, ctx['condition']['use'])
		if 'not' in ctx['condition']:
			use = z3.Not(use)
		return z3.Implies(use, z3.And(formulas))

	def visitDependCHOICE(self, ctx):
		formulas = map(self.visitDependEL, ctx['els'])
		if ctx["choice"] == "||":  # or
			return z3.Or(formulas)
		elif ctx["choice"] == "??":  # one-max
			if len(formulas) > 2:
				return get_no_two_true_expressions(formulas)
			else:
				return z3.BoolVal(True)
		elif ctx["choice"] == "^^":  # xor
			if len(formulas) > 1:
				return get_extactly_one_true_expressions(formulas)
			elif len(formulas) == 1:
				return formulas[0]
			return z3.BoolVal(False) # no formula to be satisfied

	def visitDependINNER(self, ctx):
		return z3.And(self.visitDepend(ctx['els']))

	"""def visitAtom(self, ctx):

		def aux_visit_single_pkg_single_select(pkg, sel):
			if sel["use"] not in self.id_repository["flag"][pkg]:
				# the package considered did not declared the use
				if "prefix" in sel and sel["prefix"] == "-":
					if "preference" in sel:
						if sel["preference"] == "+":
							return z3.BoolVal(False)
					# preference - or absent
					return get_smt_spl_name(self.id_repository, pkg)
				else: # prefix + or absent
					if "preference" in sel:
						if sel["preference"] == "+":
							return get_smt_spl_name(self.id_repository, pkg)
					# preference - or absent
					return z3.BoolVal(False)
			else:  # package declared the use
				if "prefix" in sel and sel["prefix"] == "-":
					return z3.And(
						get_smt_spl_name(self.id_repository, pkg),
						z3.Not(get_smt_use(self.id_repository, pkg, sel["use"])))
				else: # prefix + or absent
					return z3.And(
						get_smt_spl_name(self.id_repository, pkg),
						get_smt_use(self.id_repository, pkg, sel["use"]))

		def aux_visit_select(pkgs, sel):
			return z3.Or([aux_visit_single_pkg_single_select(x, sel) for x in pkgs])

		template = ctx["package"]
		if 'version_op' in ctx:
			operator = ctx['version_op']
			if "times"in ctx:
				template += "*"
		else:
			operator = "="
			template += "*"

		slot = ""
		subslot = ""
		if "slots" in ctx:
			if "slot" in ctx["slots"]:
				slot = ctx["slots"]["slot"]
			if "subslot" in ctx["slots"]:
				subslot = ctx["slots"]["subslot"]

		pkgs = get_packages(self.mspl,template, operator, slot, subslot)

		if pkgs:
			# decompact compact forms
			if "selection" in ctx:
				if not "decompacted" in ctx: # decompact procedure has not been run yet
					condELs, normal_sels = decompact_atom(ctx)
				else:
					normal_sels = ctx["selection"]
					condELs = []
				formulas = [aux_visit_select(pkgs, x) for x in normal_sels]
				formulas.append(self.visitDepend(condELs))
				return z3.And(formulas)
			else:
				return z3.Or(get_smt_spl_names(self.id_repository, pkgs))
		else:
			return z3.BoolVal(False)"""


def simplify_constraints(name, constraints, simplify_mode):
	if simplify_mode == "default":
		formula = z3.simplify(z3.And(constraints))
		if z3.is_false(formula):
			logging.warning("Dependencies in package " + name + " make it uninstallable.")
		return (name,[toSMT2(formula)])
	elif simplify_mode == "individual":
		formulas = []
		for i in constraints:
			formula = z3.simplify(i)
			if z3.is_false(formula):
				logging.warning("Dependency " + unicode(i) + " in package " + name + " is false." +
								"Package can not be installed")
			formulas.append(formula)
		return (name,[toSMT2(x) for x in formulas])


def convert_spl(pattern_repository, id_repository, spl, simplify_mode):
	spl_name = hyportage_data.spl_get_name(spl)
	spl_id = get_smt_spl_name(id_repository, spl_name)
	logging.debug("Processing spl " + spl_name)
	constraints = []
	#print("processing (" + str(spl_name) + ", " + str(spl_id) + ")")
	# 1. convert feature model
	visitor = ASTtoSMTVisitor(pattern_repository, id_repository, spl_name)
	for constraint in map(visitor.visitRequiredEL, hyportage_data.spl_get_fm_local(spl)):
		constraints.append(z3.Implies(spl_id, constraint))
	for constraint in map(visitor.visitDependEL, hyportage_data.spl_get_fm_combined(spl)):
		# print "--------"
		# print mspl[package]["fm"]["combined"][counter]
		# counter += 1
		# print toSMT2(z3.Implies(get_smt_package(map_name_id, package),i))
		constraints.append(z3.Implies(spl_id, constraint))

	# 2. constraint stating that selecting an spl also selects its group
	spl_group_name = hyportage_data.spl_get_group_name(spl)
	constraints.append(z3.Implies(spl_id, get_smt_spl_name(id_repository, spl_group_name)))

	spl_uses_id = get_smt_uses(
		id_repository, spl_name, hyportage_ids.id_repository_get_use_flag_from_spl_name(id_repository, spl_name))

	# 3. if package is not selected then its flags are not selected either
	constraints.append(z3.Implies(z3.Not(spl_id), z3.And([z3.Not(use_id) for use_id in spl_uses_id])))

	# 4. if flag is selected then its package is selected too
	constraints.append(z3.Implies(z3.Or(spl_uses_id), spl_id))

	return spl_name, simplify_constraints(spl_name, constraints, simplify_mode)


def convert_spl_group(id_repository, spl_group, simplify_mode):
	spl_group_name = hyportage_data.spl_group_get_name(spl_group)
	spl_group_id = get_smt_spl_name(id_repository, spl_group_name)
	spls = filter(hyportage_data.spl_is_visible, hyportage_data.spl_group_get_references(spl_group))
	spls_id = get_smt_spl_names(id_repository, [hyportage_data.spl_get_name(spl) for spl in spls])

	logging.debug("Processing spl group " + spl_group_name)
	constraints = []

	# 1. if installed then one of its version should be installed as well
	constraints.append(z3.Implies(spl_group_id, z3.Or(spls_id)))

	# 2. two installed spl should have different slots or subslots
	for spls in hyportage_data.spl_group_get_slot_mapping(spl_group).values():
		spls = filter(hyportage_data.spl_is_visible, spls)
		if len(spls) > 1:
			spls_id = get_smt_spl_names(id_repository, [hyportage_data.spl_get_name(spl) for spl in spls])
			constraints.append(get_no_two_true_expressions(spls_id))

	return spl_group_name, simplify_constraints(spl_group_name, constraints, simplify_mode)




def generate_formulas(concurrent_map, mspl, map_name_id, simplify_mode):
	ls = [(mspl, map_name_id, simplify_mode, package) for package in mspl]
	return concurrent_map(convert, ls)