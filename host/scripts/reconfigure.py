import json
import sys
import utils
import logging
import os
import subprocess
import smt_encoding
import pysmt.shortcuts
import re

import core_data

import hyportage_data
import hyportage_ids
import hyportage_pattern

from pysmt.smtlib.parser import SmtLib20Parser
import cStringIO

__author__ = "Michael Lienhardt and Jacopo Mauro"
__copyright__ = "Copyright 2017, Michael Lienhardt and Jacopo Mauro"
__license__ = "ISC"
__version__ = "0.1"
__maintainer__ = "Michael Lienhardt and Jacopo Mauro"
__email__ = "michael lienhardt@laposte.net & mauro.jacopo@gmail.com"
__status__ = "Prototype"


##########################################################################
# 1. INITIALIZE THE DATA (COMPUTE REQUEST AND UPDATE THE DATABASE)
##########################################################################

def process_request(pattern_repository, id_repository, mspl, spl_groups, config, atoms):
	"""
	This function simply takes the user request and his USE configuration from the environment,
	and translate them in relevant data
	:param pattern_repository: the pattern repository of hyportage
	:param id_repository: the id repository of hyportage
	:param mspl: the mspl of hyportage
	:param spl_groups: the spl_groups of hyportage
	:param config: the config object
	:param atoms: the user request
	:return: the list of spls involved in the request (extended with the ones in the config),
		with the corresponding SMT constraint.
		Additionally, the pattern repository is extended with the new patterns,
		and the config object have been updated with th USE user configuration
	"""
	requested_patterns = set([hyportage_pattern.pattern_create_from_atom(atom) for atom in atoms])
	requested_patterns.update(config.pattern_required_flat)
	for pattern in requested_patterns:
		hyportage_pattern.pattern_repository_add_pattern_from_scratch(pattern_repository, pattern)

	config.set_use_manipulation_env(os.environ.get("USE", "").split())

	root_spls, constraint = smt_encoding.convert_patterns(
		pattern_repository, id_repository, mspl, spl_groups, requested_patterns)
	return root_spls, constraint


##########################################################################
# 2. SOLVER WRAPPER
##########################################################################


def get_preferences_core(id_repository, mspl, installed_spls, spls):
	"""
	the priority of preferences is decided as follows:
		- remove less packages installed as possible,
		- minimize number of new packages to install
	"""
	installed_spls = set(installed_spls.keys()) & spls
	# preference for removing less packages installed and not deprecated as possible
	pref_less_remove = " + ".join([
		smt_encoding.get_smt_int_spl_name(id_repository, spl_name)
		for spl_name in installed_spls
		if not hyportage_data.spl_is_deprecated(mspl[spl_name])])
	# preference to minimize number of new packages to install
	pref_less_add = " + ".join([
		smt_encoding.get_smt_int_spl_name(id_repository, hyportage_data.spl_get_name(spl))
		for spl in spls if spl not in installed_spls])
	if not pref_less_remove: pref_less_remove = "0"
	return pref_less_remove + (" - (" + pref_less_add + ")" if pref_less_add else "")


def get_better_constraint_visualization(id_repository, mspl, constraints):
	"""
	function that manipulates the constraints in a more readable form for analysing them.
	Useful for debugging or error reporting
	:param id_repository: the id repository of hyportage
	:param mspl: the mspl of hyportage
	:param constraints: the constraints to manipulate
	:return: the manipulated constraints
	"""
	ls = []
	parser = SmtLib20Parser()
	for i in constraints:
		f = cStringIO.StringIO(i)
		script = parser.get_script(f)
		f.close()
		formula = script.get_last_formula()
		formula = pysmt.shortcuts.to_smtlib(formula, daggify=False)
		# # translate contexts
		# nums = re.findall('\(=\s*' + utils.CONTEXT_VAR_NAME + '\s*([0-9]+)\)',formula)
		# for i in nums:
		#     num = int(i)
		#     env = [ x for x in map_name_id['context_int'] if map_name_id['context_int'][x] == num]
		#     assert len(env) == 1
		#     formula = re.sub('\(=\s*' + utils.CONTEXT_VAR_NAME + '\s' + i + '\)', 'env(' + env[0] + ')',formula)
		# translate packages
		where_declared = "user-required: "
		pkgs = set(re.findall('p([0-9]+)', formula))
		for pkg in pkgs:
			name = id_repository.ids[pkg][1]
			formula = re.sub('p' + pkg,name,formula)
			if i in hyportage_data.spl_get_smt_constraint(mspl[name]):
				where_declared = name + ": "

		# translate uses
		uses = set(re.findall('u([0-9]+)', formula))
		for use in uses:
			formula = re.sub('u' + use, id_repository.ids[pkg][2] + "[[" + id_repository.ids[pkg][1] + "]]", formula)
		ls.append(where_declared + formula)
	return ls


def generate_to_install_spls(id_repository, feature_list):
	"""
	translate the output of the solver into a system to install (mapping from spl names to use flag selection)
	:param id_repository: the id repository  of hyportage
	:param mspl: the mspl of hyportage
	:param feature_list: the solution found by the solver
	:return: a dictionary spl_name -> use flag selection
	"""
	spl_names = set()
	use_flags = []
	for feature in feature_list:
		el = hyportage_ids.id_repository_get_ids(id_repository)[smt_encoding.get_id_from_smt_variable(feature)]
		if el[0] == "package":  # el = ("package", spl_name)
			spl_names.add(el[1])
		else:  # el = ("use", use, spl_name)
			use_flags.append((el[1], el[2]))

	res = core_data.dictSet()
	for spl_name, use_flag in use_flags:
		if spl_name in spl_names:
			res.add(spl_name, use_flag)
	return res


def solve_spls(
		id_repository, config, mspl, spl_groups, installed_spls,
		spls, annex_constraint, fixed_use_flags=True, par=1, explain_modality=False):
	"""
	Solves the spls in input locally assuming that there is a command hyvar-rec
	:param id_repository: the id repository of hyportage
	:param config: the config of hyportage
	:param mspl: the mspl of hyportage
	:param spl_groups: the spl groups of hyportage
	:param installed_spls: the mapping stating the use flag selection for all installed spls
	:param spls: the spls to solve
	:param annex_constraint: the additional constraint to add in the solver input
	:param fixed_use_flags: boolean saying if the solver can change the use flag default selection
	:param par: the number of threads to use for resolution (by default: 1)
	:param explain_modality: boolean saying if a problem should be explained (by default: False)
	:return: the solution found by the solver, if it exists
	"""
	# 1. construct the input data for the solver
	constraint = annex_constraint[:]
	spl_group_names = core_data.dictSet()
	for spl in spls:
		spl_group_names.add(core_data.spl_core_get_spl_group_name(spl.core), spl)
		constraint.extend(spl.smt(id_repository))
		if spl.installable and fixed_use_flags:
			if spl in installed_spls:
				constraint.extend(smt_encoding.convert_use_flag_selection(
					id_repository, spl.name, spl.required_iuses, installed_spls[spl]))
			else:
				constraint.extend(spl.smt_use_selection(id_repository, config))
	for spl_group_name, spls_tmp in spl_group_names.iteritems():
		spl_group = spl_groups[spl_group_name]
		constraint.extend(spl_group.smt_constraint)
		for spl in spl_group.references:
			if spl not in spls_tmp: constraint.append(smt_encoding.smt_to_string(smt_encoding.get_smt_not_spl_name(id_repository, spl.name)))
	logging.debug("number of constraints to solve: " + str(len(constraint)))
	preferences = get_preferences_core(id_repository, mspl, installed_spls, spls)
	data_configuration = {"selectedFeatures": [], "attribute_values": [], "context_values": []} # current configuration
	data_smt_constraints = {"formulas": constraint, "features": [], "other_int_symbols": []}
	data = {
		"attributes": [],  # attributes of the features (empty in our case)
		"contexts": [],  # contexts to consider (empty in our case)
		"configuration": data_configuration,
		"constraints": [], # constraints to fill in hyvarrec format (empty in our case for efficiency)
		"preferences": preferences, # preferences in hyvarrec format
		"smt_constraints": data_smt_constraints
	}

	# 2. generate the input file for the solver and the command line
	file_name = utils.get_new_temp_file(".json")
	with open(file_name, "w") as f:
		json.dump(data, f)
	cmd = ["hyvar-rec", "--features-as-boolean"]
	if par > 1:    cmd += ["-p", unicode(par)]
	if explain_modality: cmd.append("--explain")
	cmd.append(file_name)

	# 3. executing the solver
	utils.phase_start("Running " + unicode(cmd))
	process = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
	out, err = process.communicate()
	logging.debug('Stderr of ' + unicode(cmd))
	logging.debug(err)
	logging.debug('Return code of ' + unicode(cmd) + ': ' + str(process.returncode))
	utils.phase_end("Execution ended")

	sys.stdout.flush()
	sys.exit(0)

	# 4. managing the solver output
	res = json.loads(out)
	if res["result"] != "sat":
		if explain_modality:
			# todo handle explain modality when the answer is unsat
			# try to print a better explanation of the constraints
			constraints = get_better_constraint_visualization(res["constraints"], mspl, id_repository)
			sys.stderr.write("Conflict detected. Explanation:\n" + "\n".join(constraints) + '\n')
		logging.error("Conflict detected. Impossible to satisfy the request. Exiting.")
		sys.exit(1)
	logging.debug("HyVarRec output: " + unicode(res))

	return generate_to_install_spls(id_repository, res['features'])


def generate_emerge_script_file(mspl, path_install_script, installed_spls, to_install_spls):
	"""
	This function generates the script file to execute to install and uninstall the spls found by the solver
	:param mspl: the mspl of hyportage
	:param path_install_script: path to the script file to generate
	:param installed_spls: the currently installed spls
	:param to_install_spls: the spls to install, found by the solver
	:return: None (but the script file has been generated)
	"""
	installed_spl_names = installed_spls.keys()
	to_install_spl_names = to_install_spls.keys()

	installed_spl_groups_dict = core_data.dictSet()
	for spl_name in installed_spl_names:
		installed_spl_groups_dict.add(core_data.spl_core_get_spl_group_name(mspl[spl_name].core), spl_name)
	to_install_spl_groups_dict = core_data.dictSet()
	for spl_name in to_install_spl_names:
		to_install_spl_groups_dict.add(core_data.spl_core_get_spl_group_name(mspl[spl_name].core), spl_name)

	installed_spl_groups = set(installed_spl_groups_dict.keys())
	to_install_spl_groups = set(to_install_spl_groups_dict.keys())
	removed_spl_groups = installed_spl_groups - to_install_spl_groups


	added_spl_names = to_install_spl_names - set(installed_spl_names)
	removed_spl_names = [
		spl_name for spl_group_name in removed_spl_groups for spl_name in installed_spl_groups_dict[spl_group_name]]

	with open(path_install_script, 'w') as f:
		f.write("#!/bin/bash\n")
		f.write()
		f.write("# File auto-generated by the hyportage tool")
		f.write("# Do not update, any modification on this file will will overwritten by the tool")
		f.write()
		if added_spl_names:
			f.write("emerge -a --newuse -u" + " ".join(["=" + spl_name for spl_name in added_spl_names]) + "\n")
		if removed_spl_names:
			f.write("emerge --unmerge " + " ".join(["=" + spl_name for spl_name in removed_spl_names]) + "\n")


def generate_package_use_file(mspl, path_use_flag_configuration, to_install_spls):
	"""
	This function generates the spl configuration file (usually package.use) from the solution found by the solver
	:param mspl: the mspl of hyportage
	:param path_use_flag_configuration: path to the configuration file to generate
	:param to_install_spls: the new system generated by the solver
	:return: None (but the configuration file has been generated)
	"""
	with open(path_use_flag_configuration, 'w') as f:
		f.write("# File auto-generated by the hyportage tool")
		f.write("# Do not update, any modification on this file will will overwritten by the tool")
		f.write()
		for spl_name, use_selection in to_install_spls.iteritems():
			string = "=" + spl_name + " "
			string = string + " ".join(use_selection)
			string = string + " -".join(mspl[spl_name].required_iuses - use_selection)
			f.write(string)
		f.write()


##########################################################################
# 3. SPL SET COMPUTATION
##########################################################################


def next_spls(pattern_repository, mspl, spl_groups, spl):
	res = set()
	for pattern in hyportage_data.spl_get_dependencies(spl):
		res.update(
			hyportage_pattern.pattern_repository_get(pattern_repository, pattern).get_spls(mspl, spl_groups))
	return res


def get_dependency_transitive_closure(pattern_repository, mspl, spl_groups, spls):
	for spl in mspl.itervalues():
		spl.visited = False
	nexts = spls
	res = set()
	while len(nexts) > 0:
		accu = set()
		for spl in nexts:
			spl.visited = True
			res.add(spl)
			accu.update(next_spls(pattern_repository, mspl, spl_groups, spl))
		nexts = filter(lambda spl: not spl.visited, accu)

	return res





