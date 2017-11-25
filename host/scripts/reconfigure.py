#!/usr/bin/python
import json
import utils
import logging
import os
import subprocess
import smt_encoding
import pysmt.shortcuts
import re
import requests

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
# UTILITIES TO CALL THE HYVAR-REC SOLVER
##########################################################################


def run_hyvar(json_data, explain_modality, par_cores):
	"""
	Run hyvar locally assuming that there is a command hyvar-rec
	"""
	file_name = utils.get_new_temp_file(".json")
	with open(file_name, "w") as f:
		json.dump(json_data, f)
	cmd = ["hyvar-rec", "--constraints-minimization", "--features-as-boolean"]
	if explain_modality: cmd.append("--explain")
	if par_cores > 1: cmd.extend(["-p", unicode(par_cores)])
	cmd.append(file_name)

	# executing the solver
	utils.phase_start("Running: " + unicode(cmd))
	process = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
	out, err = process.communicate()
	if process.returncode != 0:
		logging.error("command ended with an error code: " + str(process.returncode))
		return None
	logging.debug("Stderr of the command")
	logging.debug(err)
	utils.phase_end("Execution ended")
	res = json.loads(out)
	return res


def run_remote_hyvar(json_data, explain_modality, url):
	"""
	Run hyvar
	"""
	if explain_modality: url += "/explain"
	else: url += "/process"
	utils.phase_start("Invoking url: " + url)
	response = requests.post(url, data=json.dumps(json_data), headers={'content-type': 'application/json'})
	utils.phase_end("Execution ended")
	if response.status_code != requests.codes.ok:
		logging.error("server answered with an error code: " + str(response.status_code))
		return None
	return response.json()


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


def get_preferences_core(id_repository, mspl, installed_spls, spl_names):
	"""
	the priority of preferences is decided as follows:
		- remove less packages installed as possible,
		- minimize number of new packages to install
	:param id_repository: the repository of hyportage
	:param mspl: the mspl of hyportage
	:param installed_spls: the currently installed spls with their configuration
	:param spl_names: the names of the spls considered in the reconfiguration process
	:return: an equation encoding the preference as described previously
	"""
	installed_spls = set(installed_spls.keys()) & spl_names
	# preference for removing less packages installed and not deprecated as possible
	pref_less_remove = " + ".join([
		smt_encoding.get_smt_variable_full_spl_name(id_repository, spl_name)
		for spl_name in installed_spls
		if not hyportage_data.spl_is_deprecated(mspl[spl_name])])
	# preference to minimize number of new packages to install
	pref_less_add = " + ".join([
		smt_encoding.get_smt_variable_full_spl_name(id_repository, spl_name)
		for spl_name in spl_names if spl_name not in installed_spls])
	if not pref_less_remove: pref_less_remove = "0"
	return pref_less_remove + (" - (" + pref_less_add + ")" if pref_less_add else "")


def get_preferences_use_flags(id_repository, mspl, spl_names):
	"""
	This function translates the use flag default selection of the spl in parameter into a preferences
	TODO: implement this function. It requires an API change in the SPL class to do it efficiently.
	:param id_repository: the id repository of hyportage
	:param mspl: the mspl of hyportage
	:param spl_names: the names of the spls to include in the preferences construction
	:return: an equation encoding the default configuration of the spls in parameter
	"""
	use_flags_positive = set()
	use_flag_negative = set()
	return 0


def installed_spls_to_solver(id_repository, installed_spls, spl_names):
	res = []
	for spl_name, use_selection in installed_spls.iteritems():
		if spl_name in spl_names:
			res.append(smt_encoding.get_smt_variable_full_spl_name(id_repository, spl_name))
	return res

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
		spl_ids = set(re.findall('p([0-9]+)', formula))
		for spl_id in spl_ids:
			name = id_repository.ids[spl_id][1]
			formula = re.sub('p' + spl_id, name, formula)
			if i in hyportage_data.spl_get_smt_constraint(mspl[name]):
				where_declared = name + ": "

		# translate uses
		use_ids = set(re.findall('u([0-9]+)', formula))
		for use_id in use_ids:
			formula = re.sub('u' + use_id, id_repository.ids[use_id][2] + "#" + id_repository.ids[use_id][1], formula)
		ls.append(where_declared + formula)
	return ls


def generate_to_install_spls(id_repository, feature_list):
	"""
	translate the output of the solver into a system to install (mapping from spl names to use flag selection)
	:param id_repository: the id repository of hyportage
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
	for use_flag, spl_name in use_flags:
		if spl_name in spl_names:
			res.add(spl_name, use_flag)
	return res


def solve_spls(
		id_repository, config, mspl, spl_groups, installed_spls,
		spls, annex_constraint, exploration_use, exploration_mask, exploration_keywords, hyvarrec_url, par=1,
		explain_modality=False):
	"""
	Solves the spls in input locally assuming that there is a command hyvar-rec
	:param id_repository: the id repository of hyportage
	:param config: the config of hyportage
	:param mspl: the mspl of hyportage
	:param spl_groups: the spl groups of hyportage
	:param installed_spls: the mapping stating the use flag selection for all installed spls
	:param spls: the spls to solve
	:param annex_constraint: the additional constraint to add in the solver input
	:param exploration_use: boolean saying if the solver can change the use flag default selection
	:param exploration_mask: boolean saying if the solver can change the use mask status of the packages
	:param exploration_keywords: boolean saying if the solver can change the keywords of the packages
	:param par: the number of threads to use for resolution (by default: 1)
	:param explain_modality: boolean saying if a problem should be explained (by default: False)
	:return: the solution found by the solver, if it exists
	"""
	spl_names = {spl.name for spl in spls}
	# 1. construct the input data for the solver
	# 1.1. construct the constraint
	constraint = annex_constraint[:]
	spl_group_names = core_data.dictSet()
	#tmp = 0
	for spl in spls:
		spl_group_names.add(core_data.spl_core_get_spl_group_name(spl.core), spl)
		included = (spl.unmasked or exploration_mask) and ((spl.is_stable and spl.keyword_mask) or exploration_keywords)
		if included:
			#tmp = tmp + 1
			constraint.extend(spl.smt())
			if exploration_use:
				constraint.extend(spl.smt_use_exploration(id_repository, config))
			else:
				if spl in installed_spls:
					constraint.extend(smt_encoding.convert_use_flag_selection(
						id_repository, spl.name, spl.required_iuses, installed_spls[spl]))
				else:
					constraint.extend(spl.smt_use_selection(id_repository, config))
		else:
			#logging.info("spl \"" + spl.name + "\" is not scheduled for possible installation")
			constraint.extend(spl.smt_false(id_repository))
	for spl_group_name, spls_tmp in spl_group_names.iteritems():
		spl_group = spl_groups[spl_group_name]
		constraint.extend(spl_group.smt_constraint)
		for spl in spl_group.references:
			if spl not in spls_tmp: constraint.append(smt_encoding.smt_to_string(smt_encoding.get_smt_not_spl_name(id_repository, spl.name)))
	#logging.info("included spl: " + str(tmp))
	logging.debug("number of constraints to solve: " + str(len(constraint)))
	# 1.2. construct the preferences
	preferences = [get_preferences_core(id_repository, mspl, installed_spls, spl_names)]
	# 1.3. construct the current system
	current_system = installed_spls_to_solver(id_repository, installed_spls, spl_names)
	data_configuration = {"selectedFeatures": current_system, "attribute_values": [], "context_values": []} # current configuration
	data_smt_constraints = {"formulas": constraint, "features": [], "other_int_symbols": []}
	data = {
		"attributes": [],  # attributes of the features (empty in our case)
		"contexts": [],  # contexts to consider (empty in our case)
		"configuration": data_configuration,
		"constraints": [], # constraints to fill in hyvarrec format (empty in our case for efficiency)
		"preferences": preferences, # preferences in hyvarrec format
		"smt_constraints": data_smt_constraints,
		"hyvar_options": ["--features-as-boolean", "--constraints-minimization"]
	}

	# 2. run hyvar-rec
	if hyvarrec_url:
		res = run_remote_hyvar(data, explain_modality, hyvarrec_url)
	else:
		res = run_hyvar(data, explain_modality, par)
	if res is None: return None

	# 4. managing the solver output
	if res["result"] != "sat":
		if explain_modality:
			# todo handle explain modality when the answer is unsat
			# try to print a better explanation of the constraints
			constraints = get_better_constraint_visualization(id_repository, mspl, res["constraints"])
			logging.error("Conflict detected. Explanation:\n" + "\n".join(constraints) + '\n')
		return None
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

	added_spl_names = [spl_name for spl_name in to_install_spl_names if spl_name not in set(installed_spl_names)]
	removed_spl_names = [
		spl_name for spl_group_name in removed_spl_groups for spl_name in installed_spl_groups_dict[spl_group_name]]

	with open(path_install_script, 'w') as f:
		f.write("#!/bin/bash\n")
		f.write("\n")
		f.write("# File auto-generated by the hyportage tool\n")
		f.write("# Do not update, any modification on this file will will overwritten by the tool\n")
		f.write("\n")
		if added_spl_names:
			f.write("emerge -a --newuse -u " + " ".join(["=" + spl_name for spl_name in added_spl_names]) + "\n")
		if removed_spl_names:
			f.write("emerge --unmerge " + " ".join(["=" + spl_name for spl_name in removed_spl_names]) + "\n")
		f.write("\n")


def generate_package_use_file(mspl, path_use_flag_configuration, to_install_spls):
	"""
	This function generates the spl configuration file (usually package.use) from the solution found by the solver
	:param mspl: the mspl of hyportage
	:param path_use_flag_configuration: path to the configuration file to generate
	:param to_install_spls: the new system generated by the solver
	:return: None (but the configuration file has been generated)
	"""
	with open(path_use_flag_configuration, 'w') as f:
		f.write("# File auto-generated by the hyportage tool\n")
		f.write("# Do not update, any modification on this file will will overwritten by the tool\n")
		f.write("\n")
		for spl_name, use_selection in to_install_spls.iteritems():
			string = "=" + spl_name + " "
			string = string + " ".join(use_selection)
			use_unselection = mspl[spl_name].iuses_full - use_selection
			if use_unselection:
				string = string + " -" + " -".join(use_unselection) + "\n"
			f.write(string)
		f.write("\n")


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





