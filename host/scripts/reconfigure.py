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

import hyportage_pattern
import hyportage_db

from pysmt.smtlib.parser import SmtLib20Parser
import cStringIO


"""
This file contains all the functions related to solving the constraints generated from a set of spls,
in order to compute a new configuration of the system
"""


__author__ = "Michael Lienhardt and Jacopo Mauro"
__copyright__ = "Copyright 2017, Michael Lienhardt and Jacopo Mauro"
__license__ = "GPL3"
__version__ = "0.5"
__maintainer__ = "Michael Lienhardt and Jacopo Mauro"
__email__ = "michael lienhardt@laposte.net & mauro.jacopo@gmail.com"
__status__ = "Prototype"


##########################################################################
# UTILITIES TO CALL THE HYVAR-REC SOLVER
##########################################################################


def run_local_hyvar(json_data, explain_modality, cmd, par_cores):
	"""
	Run hyvar locally assuming that there is a command hyvar-rec
	"""
	file_name = utils.get_new_temp_file(".json")
	with open(file_name, "w") as f:
		json.dump(json_data, f)
	cmd.extend(["--constraints-minimization", "--features-as-boolean", "--no-default-preferences"])
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
	res = response.json()
	if 'error' in res:
		logging.error("server answered with an error message: " + json.dumps(res))
		return None
	return res


run_hyvar = None

##########################################################################
# 1. INITIALIZE THE DATA (COMPUTE REQUEST AND UPDATE THE DATABASE)
##########################################################################


def process_request(pattern_repository, id_repository, config, atoms):
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

	config.set_use_manipulation_env(os.environ.get("USE", "").split())

	root_spls, constraint = smt_encoding.convert_patterns(pattern_repository, id_repository, requested_patterns)
	return root_spls, constraint


##########################################################################
# 2. SOLVER WRAPPER
##########################################################################


def get_preferences_core(id_repository, mspl, installed_spls, spl_name_set):
	"""
	the priority of preferences is decided as follows:
		- remove less packages installed as possible,
		- minimize number of new packages to install
	:param id_repository: the repository of hyportage
	:param mspl: the mspl of hyportage
	:param installed_spls: the currently installed spls with their configuration
	:param spl_name_set: the names of the spls considered in the reconfiguration process
	:return: an equation encoding the preference as described previously
	"""
	installed_spls = {
		spl_name
		for spl_name in installed_spls.iterkeys()
		if (spl_name in spl_name_set) and (not mspl[spl_name].is_deprecated)}
	uninstalled_spls = spl_name_set - installed_spls
	# preference for removing less packages installed and not deprecated as possible
	res = '0'
	if installed_spls:
		res = " + ".join([
			smt_encoding.get_spl_hyvarrec(id_repository, spl_name) for spl_name in installed_spls])
	# preference to minimize number of new packages to install
	if uninstalled_spls:
		res = res + " - (" + (" + ".join([
			smt_encoding.get_spl_hyvarrec(id_repository, spl_name) for spl_name in uninstalled_spls])) + ")"
	return [res]


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
			res.append(smt_encoding.get_spl_hyvarrec(id_repository, spl_name))
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
		# translate packages
		where_declared = "user-required: "
		spl_ids = set(re.findall('(p[0-9]+)', formula))
		for spl_id in spl_ids:
			name = id_repository.ids[spl_id][1]
			formula = re.sub(spl_id, name, formula)
			if i in mspl[name].smt:
				where_declared = name + ": "

		# translate uses
		use_ids = set(re.findall('(u[0-9]+)', formula))
		for use_id in use_ids:
			formula = re.sub(use_id, id_repository.ids[use_id][2] + "#" + id_repository.ids[use_id][1], formula)
		ls.append(where_declared + formula)
	return ls


def generate_to_install_spls(id_repository, mspl, feature_list):
	"""
	translate the output of the solver into a system to install (mapping from spl names to use flag selection)
	:param id_repository: the id repository of hyportage
	:param mspl: the mspl of hyportage
	:param feature_list: the solution found by the solver
	:return: a dictionary spl_name -> use flag selection
	"""
	# 1. translate the computed solution into a configuration
	res_core = core_data.dictSet()
	use_flags = []
	for feature in feature_list:
		el = id_repository.data_from_id(feature)
		if el[0] == "package":  # el = ("package", spl_name)
			res_core.add_key(el[1])
		else:  # el = ("use", use, spl_name)
			use_flags.append((el[1], el[2]))
	for use_flag, spl_name in use_flags:
		if spl_name in res_core:
			res_core.add(spl_name, use_flag)

	# 2. compares the computed solution to the actual spl use flag configuration, and generate the final configuration
	res = core_data.dictSet()
	for spl_name, use_selection_core in res_core.iteritems():
		spl = mspl[spl_name]
		if spl.use_selection_core == use_selection_core:
			res[spl_name] = spl.use_selection_full
		else:
			annex_use_flags = spl.use_selection_full - spl.iuses_core
			res[spl_name] = use_selection_core | annex_use_flags
	return res


def solve_spls(
		id_repository, config, mspl, spl_groups,
		spls, annex_constraint, exploration_use, exploration_mask, exploration_keywords, explain_modality=False):
	"""
	Solves the spls in input locally assuming that there is a command hyvar-rec
	:param id_repository: the id repository of hyportage
	:param config: the config of hyportage
	:param mspl: the mspl of hyportage
	:param spl_groups: the spl groups of hyportage
	:param spls: the spls to solve
	:param annex_constraint: the additional constraint to add in the solver input
	:param exploration_use: boolean saying if the solver can change the use flag default selection
	:param exploration_mask: boolean saying if the solver can change the use mask status of the packages
	:param exploration_keywords: boolean saying if the solver can change the keywords of the packages
	:param explain_modality: boolean saying if a problem should be explained (by default: False)
	:return: the solution found by the solver, if it exists
	"""
	# 1. construct the input data for the solver
	# 1.1. construct the constraint
	constraint = annex_constraint[:]
	spl_group_names = core_data.dictSet()
	#tmp = 0
	for spl in spls:
		spl_group_names.add(core_data.spl_core_get_spl_group_name(spl.core), spl)
		included = (spl.unmasked or exploration_mask) and ((spl.is_stable and spl.unmasked_keyword) or exploration_keywords)
		if included:
			#tmp = tmp + 1
			constraint.extend(spl.smt)
			if exploration_use:
				constraint.extend(spl.smt_use_exploration)
			else:
				constraint.extend(spl.smt_use_selection)
		else:
			#logging.info("spl \"" + spl.name + "\" is not scheduled for possible installation")
			constraint.extend(spl.smt_false)
	for spl_group_name, spls_tmp in spl_group_names.iteritems():
		spl_group = spl_groups[spl_group_name]
		constraint.extend(spl_group.smt)
		for spl in spl_group:
			if spl not in spls_tmp: constraint.append(smt_encoding.smt_to_string(smt_encoding.get_spl_smt_not(id_repository, spl.name)))
	#logging.info("included spl: " + str(tmp))
	logging.debug("number of constraints to solve: " + str(len(constraint)))
	# 1.2. construct the preferences
	spl_names = {spl.name for spl in spls}
	preferences = get_preferences_core(id_repository, mspl, config.installed_packages, spl_names)
	# 1.3. construct the current system
	current_system = [] #installed_spls_to_solver(id_repository, installed_spls, spl_names)
	data_configuration = {"selectedFeatures": current_system, "attribute_values": [], "context_values": []} # current configuration
	data_smt_constraints = {"formulas": constraint, "features": [], "other_int_symbols": []}
	data = {
		"attributes": [],  # attributes of the features (empty in our case)
		"contexts": [],  # contexts to consider (empty in our case)
		"configuration": data_configuration,
		"constraints": [], # constraints to fill in hyvarrec format (empty in our case for efficiency)
		"preferences": preferences, # preferences in hyvarrec format
		"smt_constraints": data_smt_constraints,
		"hyvar_options": ["--features-as-boolean", "--constraints-minimization", "--no-default-preferences"]
	}

	# 2. run hyvar-rec
	res = run_hyvar(data)
	if res is None: return None
	logging.debug("HyVarRec output: " + json.dumps(res))

	# 4. managing the solver output
	if res["result"] != "sat":
		if explain_modality:
			# todo handle explain modality when the answer is unsat
			# try to print a better explanation of the constraints
			constraints = get_better_constraint_visualization(id_repository, mspl, res["constraints"])
			logging.error("Conflict detected. Explanation:\n" + "\n".join(constraints) + '\n')
		return None

	return generate_to_install_spls(id_repository, mspl, res['features'])


def generate_installation_files(
		mspl,
		path_emerge_script, path_use_flag_configuration, path_mask_configuration, path_keywords_configuration,
		old_installation, new_installation):
	"""
	This function generates two files:
	1. the script file to execute to install and uninstall the spls found by the solver
	2. spl configuration file (usually package.use) from the solution found by the solver
	:param mspl: the mspl of hyportage
	:param path_emerge_script: path to the script file to generate
	:param path_use_flag_configuration: path to the configuration file to generate
	:param path_mask_configuration: the path to the unmask file to generate
	:param path_keywords_configuration: the path to the accept_keywords file to generate
	:param old_installation: the currently installed spls
	:param new_installation: the spls to install, found by the solver
	:return: None (but the script file has been generated)
	"""

	# the spls to emerge are the ones that are not present in the old installation, or that have a new configuration
	added_spl_names = []
	for spl_name, product in new_installation.iteritems():
		if spl_name in old_installation:
			if old_installation[spl_name] != product:
				added_spl_names.append(spl_name)
		else: added_spl_names.append(spl_name)

	# the spls to remove are the ones that are not in the new configuration and that are not replaced by a new version
	removed_spl_names = []
	new_spl_goups_info = core_data.dictSet()
	for spl_name in new_installation.iterkeys():
		spl = mspl[spl_name]
		new_spl_goups_info.add(core_data.spl_core_get_spl_group_name(spl.core), spl)
	for spl_name in old_installation.iterkeys():
		spl = mspl[spl_name]
		new_versions = new_spl_goups_info.get(core_data.spl_core_get_spl_group_name(spl.core))
		if new_versions is None:
			removed_spl_names.append(spl_name)
		else:
			replaced = False
			for new_spl in new_versions:
				if (spl.slot == new_spl.slot) and (spl.name != new_spl.name):
					replaced = True
					break
			if replaced: removed_spl_names.append(spl_name)

	# write the files
	added_spl_names.sort()
	with open(path_emerge_script, 'w') as f:
		f.write("#!/bin/bash\n")
		f.write("\n")
		f.write("# File auto-generated by the hyportage tool\n")
		f.write("# Do not update, any modification on this file will will overwritten by the tool\n")
		f.write("\n")
		if added_spl_names:
			f.write("emerge -a --newuse " + " ".join(["=" + spl_name for spl_name in added_spl_names]) + "\n")
		if removed_spl_names:
			f.write("emerge --unmerge " + " ".join(["=" + spl_name for spl_name in removed_spl_names]) + "\n")
		f.write("\n")

	with open(path_use_flag_configuration, 'w') as f:
		f.write("# File auto-generated by the hyportage tool\n")
		f.write("# Do not update, any modification on this file will will overwritten by the tool\n")
		f.write("\n")
		for spl_name in added_spl_names:
			use_selection = new_installation[spl_name]
			string = "=" + spl_name + " "
			string = string + " ".join(use_selection)
			use_unselection = mspl[spl_name].iuses_full - use_selection
			if use_unselection:
				string = string + " -" + " -".join(use_unselection) + "\n"
			f.write(string)
		f.write("\n")

	with open(path_mask_configuration, 'w') as f:
		f.write("# File auto-generated by the hyportage tool\n")
		f.write("# Do not update, any modification on this file will will overwritten by the tool\n")
		f.write("\n")
		for spl_name in added_spl_names:
			if not mspl[spl_name].unmasked:
				f.write("=" + spl_name)
		f.write("\n")

	with open(path_keywords_configuration, 'w') as f:
		f.write("# File auto-generated by the hyportage tool\n")
		f.write("# Do not update, any modification on this file will will overwritten by the tool\n")
		f.write("\n")
		for spl_name in added_spl_names:
			if not mspl[spl_name].unmasked_keyword:
				f.write("=" + spl_name + " ~" + hyportage_db.mspl_config.arch)
		f.write("\n")


##########################################################################
# 3. SPL SET COMPUTATION
##########################################################################


def next_spls(pattern_repository, spl):
	res = set()
	pattern_iterator = spl.dependencies.iterkeys()
	for pattern in pattern_iterator:
		res.update(pattern_repository.get_with_default(pattern).matched_spls)
	return res


def get_dependency_transitive_closure(pattern_repository, mspl, spls):
	for spl in mspl.itervalues():
		spl.visited = False
	nexts = spls
	res = set()
	while len(nexts) > 0:
		accu = set()
		for spl in nexts:
			spl.visited = True
			res.add(spl)
			accu.update(next_spls(pattern_repository, spl))
		nexts = filter(lambda spl: not spl.visited, accu)

	return res





