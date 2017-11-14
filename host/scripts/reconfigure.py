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
import portage_data

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


# todo michael: generate constraint from use selection, as a valid alternative from preference

# todo request for now just indicate packages to insall -> implement unmerge feature to remove packages

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
	for pattern in requested_patterns:
		hyportage_pattern.pattern_repository_local_map_add_pattern_from_scratch(pattern_repository, pattern)

	requested_patterns.update(config.pattern_required_flat)
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
		- keep more use flags used as possible,
		- minimize number of new packages to install
		- minimize number of flags install in new packages
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
	return pref_less_remove + " - (" + pref_less_add + ")"


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
		constraint.append(spl.smt())
		if spl.installable and fixed_use_flags:
			if spl in installed_spls:
				constraint.append(smt_encoding.convert_use_flag_selection(
					id_repository, spl.name, spl.required_iuses, installed_spls[spl]))
			else:
				constraint.append(spl.smt_use_selection(id_repository, config))
	for spl_group_name, spls_tmp in spl_group_names.iteritems():
		spl_group = spl_groups[spl_group_name]
		constraint.append(spl_group.smt_constraint)
		for spl in spl_group.references:
			if spl not in spls_tmp: constraint.append(smt_encoding.get_smt_not_spl_name(id_repository, spl.name))

	data = {
		"attributes": [],  # attributes of the features (empty in our case)
		"contexts": [],  # contexts to consider (empty in our case)
		"configuration": {  # current configuration
			"selectedFeatures": [],
			"attribute_values": [],
			"context_values": []},
		"constraints": [],  # constraints to fill in hyvarrec format (empty in our case for efficiency)
		"preferences": [],  # preferences in hyvarrec format
		"smt_constraints": {  # constraints, in smt format
			"formulas": [],
			"features": [],
			"other_int_symbols": []}
	}
	data['smt_constraints']['formulas'] = constraint
	data['preferences'] = get_preferences_core(id_repository, mspl, installed_spls, spls)

	# 2. generate the input file for the solver and the command line
	file_name = utils.get_new_temp_file("json")
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
		res.update(hyportage_pattern.pattern_repository_element_get_spls_visible(
			hyportage_pattern.pattern_repository_get(pattern_repository, pattern), mspl, spl_groups))
	return res


def get_dependency_transitive_closure(pattern_repository, mspl, spl_groups, spls):
	nexts = spls
	res = set()
	while len(nexts) > 0:
		accu = set()
		for spl in nexts:
			spl.visited = True
			res.add(spl)
			accu.update(next_spls(pattern_repository, mspl, spl_groups, spl))
		nexts = filter(lambda spl: not hyportage_data.spl_is_visited(spl), accu)
	return res







###############################################################################
###############################################################################
###############################################################################






def get_hyvarrec_input_monolithic(
		pattern_repository, id_repository, mspl, spl_groups, installed_spls,
		all_spls, smt_constraint, par, explain_modality):
	data = {
			"attributes": [],             # attributes of the features (empty in our case)
			"contexts": [],               # contexts to consider (empty in our case)
			"configuration": {            # current configuration (list of selected features)
				"selectedFeatures": [],
				"attribute_values": [],
				"context_values": []},
			"constraints": [],            # constraints to fill in hyvarrec format (empty in our case for efficiency)
			"preferences": [],            # preferences in hyvarrec format
			"smt_constraints": {          # constraints, in smt format
				"formulas": [],
				"features": [],
				"other_int_symbols": []}
		}
	# get the transitive closure of the dependency
	dep_spls = get_dependency_transitive_closure(
		pattern_repository, mspl, spl_groups, all_spls | {mspl[spl_name] for spl_name in installed_spls.keys()})
	# setup the constraint
	data['smt_constraints']['formulas'] = smt_constraint
	data['smt_constraints']['formulas'].extend(get_smt_constraint_from_spls(spl_groups, dep_spls))
	# setup the preferences
	data['preferences'] = get_preferences_core(id_repository, mspl, installed_spls, dep_spls)
	data['preferences'].extend(get_preferences_from_spls_use_selection(id_repository, dep_spls))
	# setup the initial configuration
	data['configuration']['selectedFeatures'] = get_smt_variables_from_installed_spls(id_repository, installed_spls)
	# todo ask michael why no selected features are added to data['configuration']['selectedFeatures']

	# execute hyvar-rec
	feature_list = solve_spls(id_repository, mspl, data, par, explain_modality)
	to_install_spls = core_data.package_installed_create()
	generate_to_install_spls(id_repository, mspl, to_install_spls, feature_list)
	return to_install_spls


##########################################################################
# 4. INCREMENTAL CONFIGURATION SEARCH
##########################################################################

# TODO

##########################################################################
# 5. SCRIPT AND CONFIGURATION FILES GENERATION
##########################################################################




# DEPRECATED




# this function compute the constraints corresponding to the user request, and returns the list of package involved in that constraint.
# I guess this function will get removed, as it is far more complex than necessary.
def process_request_old(pattern_repository, id_repository, mspl, spl_groups, requested_patterns, default_patterns):
	def local_function(pattern_repository, id_repository, patterns):
		spls = set()
		smt_constraint = []

		for pattern in patterns:
			local_spls = hyportage_pattern.pattern_repository_element_get_spls(
				hyportage_pattern.pattern_repository_get(pattern_repository, pattern), mspl, spl_groups)
			smt_constraint.append(smt_encoding.smt_or(
				smt_encoding.get_smt_spl_names(id_repository, [hyportage_data.spl_get_name(spl) for spl in local_spls])))
			spls.update(local_spls)
		return spls, smt_constraint
	requested_spls, smt_constraint = local_function(pattern_repository, id_repository, requested_patterns)
	all_spls, additional_smt_constraint = local_function(pattern_repository, id_repository, default_patterns)
	smt_constraint.extend(additional_smt_constraint)
	# convert all smt constraint in textual form to be saved later in the hyvarrec json input format
	txt_smt_constraint = smt_encoding.simplify_constraints("request constraint",smt_constraint,"individual")
	all_spls.update(requested_spls)
	return txt_smt_constraint, requested_spls, all_spls




"""
def load_request_file(file_name, pattern_repository, id_repository, mspl, spl_groups, core_configuration):
	with open(file_name, "r") as f:
		lines = f.readlines()

	# todo add in the request the default pattern request (assuming that is in core_configuration)
	# add core_configuration profile does not work (some constraints there make the problem unsat since some patterns
	# can not be installed
	# lines.extend([hyportage_pattern.pattern_to_atom(x) for x in hyportage_configuration.core_configuration_get_profile_patterns(core_configuration)])
	smt_visitor = smt_encoding.ASTtoSMTVisitor(pattern_repository, id_repository, "dummy_pkg_name")

	dependencies = set()
	smt_constraints = []

	for l in lines:
		parsed_line = hyportage_from_egencache.translate_depend(l)
		dep_visitor = hyportage_from_egencache.GETDependenciesVisitor("dummy_pkg_name")
		dep_visitor.visitDepend(parsed_line)
		patterns = dep_visitor.res[1]
		for pattern in patterns:
			if not hyportage_pattern.is_pattern_in_pattern_repository(pattern_repository, pattern):
				hyportage_pattern.pattern_repository_add_pattern(pattern_repository, mspl, spl_groups, pattern)
		dependencies.update([pattern[1] for pattern in patterns])
		smt_constraints.append(smt_visitor.visitDepend(parsed_line))
		print smt_constraints[-1]
		print patterns
		print [pattern[1] for pattern in patterns]
	smt_constraints = smt_encoding.simplify_constraints("user_req", smt_constraints, "individual")
	return dependencies, smt_constraints
	# returns the spl_group_names referenced in the request and the smt constraints corresponding to the request

# def load_configuration_file(file_name):
#     with open(file_name,"r") as f:
#         lines = f.readlines()
#     initial_configuration = {}
#     for l in lines:
#         ls = l.split(" ")
#         assert ls
#         assert ls[0][0] == "="
#         pkg_name = ls[0][1:]
#         initial_configuration[pkg_name] = [x for x in ls[1:]
#                                     if not x.startswith("-")]
#     return initial_configuration


def run_hyvar(json_data, par, explain_modality):
	file_name = utils.get_new_temp_file("json")
	with open(file_name, "w") as f:
		json.dump(json_data, f)
		# json.dump(json_data, f,indent=1)
	cmd = ["hyvar-rec", "--features-as-boolean"]
	if par > 1:
		cmd += ["-p", unicode(par)]
	if explain_modality:
		cmd.append("--explain")
	cmd.append(file_name)
	logging.debug("Running command " + unicode(cmd))
	process = psutil.Popen(cmd, stdout=PIPE, stderr=PIPE)
	out, err = process.communicate()
	logging.debug('Stdout of ' + unicode(cmd))
	logging.debug(out)
	logging.debug('Stderr of ' + unicode(cmd))
	logging.debug(err)
	logging.debug('Return code of ' + unicode(cmd) + ': ' + str(process.returncode))
	# in explain modality prints the output to detect which constraints are unsat
	if explain_modality:
		print(out)
	return json.loads(out)

# def run_remote_hyvar(json_data,url):
#     logging.debug("Invoking service at url " + url)
#     response = requests.post(url + "/explain",
#                              data=json.dumps(json_data),
#                              headers={'content-type': 'application/json'})
#     return response.json()


def get_transitive_closure_of_dependencies(mspl, spl_groups, pkg):
	# returns the transitive closure of the dependencies
	deps = set([pkg])
	to_check = [pkg]
	checked = set()
	while to_check:
		p = to_check.pop()
		if p in spl_groups:
			ls = hyportage_data.spl_group_get_references(spl_groups[p])
		elif p in mspl:
			ls = [pattern[1] for pattern in hyportage_data.spl_get_dependencies(mspl[p])]
		else:
			ls = []
			logging.warning("Package " + p + " not found in the mspl or spl groups.")
		for i in ls:
			if i not in checked:
				to_check.append(i)
				deps.add(i)
		checked.add(p)
	return deps


def create_hyvarrec_spls(package_request,
						 request_constraints,
						 initial_configuration,
						 # contex_value,
						 mspl,
						 spl_groups,
						 id_repository):

	spls = {}

	logging.debug("Start computing the transitive closure of dependencies")
	to_process = set(package_request)
	to_process.update(initial_configuration.keys())
	# todo: this part can be more efficient using union find
	while to_process:
		i = to_process.pop()
		spls[i] = get_transitive_closure_of_dependencies(mspl, spl_groups, i)
		to_process.difference_update(spls[i])
		intersections = [x for x in spls if spls[i].intersection(spls[x]) and x != i]
		if intersections:
			for j in intersections:
				spls[i].update(spls[j])
				del(spls[j])
	logging.debug("Transitive closure of dependencies computed.")

	jsons = []
	for i in spls:
		data = {"attributes": [],  # attributes of the features (empty in our case)
				"contexts": [],  # contexts to consider (empty in our case)
					# {"id": "context[" + utils.CONTEXT_VAR_NAME + "]",
					#           "min": 0,
					#           "max": len(map_name_id["context_int"])-1}],
				"configuration": {  # current configuration (list of selected features)
					"selectedFeatures": [],
					"attribute_values": [],
					"context_values": []},
					# "context_values": [{"id": "context[" + utils.CONTEXT_VAR_NAME + "]",
					#                     "value": map_name_id["context_int"][contex_value]}]},
				"constraints": [],  # constraints to fill in hyvarrec format (empty in our case for efficiency)
				"preferences": [],  # preferences in hyvarrec format
				"smt_constraints": {
					"formulas": [],
					"features": [],
					"other_int_symbols": [ "context[" + utils.CONTEXT_VAR_NAME + "]"] }
				}

		# add the constraints of the packages
		for j in spls[i]:
			if j in mspl:
				data["smt_constraints"]["formulas"].extend(hyportage_data.spl_get_smt_constraint(mspl[j]))
			# no need to add features since they are already boolean values

		# add constraints to select the required packages
		data["smt_constraints"]["formulas"].extend(request_constraints)

		# add info about the initial configuration
		for j in initial_configuration:
			if j in mspl and j in spls[i]:
				for k in initial_configuration[j][0]:
					if k in hyportage_ids.id_repository_get_use_flag_from_spl_name(id_repository,j):
						data["configuration"]["selectedFeatures"].append(
							smt_encoding.get_smt_int_use_flag(id_repository, j, k))
					else:
						logging.warning("The initial flag " + k + " was not available for the package " + j)

		# add preferences: do not remove packages already installed
		data["preferences"].append( " + ".join(
			[smt_encoding.get_smt_int_spl_name(id_repository, pkg) for pkg in initial_configuration
			 if pkg in spls[i]]))

		logging.debug("SPL created : constraints " + unicode(len(data["constraints"])) +
					  ", smt formulas " + unicode(len(data["smt_constraints"]["formulas"])))
		logging.debug("Packages to configure " + unicode(len(spls[i])))

		jsons.append({"json":data, "deps": spls[i]})
	return jsons
	# returns a list of constraints, more or less, where a lot of stuff is duplicated. I don't understand why


















def get_diff_configuration(new_conf, old_conf):
	data = {"toUpdate": {}, "toInstall": {}, "toRemove": {}}
	for i in new_conf:
		if i in old_conf:
			if set(new_conf[i]) != set(old_conf[i][0]):
				data["toUpdate"][i] = new_conf[i]
		else:
			data["toInstall"][i] = new_conf[i]
	for i in old_conf.keys():
		if i not in new_conf:
			data["toRemove"][i] = {}
	return data


def get_conf_with_negative_use_flags(conf, map_name_id):
	data = {}
	for i in conf.keys():
		all_flags = map_name_id["flag"][i].keys()
		positive_flags = conf[i]
		negative_flags = set(all_flags)
		negative_flags.difference_update(positive_flags)
		data[i] = positive_flags + [ "-" + x for x in negative_flags]
	return data





@click.command()
@click.option(
	'--input-file', '-i',
	type=click.Path(exists=True, file_okay=True, dir_okay=False, writable=False, readable=True, resolve_path=True),
	help="File generated by using the hyportage translate functionality",
	default="host/data/hyportage/hyportage.enc")
@click.option(
	'--request-file',
	type=click.Path(exists=True, file_okay=True, dir_okay=False, writable=False, readable=True, resolve_path=True),
	help="Request file, following the dependency syntax (more than one line is allowed)",
	default="myreq")
# @click.option(
#     '--configuration_file',
#     type=click.Path(exists=True, file_okay=True, dir_okay=False, writable=False, readable=True, resolve_path=True),
#     help="File representing the current configuration of the system",
#     default="host/configuration/package.use")
# @click.option(
#     'new_configuration_file',
#     type=click.Path(exists=False, file_okay=True, dir_okay=False, writable=True, readable=True, resolve_path=True))
# @click.option(
#     'package_use_file',
#     type=click.Path(exists=False, file_okay=True, dir_okay=False, writable=True, readable=True, resolve_path=True))
@click.option(
	'--emerge_commands_file',
	type=click.Path(exists=False, file_okay=True, dir_okay=False, writable=True, readable=True, resolve_path=True),
	help="Script command to execute emerge to install the computed packages",
	default="emerge.sh")

# @click.option('--environment', default="amd64", help="Keyword identifying the architecture to use.")
@click.option(
	'--verbose', '-v',
	count=True,
	help="Print debug messages.")
@click.option('--keep', '-k', is_flag=True, help="Do not delete intermediate files.")
@click.option('--explain', is_flag=True, help="Run HyVarRec in explanation mode.")
@click.option('--url', '-r', default="", help='URL of the remote hyvarrec to use if available (local command otherwise used).')
@click.option('--par', '-p', type=click.INT, default=-1, help='Number of process to use for running the local HyVarRec.')
@click.option(
	'--save-modality',
	type=click.Choice(["json", "gzjson", "marshal", "pickle"]), default="pickle",
	help='Saving modality. Marshal is supposed to be faster but python version specific.')
def main(
		input_file,
		request_file,
		emerge_commands_file,
		verbose,
		keep,
		explain,
		url,
		par,
		save_modality):


	##########################################################################
	# 1. OPTIONS
	##########################################################################

	# 1.1. verbose option
	if verbose != 0:
		if verbose == 1:
			logging.basicConfig(format="%(levelname)s: %(message)s", level=logging.WARNING)
		elif verbose == 2:
			logging.basicConfig(format="%(levelname)s: %(message)s", level=logging.INFO)
		elif verbose >= 3:
			logging.basicConfig(format="%(levelname)s: %(message)s", level=logging.DEBUG)
		logging.warning("Verbose (" + str(verbose) + ") output.")
	else:
		logging.basicConfig(format="%(levelname)s: %(message)s", level=logging.ERROR)

	# 1.2. parallel process option
	if par != -1: available_cores = min(par, multiprocessing.cpu_count())
	else: available_cores = 1

	if available_cores > 1:
		pool = multiprocessing.Pool(available_cores)
		concurrent_map = pool.map
	else: concurrent_map = map




	# logging.info("Load the MSPL. This may take a while.")
	# t = time.time()
	# data = utils.load_data_file(input_file,save_modality)
	# mspl,map_name_id,map_id_name = data["mspl"],data["map_name_id"],data["map_id_name"]
	# logging.info("Loading completed in " + unicode(time.time() - t) + " seconds.")

	#logging.info("Loading the stored hyportage data.")
	#t = time.time()
	#hyportage_file_path = os.path.abspath(input_file)
	#pattern_repository, id_repository, mspl, spl_groups, core_configuration, installed_spls = \
	#    hyportage.load_hyportage(hyportage_file_path, save_modality)
	#logging.info("Loading completed in " + unicode(time.time() - t) + " seconds.")

	#logging.info("Load the request package list.")
	#t = time.time()
	dependencies, constraints = load_request_file(request_file,pattern_repository,id_repository,mspl,spl_groups,core_configuration)
	logging.info("Loading completed in " + unicode(time.time() - t) + " seconds.")
	logging.debug("Dependencies: " + unicode(dependencies))
	logging.debug("Constraints: " + unicode(constraints))

	# logging.info("Load the configuration file.")
	# t = time.time()
	# initial_configuration = load_configuration_file(configuration_file)
	# logging.info("Loading completed in " + unicode(time.time() - t) + " seconds.")
	#

	logging.info("Computing the SPLs.")
	t = time.time()
	to_solve = create_hyvarrec_spls(dependencies,
									constraints,
									installed_spls,
									# environment,
									mspl,
									spl_groups,
									id_repository)
	logging.info("Computation completed in " + unicode(time.time() - t) + " seconds.")
	logging.info("SPL to process: " + unicode(len(to_solve)))

	configuration = {}
	for job in to_solve:
		logging.info("Running HyVarRec.")
		t = time.time()
		# if url:
		#     json_result = run_remote_hyvar(job["json"],url)
		# else:
		json_result = run_hyvar(job["json"],par,explain)
		logging.info("Execution of HyVarRec took " + unicode(time.time() - t) + " seconds.")
		if json_result["result"] != "sat":
			if explain:
				# try to print a better explanation of the constraints
				constraints = get_better_constraint_visualization(
					json_result["constraints"],mspl,id_repository)
				sys.stderr.write("Conflict detected. Explanation:\n" + "\n".join(constraints) + '\n')
			logging.error("Conflict detected. Impossible to satisfy the request. Exiting.")
			sys.exit(1)
		logging.debug("HyVarRec output: " + unicode(json_result))
		# update the info on the final configuration
		update_configuration(json_result,configuration,id_repository)

	# remove all the pacakges without version from final configuration
	for i in configuration.keys():
		if i in mspl:
			del(configuration[i])

	configuration_diff = get_diff_configuration(configuration,installed_spls)
	logging.debug("Packages to update flags: " + unicode(len(configuration_diff["toUpdate"])))
	logging.debug("Packages to install: " + unicode(len(configuration_diff["toInstall"])))
	logging.debug("Packages to remove: " + unicode(len(configuration_diff["toRemove"])))
	# print in std out the diff of the new configuration
	print(json.dumps(configuration_diff,indent=1))

	logging.debug("Generate emerge commands to run.")
	with open(emerge_commands_file, "w") as f:
		f.write("#!/bin/bash\n")
		if configuration_diff["toRemove"].keys():
			f.write("emerge --unmerge " + " ".join(["=" + x for x in configuration_diff["toRemove"].keys()]) + "\n")
		if configuration_diff["toUpdate"].keys() + configuration_diff["toInstall"].keys():
			f.write("emerge -a --newuse " + " ".join(["=" + x for x in configuration_diff["toUpdate"].keys()]) +
				" " + " ".join(["=" + x for x in configuration_diff["toInstall"].keys()]) + "\n")

	# logging.debug("Printing the final configuration with all the positive and negative use flags.")
	# final_conf = get_conf_with_negative_use_flags(configuration,map_name_id)
	# with open(new_configuration_file,"w") as f:
	#     json.dump(final_conf,f,indent=1)

	# logging.debug("Printing the package.use file.")
	# with open(package_use_file,"w") as f:
	#     for i in final_conf.keys():
	#         f.write("=" + i + " " + " ".join(final_conf[i]) + "\n")

	logging.info("Cleaning.")
	if keep: utils.clean_temp_files()
	logging.info("Execution terminated correctly.")


if __name__ == "__main__":
	main()
	
"""
