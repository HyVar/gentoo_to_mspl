#!/usr/bin/python

import sys
import os
import os.path
import logging
import subprocess
import bz2
import json
import cPickle

import core_data
import portage_data


__author__ = "Michael Lienhardt"
__copyright__ = "Copyright 2017, Michael Lienhardt"
__license__ = "ISC"
__version__ = "0.1"
__maintainer__ = "Michael Lienhardt"
__email__ = "michael lienhardt@laposte.net"
__status__ = "Prototype"

"""
This file extracts USE flags declarations, USE flag selection and Package visibility information (mask and keywords)
 that are specified outside the .ebuild files. 

As shown in the documentation, this information is structured in three parts:
 - the one that is 


We assume that the .ebuild file does not declare any variables that are used in
 the later construction of the IUSE and USE variables.
This assumption is motivated by efficiency
  (we would otherwise have to load the portage profile independently for every packages),
 and is supported by the fact that egencache produces files without any annex variables to use in later stages.

We also assume that the EAPI is 6 system-wide.
Indeed, dealing with specific EAPI does not seem useful.
"""


# todo: I need to refactor this file to take in account the information I got on USE flag declarations and selection.
# I thus need to structure the configuration in three parts: one that is


######################################################################
# FILE PATHS
######################################################################

# input

input_dir_portage = os.path.realpath("/usr/portage/metadata/md5-cache/")
input_dir_portage_installed = os.path.realpath("/var/db/pkg/")

input_file_profile_base = os.path.realpath("/usr/portage/profiles")
input_file_profile_selected = os.path.realpath("/etc/portage/make.profile")

input_dir_user_configuration = os.path.realpath("/etc/portage/")
input_file_make_conf = os.path.join(input_dir_user_configuration, "make.conf")
input_file_user_world = os.path.realpath("/var/lib/portage/world")

input_file_keyword_list = os.path.realpath("/usr/portage/profiles/arch.list")


script_dir = os.path.dirname(os.path.abspath(__file__))

# output

non_concurrent_map = map  # the different load processes must be done in sequence


######################################################################
# 1. UTILITY FUNCTIONS FOR LOADING A CONFIGURATION
######################################################################


######################################################################
# 1.1. BASH ENVIRONMENT MANIPULATION

def environment_create_from_script_output(out):
	"""
	Create a dictionary from the output of the "set" (in posix mode) function
	Note that the value of some variable contain \n characters, which explains the tricks used here.
	:param out: the string containing the result of "set"
	:return: the dictionary mapping all the variables present in the output to their value
	"""
	environment = {}
	# variables to deal with shell values being on severa lines
	variable = None
	value = None
	for line in out.splitlines(): # to deal with multiple-line variables
		if value:
			value = value + line
		else:
			array = line.split("=", 1)
			variable = array[0]
			value = array[1]
		if (len(value) == 0) or ((len(value) > 0) and ((value[0] != "'") or (value[-1] == "'"))):
			if (len(value) > 0) and (value[0] == "'"):
				value = value[1:-1]
			environment[variable] = value
			value = None
	return environment


def environment_extract_info(environment):
	"""
	Extracts the important information from an environment: the IUSE, USE, ARCH and ACCEPT_KEYWORDS variables
	:param environment: the input environment
	:return: the tuple containing the values of the important variables
	"""
	use_selection = core_data.SetManipulation()
	use_selection.add_all(environment.get('USE', "").split())
	use_declaration_eapi4 = set(environment.get('IUSE_EAPI_4', "").split())
	use_declaration_eapi5 = set(environment.get('IUSE_EAPI_5', "").split())
	use_declaration_hidden_from_user = set(environment.get('FLAT_PROFILE_ONLY_VARIABLES', "").split())
	arch = environment.get('ARCH')
	accept_keywords = core_data.SetManipulation()
	accept_keywords.add_all(environment.get('ACCEPT_KEYWORDS', "").split())
	return (
		use_selection, use_declaration_eapi4, use_declaration_eapi5,
		use_declaration_hidden_from_user, arch, accept_keywords
	)


##

script_load_make_defaults = os.path.join(script_dir, "load_make_defaults.sh")
def make_defaults_load_file(filename, environment):
	process = subprocess.Popen(["/bin/bash", script_load_make_defaults, filename], stdout=subprocess.PIPE, env=environment)
	out, err = process.communicate()
	return environment_create_from_script_output(out)


##

def load_make_defaults(filename, environment):
	new_environment = make_defaults_load_file(filename, environment)
	return new_environment, environment_extract_info(new_environment)


def get_loading_order(environment):
	new_environment = make_defaults_load_file(input_file_make_conf, environment)
	return list(reversed(new_environment.get('USE_ORDER', "env:pkg:conf:defaults:pkginternal:repo:env.d").split(':')))


######################################################################
# 1.2. USE*, PACKAGE.USE* and PACKAGES MANIPULATION

def parse_configuration_file(filename):
	res = []
	if os.path.isfile(filename):
		with open(filename, 'r') as f:
			for line in f:
				line = line[:-1]  # remove trailing endline
				line = line.split("#", 1)[0]  # remove comment
				line.strip()  # remove starting and trailing spaces
				if len(line) != 0:
					res.append(line)
	return res


def load_use_file(filename):
	res = core_data.SetManipulation()
	res.add_all(parse_configuration_file(filename))
	return res


def load_package_use_file(filename):
	res = core_data.SetManipulationPattern()
	for line in parse_configuration_file(filename):
		els = line.split()
		set_manipulation = core_data.SetManipulation()
		set_manipulation.add_all(els[1:])
		res.add(core_data.pattern_create_from_atom(els[0]), set_manipulation)
	return res


def load_package_mask_file(filename):
	res = core_data.PatternListManipulation()
	res.add_all(parse_configuration_file(filename))
	return res


def load_package_keywords_file(filename):
	res = core_data.SetManipulationPattern()
	for line in parse_configuration_file(filename):
		els = line.split()
		set_manipulation = core_data.SetManipulation()
		set_manipulation.add_all(els[1:])
		res.add(core_data.pattern_create_from_atom(els[0]), set_manipulation)
	return res


def load_packages_file(filename):
	res = core_data.dictSet()
	for line in parse_configuration_file(filename):
		if line[0] == "*":
			res.add("system", core_data.pattern_create_from_atom(line[1:]))
		else:
			res.add("profile", core_data.pattern_create_from_atom(line))
	return res


######################################################################
# 2. UTILITY FUNCTIONS FOR LOADING A PROFILE
######################################################################

# list of use files: use.force   use.mask   use.stable.force   use.stable.mask
# list of package.use files: package.use   package.use.force   package.use.mask
#    package.use.stable.force   package.use.stable.mask
# there is just one make.defaults

# The use.* are global, i.e., they are merged between layers, and applied globally.
# They override declarations made locally to a package

# the order in which they are loaded is as follows:
# package.use use.force use.mask make.defaults

def load_profile_layer(path, environment):
	#######################
	# use* files
	# use.force
	path_use_force = os.path.join(path, "use.force")
	use_force = load_use_file(path_use_force)
	# use.mask
	path_use_mask = os.path.join(path, "use.mask")
	use_mask = load_use_file(path_use_mask)
	# use.stable.force
	path_use_stable_force = os.path.join(path, "use.stable.force")
	use_stable_force = load_use_file(path_use_stable_force)
	# use.stable.mask
	path_use_stable_mask = os.path.join(path, "use.stable.mask")
	use_stable_mask = load_use_file(path_use_stable_mask)
	#######################
	# package.use* files
	# package.use
	path_package_use = os.path.join(path, "package.use")
	package_use = load_package_use_file(path_package_use)
	# package.use.force
	path_package_use_force = os.path.join(path, "package.use.force")
	package_use_force = load_package_use_file(path_package_use_force)
	# package.use.mask
	path_package_use_mask = os.path.join(path, "package.use.mask")
	package_use_mask = load_package_use_file(path_package_use_mask)
	# package.use.stable.force
	path_package_use_stable_force = os.path.join(path, "package.use.stable.force")
	package_use_stable_force = load_package_use_file(path_package_use_stable_force)
	# package.use.stable.mask
	path_package_use_stable_mask = os.path.join(path, "package.use.stable.mask")
	package_use_stable_mask = load_package_use_file(path_package_use_stable_mask)
	#######################
	# make.defaults file
	path_make_defaults = os.path.join(path, "make.defaults")
	if os.path.exists(path_make_defaults):
		new_environment, info = load_make_defaults(path_make_defaults, environment)
		make_defaults_use_selection = info[0]
		make_defaults_use_declaration_eapi4, make_defaults_use_declaration_eapi5 = info[1], info[2]
		make_defaults_use_declaration_hidden_from_user = info[3]
		make_defaults_arch, make_defaults_accept_keywords = info[4], info[5]
		make_defaults_use_declaration_eapi4.update(use_force.get_elements())
		make_defaults_use_declaration_eapi4.update(use_mask.get_elements())
		make_defaults_use_declaration_eapi4.update(core_data.SetManipulation().add_all(
				new_environment.get('BOOTSTRAP_USE', "").split()).get_elements())
	else:
		new_environment = environment
		make_defaults_use_selection = core_data.SetManipulation()
		make_defaults_use_declaration_eapi4, make_defaults_use_declaration_eapi5 = set(), set()
		make_defaults_use_declaration_hidden_from_user = set()
		make_defaults_arch, make_defaults_accept_keywords = None, core_data.SetManipulation()
	#######################
	# packages (required patterns)
	path_package_required = os.path.join(path, "packages")
	package_required = core_data.dictSet()
	if os.path.exists(path_package_required):
		for line in parse_configuration_file(path_package_required):
			if line[0] == "*":
				package_required.add("system", core_data.pattern_create_from_atom(line[1:]))
			else:
				package_required.add("profile", core_data.pattern_create_from_atom(line))
	#######################
	# package.provided (packages implicitly provided)
	path_package_provided = os.path.join(path, "package.provided")
	if os.path.exists(path_package_provided):
		package_provided = set(parse_configuration_file(path_package_provided))
	else:
		package_provided = set()
	#######################
	# package.mask and package.unmask (packages masking)
	path_package_mask = os.path.join(path, "package.mask")
	package_mask = load_package_mask_file(path_package_mask)
	path_package_unmask = os.path.join(path, "package.unmask")
	package_unmask = load_package_mask_file(path_package_unmask)
	#######################
	# package.keywords or package.accept_keywords
	path_package_keywords = os.path.join(path, "package.keywords")
	package_keywords = load_package_keywords_file(path_package_keywords)
	path_package_accept_keywords = os.path.join(path, "package.accept_keywords")
	package_accept_keywords = load_package_keywords_file(path_package_accept_keywords)

	#######################
	# return the result
	res_use_selection_config = core_data.UseSelectionConfig(
		make_defaults_use_selection, use_force, use_mask, use_stable_force, use_stable_mask,
		package_use, package_use_force, package_use_mask, package_use_stable_force, package_use_stable_mask
	)
	res = core_data.MSPLConfig(
		make_defaults_arch,
		make_defaults_use_declaration_eapi4, make_defaults_use_declaration_eapi5, make_defaults_use_declaration_hidden_from_user,
		res_use_selection_config,
		package_required, package_provided,	package_mask, package_unmask,
		make_defaults_accept_keywords, package_keywords, package_accept_keywords
	)
	return new_environment, res


def combine_profile_layer_data(data1, data2):
	"""
	arch = data2[1] if data2[1] else data1[1]

	accept_keywords = data1[2]
	accept_keywords.update(data2[2])

	use_declaration_eapi4 = data1[3]
	use_declaration_eapi4.update(data2[3])
	use_declaration_eapi5 = data1[4]
	use_declaration_eapi5.update(data2[4])

	make_defaults_use_declaration_hidden_from_user = data1[5]
	make_defaults_use_declaration_hidden_from_user.update(data2[5])

	use = data1[6]
	core_data.use_selection_update(use, data2[6])
	use_force = data1[7]
	core_data.use_set_construction_update(use_force, data2[7])
	use_mask = data1[8]
	core_data.use_set_construction_update(use_mask, data2[8])
	use_stable_force = data1[9]
	core_data.use_set_construction_update(use_stable_force, data2[9])
	use_stable_mask = data1[10]
	core_data.use_set_construction_update(use_stable_mask, data2[10])

	package_use = data1[11]
	core_data.pattern_use_selection_update(package_use, data2[11])
	package_use_force = data1[12]
	core_data.pattern_use_set_construction_update(package_use_force, data2[12])
	package_use_mask = data1[13]
	core_data.pattern_use_set_construction_update(package_use_mask, data2[13])
	package_use_stable_force = data1[14]
	core_data.pattern_use_set_construction_update(package_use_stable_force, data2[14])
	package_use_stable_mask = data1[15]
	core_data.pattern_use_set_construction_update(package_use_stable_mask, data2[15])

	package_required = data1[16]
	portage_data.required_pattern_update(package_required, data2[16])

	package_provided = data1[17]
	package_provided.update(data2[17])

	package_mask = data1[18]
	core_data.pattern_set_construction_update(package_mask, data2[18])
	package_unmask = data1[19]
	core_data.pattern_set_construction_update(package_unmask, data2[19])

	pattern_keywords = data1[20]
	portage_data.pattern_accept_keywords_update(pattern_keywords, data2[20])

	return (
		data2[0],
		arch, accept_keywords,
		use_declaration_eapi4, use_declaration_eapi5,
		make_defaults_use_declaration_hidden_from_user,
		use, use_force, use_mask, use_stable_force, use_stable_mask,
		package_use, package_use_force, package_use_mask, package_use_stable_force, package_use_stable_mask,
		package_required, package_provided, package_mask, package_unmask, pattern_keywords
	)
	"""
	config = data1[1]
	config.update_set(data2[1])
	return data2[0], config


def load_profile(path, environment):
	path_parent = os.path.join(path, "parent")
	if os.path.exists(path_parent):
		sub_profiles = parse_configuration_file(path_parent)
		configs = []
		for sub_profile in sub_profiles:
			environment, config = load_profile(os.path.join(path, sub_profile), environment)
			configs.append(config)
		environment, config = load_profile_layer(path, environment)
		configs.append(config)
		config = configs[0]
		for data in configs[1:]:
			config.update_set(data)
		return environment, config
	else:
		return load_profile_layer(path, environment)


######################################################################
# 3. UTILITY FUNCTIONS FOR LOADING /ETC/PORTAGE/ CONFIGURATION
######################################################################

def get_user_configuration_files_in_path(path):
	if os.path.isfile(path):
		return [ path ]
	elif os.path.isdir(path):
		filename_list = filter(os.path.isfile, os.listdir(path))
		filename_list.sort()
		return [ os.path.join(path, filename) for filename in filename_list ]
	else: return []


def get_user_configuration(environment):
	# first is loaded the profile, which is then updated with local definitions
	# 1. package.use
	files_package_use = get_user_configuration_files_in_path(os.path.join(input_dir_user_configuration, "package.use"))
	pattern_use_selection = core_data.SetManipulationPattern()
	for filename in files_package_use:
		pattern_use_selection.update(load_package_use_file(filename))

	# 2. package.accept_keywords / package.keywords
	files_package_accept_keywords = get_user_configuration_files_in_path(
		os.path.join(input_dir_user_configuration, "package.accept_keywords"))
	pattern_accept_keywords = core_data.SetManipulationPattern()
	for filename in files_package_accept_keywords:
		pattern_accept_keywords.update(load_package_keywords_file(filename))

	files_package_keywords = get_user_configuration_files_in_path(
		os.path.join(input_dir_user_configuration, "package.keywords"))
	pattern_keywords = core_data.SetManipulationPattern()
	for filename in files_package_keywords:
		pattern_keywords.update(load_package_keywords_file(filename))

	# 3. package.mask / package.unmask
	files_package_mask = get_user_configuration_files_in_path(os.path.join(input_dir_user_configuration, "package.mask"))
	pattern_mask = core_data.PatternListManipulation()
	for filename in files_package_mask:
		pattern_mask.update(load_package_mask_file(filename))

	files_package_unmask = get_user_configuration_files_in_path(os.path.join(input_dir_user_configuration, "package.unmask"))
	pattern_unmask = core_data.PatternListManipulation()
	for filename in files_package_unmask:
		pattern_unmask.update(load_package_mask_file(filename))

	# 6. sets
	location_sets = os.path.join(input_dir_user_configuration, "sets")
	pattern_required = core_data.dictSet()
	if os.path.isdir(location_sets):
		for filename in os.listdir(location_sets):
			for line in parse_configuration_file(os.path.join(location_sets, filename)):
				pattern_required.add(filename, core_data.pattern_create_from_atom(line))

	# 7. local profile
	location_local_profile = os.path.join(input_dir_user_configuration, "profile")
	if os.path.isdir(location_local_profile):
		environment, config = load_profile_layer(location_local_profile, environment)
		config.update_pattern_use(pattern_use_selection)
		config.update_pattern_required(pattern_required)
		config.update_pattern_mask(pattern_mask)
		config.update_pattern_unmask(pattern_unmask)
		config.update_pattern_accept_keywords(pattern_accept_keywords)
		config.update_pattern_keywords(pattern_keywords)
		"""
		data = load_profile_layer(location_local_profile, environment)  # parent file is not supported in local profile
		environment = data[0]
		arch = data[1]
		accept_keywords = data[2]
		use_declaration_eapi4 = data[3]
		use_declaration_eapi5 = data[4]
		make_defaults_use_declaration_hidden_from_user = data[5]

		use = data[6]
		use_force = data[7]
		use_mask = data[8]
		use_stable_force = data[9]
		use_stable_mask = data[10]

		core_data.pattern_use_selection_update(pattern_use_selection, data[11])
		package_use_force = data[12]
		package_use_mask = data[13]
		package_use_stable_force = data[14]
		package_use_stable_mask = data[15]

		portage_data.required_pattern_update(pattern_required, data[16])
		package_provided = data[17]

		core_data.pattern_set_construction_update(package_mask, data[18])
		core_data.pattern_set_construction_update(package_unmask, data[19])

		portage_data.pattern_accept_keywords_update(pattern_keywords, data[20])
		"""
	else:
		use_selection_config = core_data.UseSelectionConfig(
			pattern_use=pattern_use_selection
		)
		config = core_data.MSPLConfig(
			use_selection_config=use_selection_config,
			pattern_required=pattern_required,
			pattern_mask=pattern_mask,
			pattern_unmask=pattern_unmask,
			pattern_accept_keywords=pattern_accept_keywords,
			pattern_keywords=pattern_keywords
		)
		"""
		arch = None
		accept_keywords = set()
		use_declaration_eapi4 = set()
		use_declaration_eapi5 = set()
		make_defaults_use_declaration_hidden_from_user = set()

		use = core_data.use_selection_create()
		use_force = core_data.use_selection_create()
		use_mask = core_data.use_selection_create()
		use_stable_force = core_data.use_selection_create()
		use_stable_mask = core_data.use_selection_create()

		package_use_force = core_data.pattern_use_selection_create()
		package_use_mask = core_data.pattern_use_selection_create()
		package_use_stable_force = core_data.pattern_use_selection_create()
		package_use_stable_mask = core_data.pattern_use_selection_create()

		package_provided = set()
		"""

	return environment, config
	"""(
		environment,
		arch, accept_keywords,
		use_declaration_eapi4, use_declaration_eapi5,
		make_defaults_use_declaration_hidden_from_user,
		use, use_force, use_mask, use_stable_force, use_stable_mask,
		pattern_use_selection, package_use_force, package_use_mask, package_use_stable_force, package_use_stable_mask,
		pattern_required, package_provided, pattern_mask, pattern_unmask, pattern_keywords
	)"""


######################################################################
# 4. THE SEVEN STEPS OF USE AND VISIBILITY CONSTRUCTIONS
######################################################################

# all these function have a common API: they set the data in the input config object,
#  and return the new environment

######################################################################
# 4.1. env.d

# we suppose that env-update is up-to-date
def env_d(system, environment):
	process = subprocess.Popen(["bash", "-c", "source /etc/profile.env ; /usr/bin/env"], stdout=subprocess.PIPE, env={})
	out, err = process.communicate()
	environment.update_set(environment_create_from_script_output(out))
	return environment


######################################################################
# 4.2. repo

def repo(system, environment):
	new_environment, mspl_config = load_profile_layer(input_file_profile_base, environment)
	system.mspl_config.update_set(mspl_config)
	return new_environment


######################################################################
# 4.3. pkginternal

# dealt in the translation of each individual package
def pkginternal(system, environment):
	system.close_init_phase()
	return environment


######################################################################
# 4.4. defaults

def defaults(system, environment):
	new_environment, mspl_config = load_profile(input_file_profile_selected, environment)
	system.mspl_config.update_set(mspl_config)
	return new_environment


######################################################################
# 4.5. conf

def conf(system, environment):
	new_environment, info = load_make_defaults(input_file_make_conf, environment)
	use_selection, use_declaration_eapi4, use_declaration_eapi5, use_declaration_hidden_from_user, arch, accept_keywords = info
	system.mspl_config.use_selection_config.use.update_set(use_selection)
	system.mspl_config.use_declaration_eapi4.update_set(use_declaration_eapi4)
	system.mspl_config.use_declaration_eapi5.update_set(use_declaration_eapi5)
	system.mspl_config.use_declaration_hidden_from_user.update_set(use_declaration_hidden_from_user)
	system.mspl_config.accept_keywords.update_set(accept_keywords)
	if arch:
		system.mspl_config.arch = arch
	return new_environment


######################################################################
# 4.6. pkg

def pkg(system, environment):
	new_environment, mspl_config = get_user_configuration(environment)
	system.mspl_config.update_set(mspl_config)
	return new_environment


######################################################################
# 4.7. env

# dealt with during the execution of the emerge command
# hopefully, the environment will always be at the end
def env(system, environment):
	return environment


######################################################################
# 4.8. mapping to construct the core configuration
config_construction_mapping = {
	'env.d': env_d,
	'repo': repo,
	'pkginternal': pkginternal,
	'defaults': defaults,
	'conf': conf,
	'pkg': pkg,
	'env': env
}


######################################################################
# 5. CONFIG OBJECT CONSTRUCTION
######################################################################

######################################################################
# loading the list of keywords, with their unstable prefix
def load_keyword_list():
	keyword_list = parse_configuration_file(input_file_keyword_list)
	keyword_list = keyword_list + ["~" + keyword for keyword in keyword_list]
	return keyword_list


######################################################################
# load the installed packages
#def load_installed_package_uses(package_path):
#	path_iuses = os.path.join(package_path, "IUSE")
#	if not os.path.exists(path_iuses):
#		return core_data.use_selection_create()
#	else:
#		with open(path_iuses, 'r') as f:
#			iuses = f.read().split()
#		iuses = [ iuse[1:] if iuse[0] in "+-" else iuse for iuse in iuses ]
#		with open(os.path.join(package_path, "USE"), 'r') as f:
#			uses = f.read().split()
#		nuses = [ iuse for iuse in iuses if iuse not in set(uses) ]
#		return core_data.use_selection_create(uses, nuses)


def load_installed_package_uses(package_path):
		with open(os.path.join(package_path, "USE"), 'r') as f:
			uses = f.read().split()
		return uses


def load_installed_packages():
	data = core_data.dictSet()
	for directory in os.listdir(input_dir_portage_installed):
		path = os.path.join(input_dir_portage_installed, directory)
		for package in os.listdir(path):
			package_name = directory + "/" + package
			#print("looking at " + package_name)
			complete_path = os.path.join(path, package)
			uses = load_installed_package_uses(complete_path)
			data.set(package_name, uses)
	return data


######################################################################
# load the world file
def load_world_file():
	return map(core_data.pattern_create_from_atom, parse_configuration_file(input_file_user_world))


######################################################################
# generate the egencache files for the deprecated packages
def load_installed_package(package_path, outfile):
	eapi = None
	iuses = None
	keywords = None
	slots = None
	required_use = None
	depend = None
	rdepend = None
	pdepend = None
	# parse "environment.bz2" in which all variables are declared
	variable = None
	value = None
	with bz2.BZ2File(os.path.join(package_path, "environment.bz2"), 'r') as f:
		for line in f.readlines(): # to deal with multiple-line variables
			line = line[:-1]
			if value:
				value = value + " " + line
			else:
				array = line.split("=", 1)
				if (len(array) == 2) and (array[0].startswith("declare")):
					variable = array[0]
					value = array[1]
				else:
					variable = None
					value = None
			if variable:
				if value[-1] == "\"":
					value = value[1:-1]
					#print(variable + " = " + value)
					# set the correct variables
					if variable.endswith("EAPI"):
						eapi = value
					if variable.endswith("IUSE_EFFECTIVE"):
						iuses = value
					elif (variable.endswith("IUSE")) and (iuses is None):
						iuses = value
					elif variable.endswith("KEYWORDS"):
						keywords = value
					elif variable.endswith("SLOT"):
						slots = value
					elif variable.endswith("REQUIRED_USE"):
						required_use = value
					elif variable.endswith("DEPEND"):
						depend = value
					elif variable.endswith("RDEPEND"):
						rdepend = value
					elif variable.endswith("PDEPEND"):
						pdepend = value
					# reset the data
					variable = None
					value = None
	# 3. write file
	with open(outfile, 'w') as f:
		if eapi:
			f.write("EAPI=" + eapi + "\n")
		if iuses:
			f.write("IUSE=" + iuses + "\n")
		if keywords:
			f.write("KEYWORDS=" + keywords + "\n")
		if slots:
			f.write("SLOT=" + slots + "\n")
		if required_use:
			f.write("REQUIRED_USE=" + required_use + "\n")
		if depend:
			f.write("DEPEND=" + depend + "\n")
		if rdepend:
			f.write("RDEPEND=" + rdepend + "\n")
		if pdepend:
			f.write("PDEPEND=" + pdepend + "\n")


def load_deprecated_packages(output_file_portage_deprecated):
	if not os.path.isdir(output_file_portage_deprecated):
		logging.error("The location  \"" + output_file_portage_deprecated + "\" does not exist or is not a folder")
		sys.exit(-1)
	# perform the update of the output_file_portage_deprecated folder
	# 1. remove useless files
	for directory in os.listdir(output_file_portage_deprecated):
		path = os.path.join(output_file_portage_deprecated, directory)
		for package in os.listdir(path):
			if not os.path.exists(os.path.join(os.path.join(input_dir_portage_installed, directory), package)):
				os.remove(os.path.join(path, package))
	# 2. add new files
	for directory in os.listdir(input_dir_portage_installed):
		path = os.path.join(input_dir_portage_installed, directory)
		for package_dir in os.listdir(path):
			# 2.1. check that this is indeed a deprecated package
			if os.path.exists(os.path.join(os.path.join(input_dir_portage, directory), package_dir)):
				continue
			# 2.2. create file if does not already exist
			new_path_dir = os.path.join(output_file_portage_deprecated, directory)
			new_path = os.path.join(new_path_dir, package_dir)
			if not os.path.exists(new_path):
				old_path = os.path.join(os.path.join(input_dir_portage_installed, directory), package_dir)
				if not os.path.exists(new_path_dir):
					os.makedirs(new_path_dir)
				load_installed_package(old_path, new_path)


######################################################################
# main function
def main(output_dir):
	# 1. construct the core configuration
	system = core_data.Config()
	environment = os.environ
	use_order = get_loading_order(environment)
	passed_env = False
	for stage in use_order:
		if passed_env:
			logging.error("The USE_ORDER variable does not have 'env' at the end: " + str(use_order))
			sys.exit(-1)
		print("Running Stage \"" + stage + "\"")
		passed_env = stage == "env"
		environment = config_construction_mapping[stage](system, environment)
	# 2. add the keyword list, the installed packages and the world file
	system.keyword_list = load_keyword_list()
	system.installed_packages = load_installed_packages()
	system.world = load_world_file()
	system.set_required_patterns()

	# 3. save the config
	save_filename = os.path.join(output_dir, "config.pickle")
	if os.path.isfile(save_filename):
		with open(save_filename, 'r') as f:
			old_system = cPickle.load(f)
			system.mspl_config.set_old_config(old_system.mspl_config)
	with open(save_filename, 'w') as f:
		cPickle.dump(system, f)
	# 4. generate the egencache files for the deprecated packages
	load_deprecated_packages(os.path.join(output_dir, "packages/deprecated"))








































"""



script_load_make_defaults = os.path.join(script_dir, "load_make_defaults.sh")
#bash_environment = os.environ.copy()



def update_bash_environment(filename):
	process = subprocess.Popen(["bash", script_load_make_defaults, filename], stdout=subprocess.PIPE, env=bash_environment)
	out, err = process.communicate()
	return environment_create_from_script_output(out)




def analyse_make_defaults(conf, filename):
	environment = {}
	update_bash_environment(filename)
	# update the data
	iuse_configuration = portage_data.configuration_get_iuse_configuration(conf)
	if 'USE' in environment:
		for use in environment['USE'].split():
			if use[0] == '-':
				portage_data.iuse_configuration_remove(iuse_configuration, use[1:])
			else:
				portage_data.iuse_configuration_add(iuse_configuration, use)
		environment.pop('USE') # reset the variable
	if 'IUSE' in environment:
		for use in environment['IUSE'].split():
			if use[0] == '-':
				portage_data.iuse_configuration_remove(iuse_configuration, use[1:])
			elif use[0] == "+":
				portage_data.iuse_configuration_add(iuse_configuration, use[1:])
			else:
				portage_data.iuse_configuration_update(iuse_configuration, use)
		environment.pop('IUSE') # reset the variable
	if 'ARCH' in environment: portage_data.configuration_set_arch(conf, environment['ARCH'])
	if 'ACCEPT_KEYWORDS' in environment:
		accept_keywords = portage_data.configuration_get_pattern_accept_keywords(conf)
		portage_data.pattern_accept_keywords_add(accept_keywords, portage_data.wildcardpattern, environment['ACCEPT_KEYWORDS'].split())




# MANAGE FILES: make.defaults and make.conf bash files


# MANAGE FILES: the other, simpler files
def extract_lines_from_file(f):
	res = []
	for line in f:
		line = line[:-1] # remove trailing endline
		line = line.split("#", 1)[0] # remove comment
		line.strip() # remove starting and trailing spaces
		if len(line) == 0:
			continue # skip all comments
		res.append(line)
	return res


# file: "packages", in profile configuration
def analyse_packages(conf, lines):
	package_required = portage_data.configuration_get_pattern_required(conf)
	for line in lines:
		if line[0] == "*":
			portage_data.required_pattern_add(package_required, "system", core_data.pattern_create_from_atom(line[1:]))
		else:
			portage_data.required_pattern_add(package_required, "profile", core_data.pattern_create_from_atom(line))


# file: "world" and "set/*" in user configuration
def analyse_package_set(filepath, conf, lines):
	package_required = portage_data.configuration_get_pattern_required(conf)
	package_set = os.path.basename(filepath)
	for line in lines:
		portage_data.required_pattern_add(package_required, package_set, core_data.pattern_create_from_atom(line))


# file: "package.provided" in user configuration
def analyse_package_provided(conf, lines):
	package_provided = portage_data.configuration_get_provided_package(conf)
	for package_name in lines:
		portage_data.provided_package_configuration_add(package_provided, package_name)


# file: "package.accept_keywords", in user configuration
def analyse_package_accept_keywords(conf, lines):
	pattern_accept_keywords = portage_data.configuration_get_pattern_accept_keywords(conf)
	for line in lines:
		els = line.split()
		portage_data.pattern_accept_keywords_add(pattern_accept_keywords, core_data.pattern_create_from_atom(els[0]), els[1:])


# file: "package.mask", in profile and user configuration
def analyse_package_mask(conf, lines):
	pattern_masked = portage_data.configuration_get_pattern_masked(conf)
	for line in lines:
		portage_data.pattern_masked_add(pattern_masked, core_data.pattern_create_from_atom(line))


# file: "package.unmask", in user configuration
def analyse_package_unmask(conf, lines):
	pattern_masked = portage_data.configuration_get_pattern_masked(conf)
	for line in lines:
		portage_data.pattern_masked_remove(pattern_masked, core_data.pattern_create_from_atom(line))


# file: "package.use*", in profile and user configuration
def analyse_package_use(conf, lines):
	pattern_configuration = portage_data.configuration_get_pattern_configuration(conf)
	for line in lines:
		els = line.split()
		uses = core_data.use_selection_create_from_use_list(els[1:])
		core_data.pattern_use_selection_add(pattern_configuration, core_data.pattern_create_from_atom(els[0]), uses)


# file: "package.use.mask*", in profile configuration
def analyse_package_use_mask(conf, lines):
	pattern_configuration = portage_data.configuration_get_pattern_configuration(conf)
	for line in lines:
		els = line.split()
		uses = core_data.use_selection_create_from_use_list(els[1:])
		core_data.use_selection_invert(uses)
		core_data.pattern_use_selection_add(pattern_configuration, core_data.pattern_create_from_atom(els[0]), uses)


# file "use.force", in profile configuration
def analyse_use(conf, lines):
	pattern_configuration = portage_data.configuration_get_pattern_configuration(conf)
	uses = core_data.use_selection_create_from_use_list(lines)
	core_data.pattern_use_selection_add(pattern_configuration, portage_data.wildcardpattern, uses)


# file "use.mask", in profile configuration
def analyse_use_mask(conf, lines):
	pattern_configuration = portage_data.configuration_get_pattern_configuration(conf)
	uses = core_data.use_selection_create_from_use_list(lines)
	core_data.use_selection_invert(uses)
	core_data.pattern_use_selection_add(pattern_configuration, portage_data.wildcardpattern, uses)

##

configuration_analyse_mapping = {
	"make.defaults":			analyse_make_defaults, # managed in a different manner
	"packages":					analyse_packages,
	"package.mask":				analyse_package_mask,
	#
	"package.use":				analyse_package_use,
	"package.use.force":		analyse_package_use,
	"package.use.stable.force":	analyse_package_use,
	"package.use.mask":			analyse_package_use_mask,
	"package.use.stable.mask":	analyse_package_use_mask,
	#
	"use.force":				analyse_use,
	"use.stable.force":			analyse_use,
	"use.mask":					analyse_use_mask,
	"use.stable.mask":			analyse_use_mask
}


def analyse_configuration_file(conf, parameter):
	function, filename = parameter
	if function != analyse_make_defaults:
		with open(filename, 'r') as f:
			lines = extract_lines_from_file(f)
		function(conf, lines)
	else: # make.defaults
		function(conf, filename)


def analyse_configuration_files(function_file_list):
		conf = portage_data.configuration_create()
		non_concurrent_map(lambda parameter: analyse_configuration_file(conf, parameter), function_file_list)
		return conf

######################################################################
# LOAD PROFILE FILES
######################################################################

# https://wiki.gentoo.org/wiki/Profile_(Portage)


def get_profile_files(path=os.path.realpath(input_file_profile_selected), acc=None):
	if not acc:
		acc = set([])
	res = []
	filename_list = os.listdir(path)
	filename_list.sort()
	parent_file_name = os.path.join(path, "parent")
	if os.path.isfile(parent_file_name):
		with open(parent_file_name, 'r') as f:
			data_tmp = {}
			for parent in f:
				parent = os.path.realpath(os.path.join(path, parent[:-1]))
				if not parent in acc:
					res.extend(get_profile_files(parent, acc))
	if not path in acc:
		res.extend([ (configuration_analyse_mapping[filename], os.path.join(path, filename)) for filename in filename_list if filename in configuration_analyse_mapping.keys() ])
		acc.add(path)
	return res


def load_profile():
	load = False
	last_update = None
	input_data_files = []
	# 1. check if we have a profile file
	if not os.path.exists(output_file_profile_configuration):
		load = True
	else:
		last_update = os.path.getmtime(output_file_profile_configuration)
	# 2. check if we need to update
	if not load:
		# 2.1. check if the link changed
		if last_update < os.path.getmtime(input_file_profile_selected):
			load = True
		else:
			# 2.2. check if the files changed
			input_data_files = get_profile_files()
			for function, input_data_file in input_data_files:
				if last_update < os.path.getmtime(input_data_file):
					load = True
					break
	else:
		input_data_files = get_profile_files()
	# 3. recreate the profile files
	if load:
		# 3.1. load the profile
		conf = analyse_configuration_files(input_data_files)
		# 3.2. write the files
		with open(output_file_profile_configuration, 'w') as f:
			json.dump(portage_data.configuration_to_save_format(conf), f)


######################################################################
# LOAD USER FILES
######################################################################

# https://wiki.gentoo.org/wiki//etc/portage




def load_user_configuration():
	load = False
	last_update = None
	# 1. check if we have a profile file
	if not os.path.exists(output_file_user_configuration):
		load = True
	else:
		last_update = os.path.getmtime(output_file_user_configuration)
	# 2. check if we need to update
	if not load:
		input_data_files = get_user_configuration_files()
		for func, filename in input_data_files :
			if last_update < os.path.getmtime(filename):
				load = True
				break;
	else:
		input_data_files = get_user_configuration_files()
	# 3. recreate the user configuration file
	if load:
		# 3.1. load the user configuration
		conf = analyse_configuration_files(input_data_files)
		# 3.2. write the files
		with open(output_file_user_configuration, 'w') as f:
			json.dump(portage_data.configuration_to_save_format(conf), f)


######################################################################
# LOAD PORTAGE PACKAGES
######################################################################

# this works differently from the other update functions, as the diff will be performed on the host
# here we simply update the packages/deprecated folder


######################################################################
# LOAD INSTALLED PACKAGE CONFIGURATION
######################################################################


def load_installed_package_uses(package_path):
	path_iuses = os.path.join(package_path, "IUSE")
	if not os.path.exists(path_iuses):
		return core_data.use_selection_create()
	else:
		with open(path_iuses, 'r') as f:
			iuses = f.read().split()
		iuses = [ iuse[1:] if iuse[0] in "+-" else iuse for iuse in iuses ]
		with open(os.path.join(package_path, "USE"), 'r') as f:
			uses = f.read().split()
		nuses = [ iuse for iuse in iuses if iuse not in set(uses) ]
		return core_data.use_selection_create(uses, nuses)


def load_installed_packages():
	data = core_data.package_installed_create()
	last_update = None
	# 1. check if we have a profile file and load it
	if os.path.exists(output_file_installed_packages):
		last_update = os.path.getmtime(output_file_installed_packages)
		with open(output_file_installed_packages, 'r') as f:
			data = core_data.package_installed_from_save_format(json.load(f))
	# 2. update the data
	to_keep = []
	for directory in os.listdir(input_dir_portage_installed):
		path = os.path.join(input_dir_portage_installed, directory)
		for package in os.listdir(path):
			package_name = directory + "/" + package
			#print("looking at " + package_name)
			to_keep.append(package_name)
			complete_path = os.path.join(path, package)
			if (package_name not in data.keys()) or (last_update < os.path.getmtime(complete_path)):
				uses = load_installed_package_uses(complete_path)
				core_data.package_installed_set(data, package_name, uses)
	data = { k: data[k] for k in to_keep }
	# 3. write the file
	with open(output_file_installed_packages, 'w') as f:
		json.dump(core_data.package_installed_to_save_format(data), f)


######################################################################
# LOAD KEYWORD LIST
######################################################################

def analyse_keyword_list_file(input_file_keyword_list):
	with open(input_file_keyword_list, 'r') as f:
		keyword_list = extract_lines_from_file(f)
	keyword_list = keyword_list + [ "~" + keyword for keyword in keyword_list ]
	return keyword_list


def load_keyword_list():
	load = False
	last_update = None
	# 1. check if we have a profile file
	if not os.path.exists(output_file_keyword_list):
		load = True
	else:
		last_update = os.path.getmtime(output_file_keyword_list)
	# 2. check if we need to update
	if not load:
		load = last_update < os.path.getmtime(input_file_keyword_list)

	# 3. recreate the profile files
	if load:
		# 3.1. load the profile
		conf = analyse_keyword_list_file(input_file_keyword_list)
		# 3.2. write the files
		with open(output_file_keyword_list, 'w') as f:
			json.dump(conf, f)


######################################################################
# MAIN
######################################################################

def setup_output_files(given_output_dir):
	global output_dir
	global output_file_portage
	global output_file_portage_deprecated
	global output_file_profile_configuration
	global output_file_user_configuration
	global output_file_installed_packages
	global output_file_keyword_list
	output_dir = os.path.realpath(given_output_dir)
	output_file_portage = os.path.join(output_dir, "packages/portage-tree")
	output_file_portage_deprecated = os.path.join(output_dir, "packages/deprecated")
	output_file_profile_configuration = os.path.join(output_dir, "profile_configuration.json")
	output_file_user_configuration = os.path.join(output_dir, "user_configuration.json")
	output_file_installed_packages = os.path.join(output_dir, "installed_packages.json")
	output_file_keyword_list = os.path.join(output_dir, "keywords.json")

def main(given_output_dir):
	# 1. setup the global variables
	setup_output_files(given_output_dir)
	# 2. check if the output directory exists
	if not os.path.exists(output_dir):
		logging.error("The output directory \"" + output_dir + "\" does not exit")
		sys.exit(-1)
	elif not os.path.isdir(output_dir):
		logging.error("The output directory \"" + output_dir + "\" already exists and is not a directory")
		sys.exit(-1)
	# 3. create the initial bash environment
	update_bash_environment()
	# 4. load portage
	load_deprecated_packages()
	# 5. load the profile
	load_profile()
	# 6. load the user configuration
	load_user_configuration()
	# 7. load the current set of installed packages with their configuration
	load_installed_packages()
	# 8. load the current keyword list
	load_keyword_list()

"""

if __name__ == "__main__":
	main(sys.argv[1])
