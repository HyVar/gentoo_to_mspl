#!/usr/bin/python

import sys
import os
import os.path
import logging
import subprocess
import bz2
import json

import core_data
import portage_data


######################################################################
# FILE PATHS
######################################################################

# input

input_dir_portage = os.path.realpath("/usr/portage/metadata/md5-cache/")
input_dir_portage_installed = os.path.realpath("/var/db/pkg/")

input_file_profile = "/etc/portage/make.profile"

input_dir_user_configuration = os.path.realpath("/etc/portage/")
input_file_user_world = os.path.realpath("/var/lib/portage/world")

input_file_keyword_list = os.path.realpath("/usr/portage/profiles/arch.list")

script_dir = os.path.dirname(os.path.abspath(__file__))

# output

output_dir = None

output_file_portage = None
output_file_portage_deprecated = None

output_file_profile_configuration = None

output_file_user_configuration = None

output_file_installed_packages = None

output_file_keyword_list = None

# concurrency

non_concurrent_map = map # the different load processes must be done in sequence


######################################################################
# UTILITY FUNCTIONS FOR LOADING A CONFIGURATION
######################################################################

def parse_use(use):
	return (use[1:], "-") if use[0] == "-" else (use, "+")


def parse_use_list(uses):
	res = core_data.use_configuration_create()
	for use in uses:
		use, sign = parse_use(use)

# MANAGE FILES: make.defaults and make.conf bash files
script_load_make_defaults = os.path.join(script_dir, "load_make_defaults.sh")
bash_environment = {}


def update_bash_environment(filename = ""):
	global bash_environment
	process = subprocess.Popen(["bash", script_load_make_defaults, filename ], stdout=subprocess.PIPE, env=bash_environment)
	out, err = process.communicate()
	# reset the environment
	bash_environment = {}
	# variables to deal with shell values being on severa lines
	variable = None
	value = None
	for line in out.splitlines(): # to deal with multiple-line variables
		if value:
			value = value + line
		else:
			array = line.split("=", 1)
			variable = array[0]
			value=array[1]
		if (len(value) == 0) or ((len(value) > 0) and ((value[0] != "'") or (value[-1] == "'"))):
			if (len(value) > 0) and (value[0] == "'"):
				value = value[1:-1]
			#print("variable \"" + variable + "\" = \"" + value + "\"")
			bash_environment[variable] = value
			value = None


def analyse_make_defaults(conf, filename):
	update_bash_environment(filename)
	# update the data
	iuse_configuration = portage_data.configuration_get_iuse_configuration(conf)
	if 'USE' in bash_environment:
		for use in bash_environment['USE'].split():
			if use[0] == '-':
				portage_data.iuse_configuration_remove(iuse_configuration, use[1:])
			else:
				portage_data.iuse_configuration_add(iuse_configuration, use)
		bash_environment.pop('USE') # reset the variable
	if 'IUSE' in bash_environment:
		for use in bash_environment['IUSE'].split():
			if use[0] == '-':
				portage_data.iuse_configuration_remove(iuse_configuration, use[1:])
			elif use[0] == "+":
				portage_data.iuse_configuration_add(iuse_configuration, use[1:])
			else:
				portage_data.iuse_configuration_update(iuse_configuration, use)
		bash_environment.pop('IUSE') # reset the variable
	if 'ARCH' in bash_environment: portage_data.configuration_set_arch(conf, bash_environment['ARCH'])
	if 'ACCEPT_KEYWORDS' in bash_environment:
		accept_keywords = portage_data.configuration_get_pattern_accept_keywords(conf)
		for keyword in bash_environment['ACCEPT_KEYWORDS'].split():
			portage_data.pattern_accept_keywords_add(accept_keywords, portage_data.wildcardpattern, keyword)


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
			portage_data.required_pattern_add(package_required, "system", line[1:])
		else:
			portage_data.required_pattern_add(package_required, "profile", line)


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
		uses = core_data.use_configuration_create_from_uses_list(els[1:])
		portage_data.pattern_configuration_add(pattern_configuration, core_data.pattern_create_from_atom(els[0]), uses)


# file: "package.use.mask*", in profile configuration
def analyse_package_use_mask(conf, lines):
	pattern_configuration = portage_data.configuration_get_pattern_configuration(conf)
	for line in lines:
		els = line.split()
		uses = core_data.use_configuration_create_from_uses_list(els[1:])
		core_data.use_configuration_invert(uses)
		portage_data.pattern_configuration_add(pattern_configuration, core_data.pattern_create_from_atom(els[0]), uses)


# file "use.force", in profile configuration
def analyse_use(conf, lines):
	pattern_configuration = portage_data.configuration_get_pattern_configuration(conf)
	uses = core_data.use_configuration_create_from_uses_list(lines)
	portage_data.pattern_configuration_add(pattern_configuration, portage_data.wildcardpattern, uses)


# file "use.mask", in profile configuration
def analyse_use_mask(conf, lines):
	pattern_configuration = portage_data.configuration_get_pattern_configuration(conf)
	uses = core_data.use_configuration_create_from_uses_list(lines)
	core_data.use_configuration_invert(uses)
	portage_data.pattern_configuration_add(pattern_configuration, portage_data.wildcardpattern, uses)

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


def get_profile_files(path=os.path.realpath(input_file_profile), acc=None):
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
		if last_update < os.path.getmtime(input_file_profile):
			load = True
		else:
			# 2.2. check if the files changed
			input_data_files = get_profile_files()
			for function, input_data_file in input_data_files:
				if last_update < os.path.getmtime(input_data_file):
					load = True
					break;
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


def get_user_configuration_files_in_path(path):
	if os.path.isfile(path):
		return [ path ]
	elif os.path.isdir(path):
		filename_list = os.listdir(path)
		filename_list.sort()
		return [ os.path.join(path, filename) for filename in filename_list ]
	else: return []


def get_user_configuration_files():
	res = []
	# 1. make.conf
	file_make_conf = os.path.join(input_dir_user_configuration, "make.conf")
	if os.path.isfile(file_make_conf):
		res.append( (analyse_make_defaults, file_make_conf) )
	# 2. package.accept_keywords / package.keywords 
	files_package_accept_keywords = get_user_configuration_files_in_path(os.path.join(input_dir_user_configuration, "package.accept_keywords"))
	files_package_accept_keywords.extend(get_user_configuration_files_in_path(os.path.join(input_dir_user_configuration, "package.keywords")))
	res.extend([ (analyse_package_accept_keywords, filename) for filename in files_package_accept_keywords ])
	# 3. package.mask
	files_package_mask = get_user_configuration_files_in_path(os.path.join(input_dir_user_configuration, "package.mask"))
	res.extend([ (analyse_package_mask, filename) for filename in files_package_mask ]) 
	# 4. package.unmask
	files_package_unmask = get_user_configuration_files_in_path(os.path.join(input_dir_user_configuration, "package.unmask"))
	res.extend([ (analyse_package_unmask, filename) for filename in files_package_unmask ]) 
	# 5. package.use
	files_package_use = get_user_configuration_files_in_path(os.path.join(input_dir_user_configuration, "package.use"))
	res.extend([ (analyse_package_use, filename) for filename in files_package_use ]) 
	# 6. use.mask
	files_use_mask = get_user_configuration_files_in_path(os.path.join(input_dir_user_configuration, "profile/use.mask"))
	res.extend([ (analyse_use_mask, filename) for filename in files_use_mask ]) 
	# 7. package.use.mask
	files_package_use_mask = get_user_configuration_files_in_path(os.path.join(input_dir_user_configuration, "profile/package.use.mask"))
	res.extend([ (analyse_package_use_mask, filename) for filename in files_package_use_mask ]) 
	# 8. package.provided
	files_package_provided = get_user_configuration_files_in_path(os.path.join(input_dir_user_configuration, "profile/package.provided"))
	res.extend([ (analyse_package_provided, filename) for filename in files_package_provided ]) 
	# 9. the world and set/* file
	files_package_set = get_user_configuration_files_in_path(os.path.join(input_dir_user_configuration, "sets"))
	files_package_set.append(input_file_user_world)
	res.extend([ (lambda data, lines: analyse_package_set(filename, data, lines), filename) for filename in files_package_set])
	return res


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

def get_package_group(package_name):
	els = package_name.split("-")
	if els[-1][0] == "r":
		return "-".join(els[:-2])
	else:
		return "-".join(els[:-1])


def load_installed_package(package_path, outfile):
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
					value=array[1]
				else:
					variable = None
					value = None
			if variable:
				if value[-1] == "\"":
					value = value[1:-1]
					#print(variable + " = " + value)
					# set the correct variables
					if variable.endswith("IUSE_EFFECTIVE"):
						iuses = value
					elif (variable.endswith("IUSE")) and (iuses is None):
						iuses = value
					elif variable.endswith("KEYWORDS"):
						keywords = value
					elif variable.endswith("SLOT"):
						slot = value
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
		if iuses:
			f.write("IUSE=" + iuses + "\n")
		if keywords:
			f.write("KEYWORDS=" + keywords + "\n")
		if slots:
			f.write("SLOT=" + slot + "\n")
		if required_use:
			f.write("DEPEND=" + required_use + "\n")
		if depend:
			f.write("DEPEND=" + depend + "\n")
		if rdepend:
			f.write("RDEPEND=" + rdepend + "\n")
		if pdepend:
			f.write("PDEPEND=" + pdepend + "\n")


def load_portage():
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
# LOAD INSTALLED PACKAGE CONFIGURATION
######################################################################


def load_installed_package_uses(package_path):
	path_iuses = os.path.join(package_path, "IUSE")
	if not os.path.exists(path_iuses):
		return core_data.use_configuration_create()
	else:
		with open(path_iuses, 'r') as f:
			iuses = f.read().split()
		iuses = [ iuse[1:] if iuse[0] in "+-" else iuse for iuse in iuses ]
		with open(os.path.join(package_path, "USE"), 'r') as f:
			uses = f.read().split()
		nuses = [ iuse for iuse in iuses if iuse not in set(uses) ]
		return core_data.use_configuration_create(uses, nuses)


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
	load_portage()
	# 5. load the profile
	load_profile()
	# 6. load the user configuration
	load_user_configuration()
	# 7. load the current set of installed packages with their configuration
	load_installed_packages()
	# 8. load the current keyword list
	load_keyword_list()


if __name__ == "__main__":
	main(sys.argv[1])
