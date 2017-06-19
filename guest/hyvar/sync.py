#!/usr/bin/python

import sys
import time
import os
import os.path
import logging
import subprocess
import multiprocessing

#def get_patterns(string):
#	return re.findall(">?<?=?[a-zA-Z0-9._@][a-zA-Z0-9._\-+@/:]*", string)

######################################################################
### CONFIGURATION
######################################################################

# input

input_dir_portage = os.path.realpath("/usr/portage/metadata/md5-cache/")
input_dir_portage_deprecated = os.path.realpath("/var/lib/pkg/")

input_file_profile = "/etc/portage/make.profile"

input_dir_user_configuration = os.path.realpath("/etc/portage/")
input_file_user_world = os.path.realpath("/var/lib/portage/world")

# output

output_dir = None

output_file_portage = None
output_file_portage_deprecated = None

output_file_profile_configuration = None

output_file_user_configuration = None

# concurrency

concurrent_map = map # the different load processes must be done in sequence

######################################################################
### UTILITY FUNCTIONS AND CLASSES
######################################################################


# PACKAGE REQUIREMENT
# in portage, it is possible to statically (in files) request of package installation
# this is simply a list of real package groups with two operations: add and remove
# portage distinguish different sets of package requirement (user can specify some in the "/etc/portage/sets" folder)
def packages_required_create():
	return {}

def packages_required_update_simple(packages_required, package_set, package):
	to_update = packages_required.get(package_set)
	if not to_update:
		to_update = set([])
		packages_required[package_set] = to_update
	if package[0] == '-':
		to_update.discard(package[1:])
	else:
		to_update.add(keyword)


# PACKAGE MASKING
# in portage, one can define sequence of masking and unmasking requests
# as these requests use package patterns, we cannot apply them without knowing which packages are present in the portage tree
# Hence, here we simply store them in a list
def packages_mask_create():
	return []

def packages_mask_update_simple(packages_mask, pattern, sign):
	packages_mask.append( { 'sign': sign, 'pattern': pattern } )


# USE AND PACKAGE USE
# similarily to package masking, it is possible in portage to define sequence of partial configuration for packages
# these partial configuration uses package patterns, and so we cannot apply them directly
# we thus store them in a list
def configuration_use_create():
	return []

def configuration_use_update_simple(configuration_use, pattern, uses):
	configuration_use.append( { 'pattern': pattern, 'uses': uses } )


def use_invert(use):
	if use[0] == "-": return use[1:]
	else: return "-" + use

def use_list_invert(uses):
	return map(use_invert, uses)


# ACCEPT_KEYWORDS
# similarily to use flag partial configuration, we have again a sequence of declaration for package patterns
# however this is simply than for use flags, as there are no declaration of opposites
def accept_keywords_create():
	return []

def accept_keywords_update_simple(accept_keywords, pattern, keywords):
	accept_keywords.append( { 'pattern': pattern, 'keywords': keywords } )

# full configuration container
class Configuration(object):
	def __init__(self):
		self.arches = set([]) # list of valid architectures for the current hardware
		self.iuses = set([])  # list of implicitly declared use flags
		self.package_provided = set([]) # list of packages that is assumed to be correctly installed
		self.package_required = packages_required_create()
		self.package_mask = packages_mask_create()
		self.package_configuration_use = {}
		self.package_accept_keywords = accept_keywords_create()

	def update_arch_list(self, arches):
		self.arches.update(arches)

	def update_iuse_list(self, iuses):
		self.iuses.update(iuses)

	def update_package_provided(self, packages):
		self.package_provided.update(packages)

	def update_package_required(self, package_set, package):
		packages_required_update_simple(self.package_required, package_set, package)

	def update_package_mask(self, pattern, sign):
		packages_mask_update_simple(self.package_mask, pattern, sign)

	def update_package_configuration_use(self, pattern, uses):
		configuration_use_update_simple(self.package_configuration_use, pattern, uses)

	def update_packages_accept_keywords(self, pattern, keywords):
		accept_keywords_update_simple(self.package_accept_keywords, pattern, keywords)

	def to_dict(self):
		return {
			'arches': list(self.arches),
			'iuses': list(self.iuses),
			'package_required': self.package_required,
			'package_mask': self.package_mask,
			'package_configuration_use': self.package_configuration_use,
			'package_accept_keywords': self.package_accept_keywords
		}

	def __repr__(self):
		return repr(self.to_dict())

	def __str__(self):
		return str(self.to_dict())


######################################################################
### UTILITY FUNCTIONS FOR LOADING A CONFIGURATION
######################################################################

# MANAGE FILES: make.defaults and make.conf bash files
bash_environment = {}
def update_bash_environment(filename = ""):
	global bash_environment
	process = subprocess.Popen(["bash", "./load_make_defaults.sh", filename ], stdout=subprocess.PIPE, env=bash_environment)
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

def analyse_make_defaults(data, filename):
	update_bash_environment(filename)
	# update the data
	if 'USE' in bash_environment: data.update_package_configuration_use("*/*", bash_environment['USE'].split())
	if 'IUSE' in bash_environment: data.update_iuse_list(bash_environment['IUSE'].split())
	if 'ARCH' in bash_environment: data.update_arch_list(bash_environment['ARCH'].split())
	if 'ACCEPT_KEYWORDS' in bash_environment: data.update_arch_list(bash_environment['ACCEPT_KEYWORDS'].split())



# MANAGE FILES: the other, simpler files
def extact_lines_from_file(f):
	res = []
	for line in f:
		line = line[:-1] # remove trailing endline
		line = line.split("#", 1)[0] # remove comment
		line.strip() # remove starting and trailing spaces
		if len(line) == 0:
			continue # skip all comments
		res.append(line))
	return res

# file: "packages", in profile configuration
def analyse_packages(data, lines):
	for line in lines:
		if line[0] = "*":
			data.update_package_required("system", line[1:])
		else:
			data.update_package_required("profile", line)

# file: "world" and "set/*" in user configuration
def analyse_package_set(filepath, data, lines):
	package_set = os.path.basename(filepath)
	for line in lines:
		data.update_package_required(package_set, line)

# file: "package.provided" in user configuration
def analyse_package_provided(data, lines):
	data.update_package_provided(lines)

# file: "package.accept_keywords", in user configuration
def analyse_package_accept_keywords(data, lines):
	for line in lines:
		els = line.split()
		data.update_packages_accept_keywords(els[0], els[1:])	

# file: "package.mask", in profile and user configuration
def analyse_package_mask(data, lines):
	for line in lines:
		data.update_package_mask(line, "mask")

# file: "package.unmask", in user configuration
def analyse_package_unmask(data, lines):
	for line in lines:
		data.update_package_mask(line, "unmask")

# file: "package.use*", in profile and user configuration
def analyse_package_use(data, lines):
	for line in lines:
		els = line.split()
		data.configuration_use_update_simple(els[0], els[1:])

# file: "package.use.mask*", in profile configuration
def analyse_package_use_mask(data, lines):
	for line in lines:
		els = line.split()
		data.configuration_use_update_simple(els[0], use_list_invert(els[1:]))

# file "use.force", in profile configuration
def analyse_use(data, lines):
	data.configuration_use_update_simple("*/*", lines)

# file "use.mask", in profile configuration
def analyse_use_mask(data, lines):
	data.configuration_use_update_simple("*/*", use_invert(line))




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

def analyse_configuration_file(data, parameter):
	function, filename = parameter
	if function != analyse_make_defaults:
		with open(filename, 'r') as f:
			lines = extact_lines_from_file(f)
		function(data, lines)
	else: # make.defaults
		function(data,filename)


def analyse_configuration_files(function_file_list):
		data = Configuration()
		non_concurrent_map(lambda parameter: analyse_configuration_file(data, parameter), input_data_files)
		return data

######################################################################
### LOAD PROFILE
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
	load  = False
	last_update = None
	input_data_files = []
	# 1. check if we have a profile file
	if not os.path.exits(output_file_profile_configuration):
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
		data = analyse_configuration_files(input_data_files)
		# 3.2. write the files
		with open(output_file_profile_configuration, 'w') as f:
			json.dump(data.to_dict(), f)

######################################################################
### LOAD USER-DEFINED FILES
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
		res.append(None, file_make_conf)
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
	files_package_set.add(input_file_user_world)
	res.extend([ (lambda data, lines: analyse_package_set(filename, data, lines), filename) for filename in files_package_set])
	return res

def load_user_configuration():
	load  = False
	last_update = None
	input_data_files = []
	# 1. check if we have a profile file
	if not os.path.exits(output_file_user_configuration):
		load = True
	else:
		last_update = os.path.getmtime(output_file_user_configuration)
	# 2. check if we need to update
	if not load:
		input_data_files = get_user_configuration_files()
		for filename in [ filename in input_data_files.values() ]:
			if last_update < os.path.getmtime(filename):
				load = True
				break;
	else:
		input_data_files = get_user_configuration_files()
	# 3. recreate the user configuration file
	if load:
		# 3.1. load the user configuration
		data = analyse_configuration_files(input_data_files)
		# 3.2. write the files
		with open(output_file_user_configuration, 'w') as f:
			json.dump(data.to_dict(), f)


######################################################################
### LOAD PORTAGE
######################################################################

# this works differently from the other update functions, as the diff will be performed on the host
# here we simply update the packages/deprecated folder
def load_portage():
	if not os.path.isdir(output_file_portage_deprecated):
		logging.error("The location  \"" + output_file_portage_deprecated + "\" does not exist or is not a folder")
		sys.exit(-1)
	# perform the update of the output_file_portage_deprecated folder
	# 1. remove useless files
	for directory in os.listdir(output_file_portage_deprecated):
		path = os.path.join(output_file_portage_deprecated, directory)
		for package in os.listdir(path):
			if not os.path.exists(os.path.join(os.path.join(input_dir_portage_deprecated,directory),package)):
				os.remove(os.path.join(path, package))
				els = package.split("-")
				if els[-1][0] == "r":
					package_group = "-".join(els[:-2])
				else:
					package_group = "-".join(els[:-1])
			elif os.path.exists(os.path.exists(os.path.join(os.path.join(input_dir_portage,directory),package_group)),package + ".ebuild"):
				os.remove(os.path.join(path, package))
	# 2. add new files
	for directory in os.listdir(input_dir_portage_deprecated):
		path = os.path.join(output_file_portage_deprecated, directory)
		for package_dir in os.listdir(path):
			new_path = os.path.join(os.path.join(output_file_portage_deprecated,directory),package_dir)
			if not os.path.exists(new_path):
				old_path = os.path.join(os.path.join(os.path.join(input_dir_portage_deprecated,directory),package_dir),package_dir + ".ebuild")
				subprocess.call("load_ebuild.sh", old_path, new_path)



######################################################################
### MAIN
######################################################################

def setup_output_files(given_output_dir):
	global output_dir
	global output_file_portage
	global output_file_portage_deprecated
	global output_file_profile_configuration
	global output_file_user_configuration
	output_dir = os.path.realpath(given_output_dir)
	output_file_portage = os.path.join(output_dir, "packages/portage-tree")
	output_file_portage_deprecated = os.path.join(output_dir, "packages/deprecated")
	output_file_profile_configuration = os.path.join(output_dir, "profile_configuration.json")
	output_file_user_configuration = os.path.join(output_dir, "user_configuration.json")


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
	load_profile(concurrent_map)
	# 6. load the user configuration
	load_user_configuration()






if __name__ == "__main__":
	main(sys.argv[1])