#!/usr/bin/python

import sys
import time
import os
import os.path
import logging

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

output_dir = os.path.realpath("./gen")

output_file_portage = os.path.join(output_dir, "portage.tar.bz2")
output_file_portage_configuration = os.path.join(output_dir, "portage_configuration.json")

output_file_profile_configuration = os.path.join(output_dir, "profile_configuration.json")

output_file_user_configuration = os.path.join(output_dir, "user_configuration.json")


######################################################################
### UTILITY FUNCTIONS AND CLASSES
######################################################################

def get_patterns(string):
	return re.findall(">?<?=?[a-zA-Z0-9._@][a-zA-Z0-9._\-+@/:]*", string)


# use and use_map
def configuration_use_create():
	return { 'positive': set([]), 'negative': set([]) }

def configuration_use_create_from_list(uselist):
	res = configuration_use_create()
	for use in uselist:
		configuration_use_update_simple(res, use)
	return res

def configuration_use_update_simple(uses, use):
	if use[0] == '-':
		uses['negative'].add(use[1:])
	elif use[0] == '+':
		uses['positive'].add(use[1:])
	else:
		uses['positive'].add(use)

def configuration_use_update(uses1, uses2):
   	uses1['positive'].difference_update(uses2['negative'])
   	uses1['negative'].difference_update(uses2['positive'])
   	uses1['positive'].update(uses2['positive'])
   	uses1['negative'].update(uses2['negative'])

def use_invert(use):
	if use[0] == "-":
		return use[1:]
	elif use[1] == "+":
		use[1] = "-"
		return use
	else:
		return "-" + use

def configuration_use_invert(uses):
	return 	{ 'positive': uses['negative'], 'negative': uses['positive'] }

def configuration_use_clean(uses):
	return { 'positive': list(uses['positive']), 'negative': list(uses['negative']) }


class Configuration(object):
	def __init__(self):
		self.arches = set([])
		self.iuses = set([])
		self.configuration_use = configuration_use_create()
		self.packages = { 'system': set([]), 'profile': set([]), 'mask': set([]) , 'provided': set([]) }
		self.packages_configuration_use = {}
		self.package_keywords = {}

	def update_arch_list(self, arches):
		self.arches.update(arches)

	def update_iuse_list(self, iuses):
		self.iuses.update(iuses)

	def update_configuration_use(self, uses):
		configuration_use_update(self.configuration_use, uses)

	def update_use_simple(self, use):
		configuration_use_update_simple(self.configuration_use, use)

	def update_package(self, kind, package):
		self.packages[kind].add(package)
		if kind = "mask":
			for k,v in self.packages.iteritems():
				if k != "mask":
					v.discard(package)
		else:
			self.packages['mask'].discard(package)

	def update_package_use(self, package_uses):
		package, uses = package_uses
		if package in self.packages_configuration_use:
			configuration_use_update(self.packages_configuration_use[package], uses)
		else:
			self.packages_configuration_use[package] = uses

	def add_egencache_data(self, d):
		package, package_uses = d
		if package in self.packages_configuration_use:
			configuration_use_update(self.packages_configuration_use[package], package_uses)
		else:
			self.packages_configuration_use[package] = package_uses


	def to_dict(self):
		packages = { k: list(v) for k,v in self.packages.iteritems() }
		package_uses = { package: configuration_use_clean(configuration_use) for package, configuration_use in self.package_configuration_use.iteritems() }
		return { 'arches': list(self.arches), 'iuses': list(self.iuses), 'configuration_use': configuration_use_clean(self.configuration_use), 'packages': packages, 'packages_configuration_use': package_uses }

	def __repr__(self):
		return repr(self.to_dict())

	def __str__(self):
		return str(self.to_dict())


######################################################################
### UTILITY FUNCTIONS FOR LOADING A CONFIGURATION
######################################################################


bash_environment = {}
def analyse_make_defaults(data, filename):
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
	# update the data
	if 'USE' in bash_environment: data.update_configuration_use(configuration_use_create_from_list(bash_environment['USE'].split()))
	if 'IUSE' in bash_environment: data.update_iuse_list(configuration_use_create_from_list(bash_environment['IUSE'].split()))
	if 'ARCH' in bash_environment: datta.update_arch_list(bash_environment['ARCH'].split())


# manage the other, simpler files
def process_file(f, function):
	res = []
	for line in f:
		line = line[:-1] # remove trailing endline
		line.strip() # remove starting and trailing spaces
		if (len(line) == 0) or (line[0] == "#"):
			continue # skip all comments
		res.append(function(line))
	return res

def __analyse_packages1(data, line):
	ProfileData.update_package(data, "system", line)
def __analyse_packages2(data, line):
	ProfileData.update_package(data, "profile", line)
def __analyse_packages3(data, line):
	ProfileData.update_package(data, "mask", line)
def __analyse_packages4(data, line):
	ProfileData.update_package(data, "provided", line)
def analyse_packages(line):
	if line[0] == "*":
		return (__analyse_packages1, line[1:])
	else:
		return (__analyse_packages2, line)
def analyse_package_mask(line):
	return (__analyse_packages3, line)

def analyse_package_use(line):
	tmp = split_string(line)
	return (ProfileData.update_package_use, (tmp[0], configuration_use_create_from_list(tmp[1:])))

def analyse_package_use_mask(line):
	tmp = split_string(line)
	return (ProfileData.update_package_use, (tmp[0], use_invert_map(configuration_use_create_from_list(tmp[1:]))))

def analyse_use(line): # one use per line
	return (ProfileData.update_use_simple, line)

def analyse_use_mask(line): # one use per line
	return (ProfileData.update_use_simple, use_invert(line))


configuration_analyse_mapping = {
	"make.defaults":			None, # managed in a different manner
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




######################################################################
### LOAD PROFILE
######################################################################

def get_profile_files(path=os.path.realpath(input_file_profile), acc=None):
	if not acc:
		acc = set([])
	res = []
	filename_list = os.listdir(path)
	parent_file_name = os.path.join(path, "parent")
	if os.path.isfile(parent_file_name):
		with open(parent_file_name, 'r') as f:
			data_tmp = {}
			for parent in f:
				parent = os.path.realpath(os.path.join(path, parent[:-1]))
				if not parent in acc:
					res.extend(get_profile_files(parent, acc))
	if not path in acc:
		res.extend([ os.path.join(path, filename) for filename in filename_list if filename in __analyse_mapping.keys() ])
		acc.add(path)
	return res

def analyse_profile_file(path):
	filename = os.path.basename(path)
	try:
		function = configuration_analyse_mapping[filename]
		if function:
			with open(filename, 'r') as f:
				return process_file(f, function)
		else: # make.defaults 
			return [(analyse_make_defaults, filename)] # make.defaults needs to be handled in sequence, to correctly deal with the environment
	except KeyError:
		logging.error("No function to load file: \"" + path + "\"")
		sys.exit(-1)	

def load_profile(concurrent_map):
	load  = False
	last_update = time.gmtime(0)
	input_data_files = []
	# 1. check if we have a profile file
	if not os.path.exits(output_file_profile_iuse):
		load = True
	else:
		last_update = os.path.getmtime(output_file_profile_iuse)
	# 2. check if we need to update
	if not load:
		# 2.1. check if the link changed
		if last_update < os.path.getmtime(input_file_profile):
			load = True
		else:
			# 2.2. check if the files changed
			input_data_files = get_profile_files()
			for input_data_file in input_data_files:
				if last_update < os.path.getmtime(input_data_file):
					load = True
					break;
	else:
		input_data_files = get_profile_files()
	# 3. recreate the profile files
	if load:
		# 3.1. load the profile
		data = Configuration()
		profile_data_list = concurrent_map(analyse_profile_file, input_data_files)
		for function, profile_data in [ function, profile_data for inner_list in profile_data_list for function, profile_data in inner_list ]:
		function(data, profile_data)
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
		return [ os.path.join(path, filename) for filename in os.listdir(path) ]
	else: return []

def get_user_configuration_files():
	res = {}
	# 1. make.conf
	res['make.conf'] = os.path.join(input_dir_user_configuration, "make.conf")
	# 2. package.accept_keywords / package.keywords 
	res['package.accept_keywords'] = get_user_configuration_files_in_path(os.path.join(input_dir_user_configuration, "package.accept_keywords"))
	res['package.accept_keywords'].extend(get_user_configuration_files_in_path(os.path.join(input_dir_user_configuration, "package.keywords")))
	# 3. package.mask
	res['package.mask'] = get_user_configuration_files_in_path(os.path.join(input_dir_user_configuration, "package.mask"))
	# 4. package.mask
	res['package.unmask'] = get_user_configuration_files_in_path(os.path.join(input_dir_user_configuration, "package.unmask"))
	# 5. package.use
	res['package.use'] = get_user_configuration_files_in_path(os.path.join(input_dir_user_configuration, "package.use"))
	# 6. use.mask
	res['use.mask'] = get_user_configuration_files_in_path(os.path.join(input_dir_user_configuration, "profile/use.mask"))
	# 7. package.use.mask
	res['package.use.mask'] = get_user_configuration_files_in_path(os.path.join(input_dir_user_configuration, "profile/package.use.mask"))
	# 8. package.provided
	res['package.provided'] = get_user_configuration_files_in_path(os.path.join(input_dir_user_configuration, "profile/package.provided"))
	return res

def load_user_configuration(concurrent_map):
	load  = False
	last_update = time.gmtime(0)
	input_data_files = []
	# 1. check if we have a profile file


######################################################################
### LOAD PORTAGE
######################################################################

def load_portage():
	# 1. check if we have a portage file

	# 2. check if we need to update

	# 3. recreate the portage file and portage configuration



######################################################################
### MAIN
######################################################################

def main():
	# 1. check if the output directory exists
	if not os.path.exists(output_dir):
		os.makedirs(output_dir)
	elif not os.path.isdir(output_dir):
		logging.error("The output directory \"" + output_dir + "\" already exists and is not a directory")
		sys.exit(-1)
	# 2. load portage
	# 3. load the profile

	# 4. load the user configuration







if __name__ == "__main__":
	main()