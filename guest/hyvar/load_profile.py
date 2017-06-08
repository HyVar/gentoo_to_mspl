#!/usr/bin/python

import os
import os.path
import subprocess
import logging
import re


######################################################################
### USE AND DATA MANAGEMENT
######################################################################


# use and use_map
def use_create_map():
	return { 'positive': set([]), 'negative': set([]) }

def use_update_map_simple(uses, use):
	if use[0] == '-':
		uses['negative'].add(use[1:])
	else:
		uses['positive'].add(use)

def use_invert(use):
	if use[0] == '-':
		return use[1:]
	else:
		return "-" + use

def iuse_update_map_simple(uses, iuse):
	if iuse[0] == '-':
		uses['negative'].add(iuse[1:])
	elif iuse[0] == '+':
		uses['positive'].add(iuse[1:])


def use_process_list(uselist):
	res = use_create_map()
	for use in uselist:
		use_update_map_simple(res, use)
	return res

def use_invert_map(uses):
	return 	{ 'positive': uses['negative'], 'negative': uses['positive'] }

def use_update_map_map(uses1, uses2):
   	uses1['positive'].difference_update(uses2['negative'])
   	uses1['negative'].difference_update(uses2['positive'])
   	uses1['positive'].update(uses2['positive'])
   	uses1['negative'].update(uses2['negative'])


# data
class ProfileData(object):
	def __init__(self):
		self.uses = use_create_map()
		self.packages = { 'system': set([]), 'profile': set([]), 'mask': set([]) }
		self.package_uses = {}

	def update_use(self, uses):
		use_update_map_map(self.uses, uses)

	def update_use_simple(self, use):
		use_update_map_simple(self.uses, use)

	def update_use_simple_mask(self, use):
		use_update_map_simple(self.uses, use_invert(use))

	def update_system_package(self, package):
		self.packages['system'].add(package)

	def update_profile_package(self, package):
		self.packages['profile'].add(package)

	def update_package_mask(self, package):
		self.packages['mask'].add(package)

	def update_package_use(self, package, uses):
		if package in self.package_uses:
			use_update_map_map(self.package_uses[package], uses)
		else:
			self.package_uses[package] = uses

	def toDict(self):
		return { 'uses': self.uses, 'packages': self.packages, 'package_uses': self.package_uses }

	def __repr__(self):
		return repr(self.toDict())

	def __str__(self):
		return str(self.toDict())


# data
# we have two kind of included package: system set and profile set
# package.mask is tricky:
#  - because file inclusion is ordered, we need to apply the mask on the system and profile sets
#  - because we need to say to the user that he cannot install masked package, we need to remember it as a separated list.
#  hence, we need to do both... However, it is very possible that things are implemented in a simpler manner, and we don't need to update the list of required packages
# for now, our implementation will follow the simple approach

######################################################################
### ANALYSING PROFILE FILES
######################################################################

"""
This function needs to be extended (from https://dev.gentoo.org/~zmedico/portage/doc/man/portage.5.html):
The profile default settings for Portage. The general format is described in make.conf(5). The make.defaults for your profile defines a few specific variables too:

    ARCH
        Architecture type (x86/ppc/hppa/etc...). 
    IUSE_IMPLICIT = [space delimited list of USE flags]
        Defines implicit IUSE for ebuilds using EAPI 5 or later. Flags that come from USE_EXPAND or USE_EXPAND_UNPREFIXED variables do not belong in IUSE_IMPLICIT, since USE_EXPAND_VALUES_* variables are used to define implicit IUSE for those flags. See ebuild(5) for more information about IUSE. 
    USERLAND = GNU
        Support BSD/cygwin/etc... 
    USE_EXPAND = [space delimited list of variable names]
        Any variable listed here will be used to augment USE by inserting a new flag for every value in that variable, so USE_EXPAND="FOO" and FOO="bar bla" results in USE="foo_bar foo_bla". 
    USE_EXPAND_HIDDEN = [space delimited list of variable names]
        Names of USE_EXPAND variables that should not be shown in the verbose merge list output of the emerge(1) command. 
    USE_EXPAND_IMPLICIT = [space delimited list of variable names]
        Defines USE_EXPAND and USE_EXPAND_UNPREFIXED variables for which the corresponding USE flags may have implicit IUSE for ebuilds using EAPI 5 or later. 
    USE_EXPAND_UNPREFIXED = [space delimited list of variable names]
        Any variable listed here will be used to augment USE by inserting a new flag for every value in that variable, so USE_EXPAND_UNPREFIXED="FOO" and FOO="bar bla" results in USE="bar bla". 
    USE_EXPAND_VALUES_ARCH = [space delimited list of ARCH values]
        Defines ARCH values used to generate implicit IUSE for ebuilds using EAPI 5 or later. 
    USE_EXPAND_VALUES_ELIBC = [space delimited list of ELIBC values]
        Defines ELIBC values used to generate implicit IUSE for ebuilds using EAPI 5 or later. 
    USE_EXPAND_VALUES_KERNEL = [space delimited list of KERNEL values]
        Defines KERNEL values used to generate implicit IUSE for ebuilds using EAPI 5 or later. 
    USE_EXPAND_VALUES_USERLAND = [space delimited list of USERLAND values]
        Defines USERLAND values used to generate implicit IUSE for ebuilds using EAPI 5 or later. 
    ELIBC = glibc
        Support uClibc/BSD libc/etc... 
    PROFILE_ONLY_VARIABLES = ARCH
        Prevent critical variables from being changed by the user in make.conf or the env. 
    PROFILE_ARCH
        Distinguish machines classes that have the same ARCH. All sparc machines have ARCH=sparc but set this to either 'sparc32' or 'sparc64'. 
    BOOTSTRAP_USE
        Special USE flags which may be needed when bootstrapping from stage1 to stage2.
"""
def analyse_make_defaults(filename, data):
	process = subprocess.Popen(["bash", "-c", "source " + filename + "; echo $USE"], stdout=subprocess.PIPE)
	out, err = process.communicate()
	data.update_use(use_process_list(split_string(out[:-1]))) # remove trailing \n from the string


def split_string(string):
	return re.findall(">?<?=?[a-zA-Z0-9._@][a-zA-Z0-9._\-+@/:]*", string)


def process_file(f, data, function):
	for line in f:
		line = line[:-1] # remove trailing endline
		line.strip()
		if (len(line) == 0) or (line[0] == "#"):
			continue # skip all comments
		function(data, line)

def __analyse_packages(data, line):
	if line[0] == "*":
		data.update_system_package(line[1:])
	else:
		data.update_profile_package(line)
def analyse_packages(f, data):
	process_file(f, data, __analyse_packages)
	
def analyse_package_mask(f, data):
	process_file(f, data, ProfileData.update_package_mask)

def __analyse_package_use(data, line):
	print("__analyse_package_use: '" + line + "'")
	tmp = split_string(line)
	data.update_package_use(tmp[0], use_process_list(tmp[1:]))
def analyse_package_use(f, data):
	process_file(f, data, __analyse_package_use)

def __analyse_package_use_mask(data, line):
	print("__analyse_package_use_mask: '" + line + "'")
	tmp = split_string(line)
	data.update_package_use(tmp[0], use_invert_map(use_process_list(tmp[1:])))
def analyse_package_use_mask(f, data):
	process_file(f, data, __analyse_package_use_mask)

def analyse_use(f, data): # one use per line
	process_file(f, data, ProfileData.update_use_simple)

def analyse_use_mask(f, data):
	process_file(f, data, ProfileData.update_use_simple_mask)




######################################################################
### ANALYSING EGENCACHE FILES FOR PARTIAL CONFIGURATION
######################################################################

egencache_path = "/usr/portage/metadata/md5-cache"

def analyse_egencache(data):
	for root, dirnames, filenames in os.walk(egencache_path):
		for filename in filenames:
			data_tmp = {}
			with open(os.path.join(root, filename), 'r') as f:
				for line in f:
					line = line[:-1]  # remove the \n at the end of the line
					tmp = string.split(line, "=", 1)
					data_tmp[array[0]] = tmp[1]
			if 'IUSE' in data_tmp:
				package = "=" + filename
				if not package in data.package_uses:
					package_uses = use_create_map()
				else:
					package_uses = data.package_uses[package]
				for iuse in re.findall("[a-zA-Z0-9._\-+@]+", data_tmp['IUSE']):
					iuse_update_map_simple(package_uses, iuse)
				if (len(package_uses['positive']) + len(package_uses['negative']) > 0): # avoids filling the data with empty information
					data.package_uses[package] = package_uses



######################################################################
### GLOBAL FUNCTIONS
######################################################################

def get_profile_folders(profile_path, acc=None):
	if not acc:
		acc = set([])
	res = [ profile_path ]
	acc.add(profile_path)
	parent_file_name = os.path.join(profile_path, "parent")
	if os.path.isfile(parent_file_name):
		with open(parent_file_name, 'r') as f:
			data_tmp = {}
			for parent in f:
				parent = os.path.realpath(os.path.join(profile_path, parent[:-1]))
				if not parent in acc:
					res.extend(get_profile_folders(parent, acc))
	return res

__analyse_mapping = {
	#"make.defaults":			 analyse_make_defaults, # uses filename, not file
	#
	"packages":				  analyse_packages,
	"package.mask":			  analyse_package_mask,
	#
	"package.use":			   analyse_package_use,
	"package.use.force":		analyse_package_use,
	"package.use.stable.force": analyse_package_use,
	"package.use.mask":			analyse_package_use_mask,
	"package.use.stable.mask":  analyse_package_use_mask,
	#
	"use.force":				analyse_use,
	"use.stable.force":			analyse_use,
	"use.mask":					analyse_use_mask,
	"use.stable.mask":			analyse_use_mask
}

def analyse_profile_folder(folder, data):
	for filename in os.listdir(folder):
		if filename == "make.defaults":
			analyse_make_defaults(os.path.join(folder, filename), data)
		else:
			function = __analyse_mapping.get(filename)
			if function:
				with open(os.path.join(folder, filename), 'r') as f:
					function(f, data)
			else:
				logging.debug("unhandled file \"" + os.path.join(folder, filename) + "\"")

def main():
	profile_list = get_profile_folders(os.path.realpath("/etc/portage/make.profile"))
	profile_list.reverse()
	data = ProfileData()
	map((lambda folder: analyse_profile_folder(folder, data)), profile_list)
	print(str(data))



# TODO: deal with package configuration set in the .ebuild itself...
#	iterate over all egencache files, extract the IUSE, and the ones with + and - give a partial configuration
# TODO: deal with /etc/portage/package.use ...
#	not different from what I already did with the other package.use
# TODO: deal with /etc/portage/make.conf
#	not different from what I will do with the other make.defaults
# TODO: make things concurrent, as we have a lot of data to manage, like usually...

if __name__ == "__main__":
	#profile_list = get_profile_folders(os.path.realpath("/etc/portage/make.profile"))
	#profile_list.reverse()
	#print(str(profile_list))
	#print(split_string("net-analyzer/metasploit nexpose openvas"))
	#print(split_string(">=dev-scheme/slib-3.2.5 gambit scm"))
	#print(split_string("sys-boot/grub:2 grub_platforms_xen-32"))
	#main()
	data = ProfileData()
	#with open("/usr/portage/profiles/arch/amd64/use.mask", 'r') as f:
	#	analyse_use_mask(f, data)
	analyse_make_defaults("/usr/portage/profiles/releases/make.defaults", data)
	print(str(data))
