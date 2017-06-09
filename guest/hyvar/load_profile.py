#!/usr/bin/python

import os
import os.path
import subprocess
import multiprocessing
import logging
import re
import json


######################################################################
### USE AND DATA MANAGEMENT
######################################################################

def split_string(string):
	return re.findall(">?<?=?[a-zA-Z0-9._@][a-zA-Z0-9._\-+@/:]*", string)


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


def use_map_to_inner_list(uses):
	return { 'positive': list(uses['positive']), 'negative': list(uses['negative']) }

# data
class ProfileData(object):
	def __init__(self):
		self.iuses = set([])
		self.uses = use_create_map()
		self.packages = { 'system': set([]), 'profile': set([]), 'mask': set([]) }
		self.package_uses = {}

	def update_iuse(self, iuses):
		self.iuses.update(iuses)

	def update_use(self, uses):
		use_update_map_map(self.uses, uses)

	def update_use_simple(self, use):
		use_update_map_simple(self.uses, use)

	def update_system_package(self, package):
		self.packages['system'].add(package)

	def update_profile_package(self, package):
		self.packages['profile'].add(package)

	def update_package_mask(self, package):
		self.packages['mask'].add(package)

	def update_package_use(self, package_uses):
		package, uses = package_uses
		if package in self.package_uses:
			use_update_map_map(self.package_uses[package], uses)
		else:
			self.package_uses[package] = uses

	def add_egencache_data(self, d):
		package, package_uses = d
		if package in self.package_uses:
			use_update_map_map(self.package_uses[package], package_uses)
		else:
			self.package_uses[package] = package_uses


	def toDict(self):
		packages = { 'system': list(self.packages['system']), 'profile': list(self.packages['profile']), 'mask': list(self.packages['mask']) }
		package_uses = { package: use_map_to_inner_list(uses) for package, uses in self.package_uses.iteritems() }
		return { 'iuses':list(self.iuses), 'uses': use_map_to_inner_list(self.uses), 'packages': packages, 'package_uses': package_uses }

	def __repr__(self):
		return repr(self.toDict())

	def __str__(self):
		return str(self.toDict())


# WARNING:
# we have two kind of included package: system set and profile set
# package.mask is tricky:
#  - because file inclusion is ordered, we need to apply the mask on the system and profile sets
#  - because we need to say to the user that he cannot install masked package, we need to remember it as a separated list.
#  hence, we need to do both... However, it is very possible that things are implemented in a simpler manner, and we don't need to update the list of required packages
# for now, our implementation will follow the simple approach



######################################################################
### ANALYSING PROFILE FILES
######################################################################

profile_path = os.path.realpath("/etc/portage/make.profile")

def get_profile_files(path=profile_path, acc=None):
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




# manage make.defaults and make.conf
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
	for line in out.splitlines():
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
	if 'USE' in bash_environment: data.update_use(use_process_list(bash_environment['USE'].split()))
	if 'IUSE' in bash_environment: data.update_iuse(use_process_list(bash_environment['IUSE'].split()))


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

def analyse_packages(line):
	if line[0] == "*":
		return (ProfileData.update_system_package, line[1:])
	else:
		return (ProfileData.update_profile_package, line)
	
def analyse_package_mask(line):
	return (ProfileData.update_package_mask, line)

def analyse_package_use(line):
	tmp = split_string(line)
	return (ProfileData.update_package_use, (tmp[0], use_process_list(tmp[1:])))

def analyse_package_use_mask(line):
	tmp = split_string(line)
	return (ProfileData.update_package_use, (tmp[0], use_invert_map(use_process_list(tmp[1:]))))

def analyse_use(line): # one use per line
	return (ProfileData.update_use_simple, line)

def analyse_use_mask(line): # one use per line
	return (ProfileData.update_use_simple, use_invert(line))


__analyse_mapping = {
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

def analyse_profile_file(filename):
		function = __analyse_mapping.get(os.path.basename(filename))
		if function:
			with open(filename, 'r') as f:
				return process_file(f, function)
		elif "package.use" in filename: # files stored in /etc/portage/package.use
			with open(filename, 'r') as f:
				return process_file(f, analyse_package_use)
		else: # the rest is considered to be make.defaults or make.conf
			print("dealing with " + filename)
			return [(analyse_make_defaults, filename)] # make.defaults needs to be handled in sequence, to correctly deal with the environment


path_make_conf = "/etc/portage/make.conf"
path_package_use = "/etc/portage/package.use"

def analyse_profile(concurrent_map, data):
	profile_file_list = get_profile_files()
	# add files from /etc/portage
	if os.path.isfile(path_make_conf):
		profile_file_list.append(path_make_conf)
	if os.path.isfile(path_package_use):
		profile_file_list.append(path_package_use)
	elif os.path.isdir(path_package_use):
		profile_file_list.extend([os.path.join(path_package_use, filename) for filename in os.listdir(path_package_use)])
	# process everything
	profile_data_list = concurrent_map(analyse_profile_file, profile_file_list)
	for inner_list in profile_data_list:
		for function, profile_data in inner_list:
			function(data, profile_data)

######################################################################
### ANALYSING EGENCACHE FILES FOR PARTIAL CONFIGURATION
######################################################################

egencache_path = "/usr/portage/metadata/md5-cache"

def get_egencache_files():
    """
    returns the set of portage files to load
    """
    files = []
    for root, dirnames, filenames in os.walk(egencache_path):
        files.extend([os.path.join(root, filename) for filename in filenames])
    return files

def analyse_egencache_file(filename):
	data_tmp = {}
	with open(filename, 'r') as f:
		for line in f:
			line = line[:-1]  # remove the \n at the end of the line
			array = line.split("=", 1)
			data_tmp[array[0]] = array[1]
	if 'IUSE' in data_tmp:
		package = "=" + filename
		package_uses = use_create_map()
		for iuse in re.findall("[a-zA-Z0-9._\-+@]+", data_tmp['IUSE']):
			iuse_update_map_simple(package_uses, iuse)
		if (len(package_uses['positive']) + len(package_uses['negative']) > 0): # avoids filling the data with empty information
			return (package, package_uses)
		else:
			return None

def analyse_egencache(concurrent_map, data):
	egencache_data_list = concurrent_map(analyse_egencache_file, get_egencache_files())
	for egencache_data in egencache_data_list:
		if egencache_data:
			data.add_egencache_data(egencache_data)
		


######################################################################
### GLOBAL FUNCTIONS
######################################################################

available_cores = 3

""" does not work with multiprocessing:
multiprocessing.pool.MaybeEncodingError: Error sending result: '[[(<unbound method ProfileData.update_use_simple>, '-elogind'), (<unbound method ProfileData.update_use_simple>, '-curl_ssl_winssl'), (<unbound method ProfileData.update_use_simple>, '-kmod'), (<unbound method ProfileData.update_use_simple>, '-packagekit'), (<unbound method ProfileData.update_use_simple>, '-selinux'), (<unbound method ProfileData.update_use_simple>, '-uclibc'), (<unbound method ProfileData.update_use_simple>, '-multilib'), (<unbound method ProfileData.update_use_simple>, '-userland_BSD'), (<unbound method ProfileData.update_use_simple>, '-elibc_AIX'), (<unbound method ProfileData.update_use_simple>, '-elibc_bionic'), (<unbound method ProfileData.update_use_simple>, '-elibc_Cygwin'), (<unbound method ProfileData.update_use_simple>, '-elibc_Darwin'), (<unbound method ProfileData.update_use_simple>, '-elibc_DragonFly'), (<unbound method ProfileData.update_use_simple>, '-elibc_FreeBSD'), (<unbound method ProfileData.update_use_simple>, '-elibc_HPUX'), (<unbound method ProfileData.update_use_simple>, '-elibc_Interix'), (<unbound method ProfileData.update_use_simple>, '-elibc_mintlib'), (<unbound method ProfileData.update_use_simple>, '-elibc_musl'), (<unbound method ProfileData.update_use_simple>, '-elibc_NetBSD'), (<unbound method ProfileData.update_use_simple>, '-elibc_OpenBSD'), (<unbound method ProfileData.update_use_simple>, '-elibc_SunOS'), (<unbound method ProfileData.update_use_simple>, '-elibc_uclibc'), (<unbound method ProfileData.update_use_simple>, '-elibc_Winnt'), (<unbound method ProfileData.update_use_simple>, '-kernel_AIX'), (<unbound method ProfileData.update_use_simple>, '-kernel_Darwin'), (<unbound method ProfileData.update_use_simple>, '-kernel_FreeBSD'), (<unbound method ProfileData.update_use_simple>, '-kernel_freemint'), (<unbound method ProfileData.update_use_simple>, '-kernel_HPUX'), (<unbound method ProfileData.update_use_simple>, '-kernel_NetBSD'), (<unbound method ProfileData.update_use_simple>, '-kernel_OpenBSD'), (<unbound method ProfileData.update_use_simple>, '-kernel_SunOS'), (<unbound method ProfileData.update_use_simple>, '-kernel_Winnt'), (<unbound method ProfileData.update_use_simple>, '-aqua'), (<unbound method ProfileData.update_use_simple>, '-coreaudio'), (<unbound method ProfileData.update_use_simple>, '-prefix'), (<unbound method ProfileData.update_use_simple>, '-prefix-chain'), (<unbound method ProfileData.update_use_simple>, '-prefix-guest'), (<unbound method ProfileData.update_use_simple>, '-kqueue'), (<unbound method ProfileData.update_use_simple>, '-python_targets_jython2_7'), (<unbound method ProfileData.update_use_simple>, '-python_single_target_jython2_7'), (<unbound method ProfileData.update_use_simple>, '-prelude'), (<unbound method ProfileData.update_use_simple>, '-netlink'), (<unbound method ProfileData.update_use_simple>, '-openrc-force'), (<unbound method ProfileData.update_use_simple>, '-php_targets_php5-4'), (<unbound method ProfileData.update_use_simple>, '-php_targets_php5-5')], [(<unbound method ProfileData.update_use_simple>, 'elibc_glibc'), (<unbound method ProfileData.update_use_simple>, 'kernel_linux'), (<unbound method ProfileData.update_use_simple>, 'userland_GNU')], [(<function analyse_make_defaults at 0x7fec809f68c0>, '/usr/portage/profiles/base/make.defaults')], [(<unbound method ProfileData.update_system_package>, '>=sys-apps/baselayout-2'), (<unbound method ProfileData.update_system_package>, 'app-arch/bzip2'), (<unbound method ProfileData.update_system_package>, 'app-arch/gzip'), (<unbound method ProfileData.update_system_package>, 'app-arch/tar'), (<unbound method ProfileData.update_system_package>, 'app-arch/xz-utils'), (<unbound method ProfileData.update_system_package>, 'app-shells/bash:0'), (<unbound method ProfileData.update_system_package>, 'net-misc/iputils'), (<unbound method ProfileData.update_system_package>, 'net-misc/rsync'), (<unbound method ProfileData.update_system_package>, 'net-misc/wget'), (<unbound method ProfileData.update_system_package>, 'sys-apps/coreutils'), (<unbound method ProfileData.update_system_package>, 'sys-apps/diffutils'), (<unbound method ProfileData.update_system_package>, 'sys-apps/file'), (<unbound method ProfileData.update_system_package>, '>=sys-apps/findutils-4.4'), (<unbound method ProfileData.update_system_package>, 'sys-apps/gawk'), (<unbound method ProfileData.update_system_package>, 'sys-apps/grep'), (<unbound method ProfileData.update_system_package>, 'sys-apps/kbd'), (<unbound method ProfileData.update_system_package>, 'sys-apps/less'), (<unbound method ProfileData.update_system_package>, 'sys-apps/openrc'), (<unbound method ProfileData.update_system_package>, 'sys-process/procps'), (<unbound method ProfileData.update_system_package>, 'sys-process/psmisc'), (<unbound method ProfileData.update_system_package>, 'sys-apps/sed'), (<unbound method ProfileData.update_system_package>, 'sys-apps/which'), (<unbound method ProfileData.update_system_package>, 'sys-devel/binutils'), (<unbound method ProfileData.update_system_package>, 'sys-devel/gcc'), (<unbound method ProfileData.update_system_package>, 'sys-devel/gnuconfig'), (<unbound method ProfileData.update_system_package>, 'sys-devel/make'), (<unbound method ProfileData.update_system_package>, '>=sys-devel/patch-2.7'), (<unbound method ProfileData.update_system_package>, 'sys-fs/e2fsprogs'), (<unbound method ProfileData.update_system_package>, 'virtual/dev-manager'), (<unbound method ProfileData.update_system_package>, 'virtual/editor'), (<unbound method ProfileData.update_system_package>, 'virtual/libc'), (<unbound method ProfileData.update_system_package>, 'virtual/man'), (<unbound method ProfileData.update_system_package>, 'virtual/modutils'), (<unbound method ProfileData.update_system_package>, 'virtual/os-headers'), (<unbound method ProfileData.update_system_package>, 'virtual/package-manager'), (<unbound method ProfileData.update_system_package>, 'virtual/pager'), (<unbound method ProfileData.update_system_package>, 'virtual/service-manager'), (<unbound method ProfileData.update_system_package>, 'virtual/shadow'), (<unbound method ProfileData.update_system_package>, 'virtual/ssh')]]'. Reason: 'PicklingError("Can't pickle <type 'instancemethod'>: attribute lookup __builtin__.instancemethod failed",)'
"""
def main():
	data = ProfileData()
	pool = multiprocessing.Pool(available_cores) 
	analyse_egencache(pool.map, data)
	#analyse_profile(pool.map, data)
	analyse_profile(map, data)
	with open("gen/profile.json", 'w') as f:
		json.dump(data.toDict(), f)



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
	main()
	#data = ProfileData()
	#with open("/usr/portage/profiles/arch/amd64/use.mask", 'r') as f:
	#	analyse_use_mask(f, data)
	#analyse_make_defaults(data, "/usr/portage/profiles/releases/make.defaults")
	#print(str(data))
