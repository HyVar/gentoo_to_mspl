#!/usr/bin/python

import multiprocessing
import string
import os


# in portage, we only consider the egencache files (and the other ones we generate), as it is the default behavior of emerge

######################################################################
### GET EGENCACHE FILES FOM A MD5-CACHE REPOSITORY
######################################################################


def get_egencache_files(path, match_path=(lambda x: True)):
	"""
	returns the set of portage files to load
	"""
	files = []
	for root, dirnames, filenames in os.walk(path):
		for filename in filenames:
			path_file = os.path.join(root, filename)
			if match_path(path_file): files.append(path_file)
	return files


######################################################################
### EXTRACT DATA FROM PACKAGE FILE NAMES AND PATH
######################################################################


def structure_package_name(package_name):
	"""
	this function splits a portage package name into relevant information
	"""
	filename_split = package_name.split("-")
	version_full, version = (None, None)
	if len(filename_split) > 1:
		check1 = filename_split[-1]
		check2 = filename_split[-2]
		if check1[0] == 'r' and check2[0].isdigit():
			revision = check1
			version = check2
			del filename_split[-2:]
			version_full = version + "-" + revision
		elif check1[0].isdigit():
			version = check1
			del filename_split[-1]
			version_full = version
	package_group = "-".join(filename_split)
	return (package_group, version_full, version)


def get_package_name_from_path(package_path):
	els = package_path.split(os.sep)
	package_name = "/".join(els[:-2]) if len(els) > 1 else els[-1]
	deprecated = (len(els) > 2) and (els[-3] == "deprecated")
	return (package_name, deprecated)


######################################################################
### TRANSLATE ATOMS INTO HASHABLE PATTERNS
######################################################################



######################################################################
### LOAD A PORTAGE MD5-CACHE REPOSITORY
######################################################################


def construct_spl(package_name, package_group, deprecated, version_full, version, keywords_string, slots_string, iuses_string, fm_local, fm_external, fm_runtime):
	"""
	create the spl structure from the extracted information
	"""
	keywords = keywords_string.split() if keywords_string else ["*"]

	slots = slots_string.split("/") if slots_string else [0, 0]
	slot = str(slots[0])
	subslot = (str(slots[1]) if (len(slots) == 2) else "0")


	iuses = []
	use_configuration_default = utils_hyportage.use_configuration_create()
	for iuse in (iuses_string.split() if iuses_string else []):
		if iuse[0] == "+":
			iuse = iuse[1:]
			iuses.append(iuse)
			utils_hyportage.use_configuration_add(use_configuration_default, iuse)
		elif iuse[0] == "-":
			iuse = iuse[1:]
			iuses.append(iuse)
			utils_hyportage.use_configuration_remove(use_configuration_default, iuse)
		else:
			iuses.append(iuse)

	fm_local = fm_local if fm_local else ""
	fm_external = fm_external if fm_external else ""
	fm_runtime = fm_runtime if fm_runtime else ""

	data = {'name': package_name, 'group': package_group, 'features': features, 'environment': keywords,
			'fm': { 'local': fm_local, 'external': fm_external, 'runtime': fm_runtime },
			'versions': {'full': str(version_full), 'base': str(version) },
			'slot': slot, 'subslot': subslot}
	return utils_hyportage.spl_create(
		package_name, package_group, deprecated,
		version_full, version,
		keywords,
		slot, subslot,
		iuses, use_configuration_default,
		fm_local, fm_external, fm_runtime )


def load_file_egencache(file_path):
	"""
	create the spl structure of a portage md5-cache file, and stores it in the mspl global variable
	"""
	# 1. base information from the file name
	package_name, deprecated = get_package_name_from_path(file_path)
	package_group, version_full, version = structure_package_name(package_name)
	# 2. informations from the file content
	data_tmp = {}
	with open(filepath, 'r') as f:
		for line in f:
			array = string.split(line, "=", 1)
			data_tmp[array[0]] = array[1][:-1]  # remove the \n at the end of the line
	# 3. return the data
	return construct_spl(
		package_name, package_group, deprecated,
		version_full, version,
		data_tmp.get('KEYWORDS'),
		data_tmp.get('SLOT'),
		data_tmp.get('IUSE'),
		data_tmp.get('REQUIRED_USE'),
		data_tmp.get('DEPEND'),
		data_tmp.get('RDEPEND')
	)


def load_files_egencache(concurrent_map, filepaths):
	return concurrent_map(load_file_egencache, filepaths)

