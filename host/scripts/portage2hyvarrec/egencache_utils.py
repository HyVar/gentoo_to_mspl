#!/usr/bin/python

import multiprocessing
import string
import os




######################################################################
### FUNCTIONS TO LOAD A PORTAGE MD5-CACHE REPOSITORY
######################################################################



def structure_package_name(package_name):
	"""
	this function splits a portage package name into relevant information
	"""
	filename_split = package_name.split("-")
	version_all, version, revision = (None, None, None)
	if len(filename_split) > 1:
		check1 = filename_split[-1]
		check2 = filename_split[-2]
		#print(str(filename_split) + ": (" + check2 + ", " + check1 + ")")
		if check1[0] == 'r' and check2[0].isdigit():
			revision = check1
			version = check2
			del filename_split[-2:]
			version_all = version + "-" + revision
		elif check1[0].isdigit():
			revision = "r0"
			version = check1
			del filename_split[-1]
			version_all = version
	package = "-".join(filename_split)
	return (package, version_all, version, revision)


def get_egencache_files(path):
	"""
	returns the set of portage files to load
	"""
	files = []
	for root, dirnames, filenames in os.walk(path):
		files.extend([os.path.join(root, filename) for filename in filenames])
	return files


def construct_spl(names, versions, environment, slots, features, fm_local, fm_external, fm_runtime):
	"""
	create the spl structure from the extracted information
	"""
	name, group_name = names
	version_all, version, revision = versions
	environment = environment.split() if environment else ["*"]
	slots = slots.split("/") if slots else [0, 0]
	slot = str(slots[0])
	has_subslot = (len(slots) == 2)
	subslot = (str(slots[1]) if has_subslot else "0")
	features = features.split() if features else []
	features = [ (feature[1:] if (feature[0] in ['+', '-']) else feature) for feature in features ]
	fm_local = fm_local if fm_local else ""
	fm_external = fm_external if fm_external else ""
	fm_runtime = fm_runtime if fm_runtime else ""
	data = {'name': name, 'group_name': group_name, 'features': features, 'environment': environment,
			'fm': {'local': fm_local, 'external': fm_external, 'runtime': fm_runtime},
			'versions': {'full': str(version_all), 'base': str(version), 'revision': str(revision)},
			'slot': slot, 'subslot': subslot}
	return data


def load_file_egencache(filepath):
	"""
	create the spl structure of a portage md5-cache file, and stores it in the mspl global variable
	"""
	# 1. base information from the file name
	path_to_file, filename = os.path.split(filepath)
	path_to_category, category = os.path.split(path_to_file)
	package, version_all, version, revision = structure_package_name(filename)
	name = category + "/" + filename
	# 2. informations from the file content
	data_tmp = {}
	with open(filepath, 'r') as f:
		for line in f:
			array = string.split(line, "=", 1)
			data_tmp[array[0]] = array[1][:-1]  # remove the \n at the end of the line
	# 3. return the data
	return construct_spl(
		(name, category + "/" + package),
		(version_all, version, revision),
		data_tmp.get('KEYWORDS'),
		data_tmp.get('SLOT'),
		data_tmp.get('IUSE'),
		data_tmp.get('REQUIRED_USE'),
		data_tmp.get('DEPEND'),
		data_tmp.get('RDEPEND')
	)


def load_files_egencache(concurrent_map, filepaths):
	return concurrent_map(load_file_egencache, filepaths)

