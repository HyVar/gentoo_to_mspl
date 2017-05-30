#!/usr/bin/python

import utils

import os
import sys

import time
import json
import gzip
import tarfile

#####################################################################################
### GENERATING DATA FROM A GENTOO INSTALLATION
#####################################################################################

def generate_all(path_to_md5):
	# 1. load all packages
	print("loading repository ...")
	time0 = time.time()
	repository = utils.load_from_egencache(path_to_md5)
	time1 = time.time()
	print("   ... " + str(time1 - time0) + " secs")
	# 2. generating the entries for the packages
	print("completing repository ...")
	time0 = time.time()
	packages = utils.generate_packages(repository)
	repository.update(packages)
	time1 = time.time()
	print("   ... " + str(time1 - time0) + " secs")
	# 3. generate extra data and catalog
	print("computing dependencies and catalog ...")
	time0 = time.time()
	spl_parser = utils.SPLParser()
	spl_parser.load_repository(repository)
	time1 = time.time()
	print("   ... " + str(time1 - time0) + " secs")
	catalog = spl_parser.get_catalog()
	return (catalog, repository)


#####################################################################################
### LOADING AND SAVING DATA
#####################################################################################

def dtouch(dirname):
	if not os.path.exists(dirname):
		os.makedirs(dirname)


def save_catalog(catalog_dir, catalog):

	filename = os.path.join(catalog_dir, "features.json")
	f = open(filename, 'w')
	json.dump(catalog['features'] , f, sort_keys=True, indent=4, separators=(',', ': '))
	f.close()

	filename = os.path.join(catalog_dir, "names.json")
	f = open(filename, 'w')
	json.dump({'declared': catalog['spl'].keys(), 'used': catalog['spl_used'] }, f, sort_keys=True, indent=4, separators=(',', ': '))
	f.close()

	filename = os.path.join(catalog_dir, "versions.json")
	f = open(filename, 'w')
	json.dump(catalog['versions'] , f, sort_keys=True, indent=4, separators=(',', ': '))
	f.close()

	filename = os.path.join(catalog_dir, "slots.json")
	f = open(filename, 'w')
	json.dump(catalog['slots'] , f, sort_keys=True, indent=4, separators=(',', ': '))
	f.close()

	filename = os.path.join(catalog_dir, "subslots.json")
	f = open(filename, 'w')
	json.dump(catalog['slots'] , f, sort_keys=True, indent=4, separators=(',', ': '))
	f.close()

	metadata_dir = os.path.join(catalog_dir, "spl")
	dtouch(metadata_dir)
	for name, d in catalog['spl'].iteritems():
		filename = os.path.join(metadata_dir, name + ".json")
		dtouch(os.path.dirname(filename))
		f = open(filename, 'w')
		json.dump(d , f, sort_keys=True, indent=4, separators=(',', ': '))
		f.close()


def save_mspl(mspl_dir, mspl):
	for name, d in mspl.iteritems():
		filename = os.path.join(mspl_dir, name + ".json")
		dtouch(os.path.dirname(filename))
		f = open(filename, 'w')
		json.dump(d , f, sort_keys=True, indent=4, separators=(',', ': '))
		f.close()


#####################################################################################
### MAIN FUNCTIONS
#####################################################################################


if __name__ == "__main__":
	if len(sys.argv) != 2:
		print ("usage: ", sys.argv[0], " main-folder")
		sys.exit(-1)
	root_dir = sys.argv[1]
	#
	path_to_md5= os.path.join(root_dir, "usr/portage/metadata/md5-cache")
	catalog_dir = os.path.join(root_dir, "json/catalog")
	mspl_dir = os.path.join(root_dir, "json/mspl")
	#
	dtouch(os.path.join(root_dir, "json"))
	dtouch(catalog_dir)
	dtouch(mspl_dir)
	#
	root_spl_name="__root__"
	catalog, mspl = generate_all(path_to_md5)
	save_catalog(catalog_dir, catalog)
	save_mspl(mspl_dir, mspl)



