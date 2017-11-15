"""
utils.py: file containing some variables used by other modules 
"""

import re
import uuid
import time

import multiprocessing
import tempfile

import logging

import os
import os.path
import json
import marshal
import gzip
import cPickle


__author__ = "Michael Lienhardt & Jacopo Mauro"
__copyright__ = "Copyright 2017, Michael Lienhardt & Jacopo Mauro"
__license__ = "ISC"
__version__ = "0.1"
__maintainer__ = "Jacopo Mauro"
__email__ = "mauro.jacopo@gmail.com"
__status__ = "Prototype"


######################################################################
# FILES RELATED INFORMATION AND FUNCTIONS
######################################################################


# List of the temp files.
__tmp_files_directory = "/tmp"
__tmp_files = []
__tmp_files_lock = multiprocessing.Lock()


def get_new_temp_file(extension):
	global __tmp_files_lock
	global __tmp_files
	# probablility of picking up the same uuid is negligible
	file_id, name = tempfile.mkstemp(suffix=extension, text=True)
	os.close(file_id)
	__tmp_files_lock.acquire()
	__tmp_files.append(name)
	__tmp_files_lock.release()
	return name


def clean_temp_files():
	__tmp_files_lock.acquire()
	for f in __tmp_files:
		if os.path.exists(f):
			os.remove(f)
		__tmp_files_lock.release()


##

def load_data_file(file_name, save_modality="pickle"):
	if save_modality == "marshal":
		with open(file_name, "r") as f:
			data = marshal.load(f)
	if save_modality == "pickle":
		with open(file_name, "r") as f:
			data = cPickle.load(f)
	elif save_modality == "gzjson":
		with gzip.open(file_name, "r") as f:
			data = json.load(f)
	elif save_modality == "json":
		with open(file_name, "r") as f:
			data = json.load(f)
	else:
		logging.error(
			"Cannot load data from file \"" + file_name + "\", because the format \""
			+ save_modality + "\" is unknown")
		data = None
	return data


def store_data_file(file_name, data, save_modality="pickle"):
	# 1. create file if does not exist
	basedir = os.path.dirname(file_name)
	if not os.path.exists(basedir): os.makedirs(basedir)
	with open(file_name, 'a'):
		pass
	# 2. write the data
	if save_modality == "marshal": # marshal can not use gzip file directly (possible work around marshal.dumps)
		with open(file_name, 'w') as f:
			marshal.dump(data,f)
	if save_modality == "pickle": # marshal can not use gzip file directly (possible work around marshal.dumps)
		with open(file_name, 'w') as f:
			cPickle.dump(data,f)
	elif save_modality == "gzjson":
		with gzip.GzipFile(file_name, 'wb') as f:
			json.dump(data,f)
	elif save_modality == "json":
		with open(file_name, 'w') as f:
			json.dump(data,f)
	else:
		logging.error(
			"Cannot save data on file \"" + file_name + "\", because the format \""
			+ save_modality + "\" is unknown")


######################################################################
# LIST COMPACTION
######################################################################

def compact_list(l):
	l = sorted(l)
	res = [] if len(l) == 0 else [l[0]]
	for v1, v2 in zip(l, l[1:]):
		if v1 != v2:
			res.append(v2)
	return res

######################################################################
# ID GENERATION
######################################################################

__id_current_lock = multiprocessing.Lock()


def new_id(obj):
	global __id_current_lock
	with __id_current_lock:
		res = obj.id_current
		obj.id_current = obj.id_current + 1
	return unicode(res)


def new_ids(obj, nb=1):
	global __id_current_lock
	with __id_current_lock:
		res = [ unicode(i) for i in xrange(obj.id_current, obj.id_current + nb) ]
		obj.id_current = obj.id_current + nb
	return res


CONTEXT_VAR_NAME = "ccc"


######################################################################
# PHASE LOGGING
######################################################################

t = None


def phase_start(message):
	global t
	logging.info(message)
	t = time.time()

def phase_end(message):
	global t
	logging.info(message + " in " + unicode(time.time() - t) + " seconds.")


######################################################################
### TRANSLATION SIMPLIFICATION FUNCTIONS
######################################################################

def is_base_package(mspl,name):
	"""
	given the data returns true if the name is a base package
	"""
	assert name in mspl
	return "implementations" in mspl[name]


def get_base_package(data,name):
	"""
	given a string returns the base package name if available, "" otherwise
	"""
	if name in data:
		if "implementations" in data[name]:
			return name
		else:
			return data[name]["group_name"]
	m = re.search(VERSION_RE, name)
	if m:
		version = m.group()[1:]
		return name.replace("-" + version, "")
	return ""







