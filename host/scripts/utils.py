"""
utils.py: file containing some variables used by other modules 
"""
__author__ = "Michael Lienhardt & Jacopo Mauro"
__copyright__ = "Copyright 2017, Michael Lienhardt & Jacopo Mauro"
__license__ = "ISC"
__version__ = "0.1"
__maintainer__ = "Jacopo Mauro"
__email__ = "mauro.jacopo@gmail.com"
__status__ = "Prototype"

import re
import uuid

import multiprocessing
import threading

import logging

import os
import os.path
import json
import marshal
import gzip
import cPickle

######################################################################
### BASE STRUCTURED DICTIONARIES AND LISTS MANIPULATION
######################################################################

def dict_create(parameter):
    key, val = parameter
    return { key: val }

def list_creat(parameter):
    return [parameter]


def dict_put_inline(dictionary, key, val, el_create, el_put_inline):
    if key in dictionary: el_put_inline(dictionary[key], val)
    else: dictionary[key] = el_create(val)

def list_put_inline(l, val):
    l.append(val)


def dict_combine_inline(dict1, dict2, inline_combine):
	for k,v in dict2.iteritems():
		if k in dict1:
			inline_combine(dict1[k], dict2[k])
		else:
			dict1[k] = dict2[k]

def list_combine_inline(l1,l2):
	return l1.extend(l2)

def all_combine_inline_drop(val1, val2):
	pass

######################################################################
### GENTOO RELATED INFORMATION AND FUNCTIONS
######################################################################

PACKAGE_NAME_SEPARATOR = '/'
VERSION_RE = "-[0-9]+(\.[0-9]+)*[a-zA-Z]?((_alpha|_beta|_pre|_rc|_p)[0-9]*)*(-r[0-9]+)?$"

# consider only envirnoments that we are sure the component can be installed
# * and ** are treated the same, ~x and x are treated the same
def process_keyword(s):
	if s == "**":
		return "*"
	if s[0] == "~":  # testing env are equivalent for us to stable env
		return s[1:]
	return s


######################################################################
### FILES RELATED INFORMATION AND FUNCTIONS
######################################################################

TEMP_DIR = 'tmp'
TMP_FILES_LOCK = threading.Lock()
TMP_FILES = []

# List of the temp files.
__tmp_files = []
__tmp_files_lock = multiprocessing.Lock()

def get_new_temp_file(extension):
	global __tmp_files_lock
	global __tmp_files
	name = '/tmp/' + uuid.uuid4().hex + '.' + extension
	__tmp_files_lock.acquire()
	__tmp_files.append(name)
	__tmp_files_lock.release()
	return name


def load_data_file(file_name, save_modality="gzjson"):
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


def store_data_file(file_name, data, save_modality="gzjson"):
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
### LIST COMPACTION
######################################################################

def compact_list(l):
	l = sorted(l)
	res = [] if len(l) == 0 else [l[0]]
	for v1, v2 in zip(l, l[1:]):
		if v1 != v2:
			res.append(v2)
	return res

######################################################################
### ID GENERATION
######################################################################

__id_current = 0
__id_current_lock = multiprocessing.Lock()


def new_id():
	global __id_current
	global __id_current_lock
	with __id_current_lock:
		res = __id_current
		__id_current = __id_current + 1
	return unicode(res)


def new_ids(nb=1):
	global __id_current
	global __id_current_lock
	with __id_current_lock:
		res = [ unicode(i) for i in xrange(__id_current, __id_current + nb) ]
		__id_current = __id_current + nb
	return res


def get_last_id(): return __id_current
def set_last_id(last_id):
	global __id_current
	__id_current = last_id


CONTEXT_VAR_NAME = "ccc"

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







