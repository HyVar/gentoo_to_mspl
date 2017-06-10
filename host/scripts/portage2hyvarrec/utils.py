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

def inline_combine_dicts(dict1, dict2, inline_combine):
    for k,v in dict2.iteritems():
        if k in dict1:
            inline_combine(dict1[k], dict2[k])
        else:
            dict1[k] = dict2[k]
def inline_combine_lists(l1,l2):
    return l1.extend(l2)
def inline_combine_drop(val1, val2):
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
NAME_MAP_FILE = 'name_maps.json'

# List of the temp files.
__tmp_files = []
__tmp_files_lock = multiprocessing.Lock()

def get_new_temp_file(extension):
    global __tmp_files_lock
    global __tmp_files
    name = '/tmp/' + uuid.uuid4().hex + '.' + extension
    #__tmp_files_lock.acquire()
    __tmp_files.append(name)
    #__tmp_files_lock.release()
    return name


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







