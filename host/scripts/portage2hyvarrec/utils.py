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

######################################################################
### GENTOO RELATED INFORMATION AND FUNCTIONS
######################################################################

PACKAGE_NAME_SEPARATOR = '/'
VERSION_RE = "-[0-9]+(\.[0-9]+)*[a-zA-Z]?((_alpha|_beta|_pre|_rc|_p)[0-9]*)*(-r[0-9]+)?$"

def process_environment_name(s):
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
### DICTIONARY GENERATION
######################################################################

# stores the mapping between names and ids
map_name_id = {'package': {}, 'flag': {}, 'slot': {}, 'subslot': {}, 'context': {}}

# stores the mapping between ids and names
map_id_name = {}

__id_current = 0
def __get_id():
    global __id_current
    __id_current = __id_current + 1
    return unicode(__id_current)

__map_update_lock = multiprocessing.RLock()
def update_map(kind, package, name):
    global __map_update_lock
    global __id_current
    global map_name_id
    global map_id_name
    __map_update_lock.acquire()
    if package not in map_name_id[kind]:
        update_map_spl(package)
    id = __get_id()
    map_name_id[kind][package][name] = id
    map_id_name[id] = {'type': kind, 'name': name, 'package': package}
    __map_update_lock.release()

def update_map_spl(name):
    if package not in map_name_id['package']:
        __map_update_lock.acquire()
        id = __get_id()
        map_name_id['package'][name] = id
        map_id_name[id] = {'type': 'package', 'name': name}
        map_name_id['flag'][name] = {}
        map_name_id['slot'][name] = {}
        map_name_id['subslot'][name] = {}
        __map_update_lock.release()


######################################################################
### TRANSLATION SIMPLIFICATION FUNCTIONS
######################################################################

def get_hyvar_or(ls):
    ls = [x for x in ls if x != "false"]
    if "true" in ls:
        return "true"
    s = "("
    if ls:
        s += "( " + ls[0] + ")"
        for i in ls[1:]:
            s += " or (" + i + ")"
    else:
        return "false"
    return s + ")"

def get_hyvar_and(ls):
    ls = [x for x in ls if x != "true"]
    if "false" in ls:
        return "false"
    s = "("
    if ls:
        s += "( " + ls[0] + ")"
        for i in ls[1:]:
            s += " and (" + i + ")"
    else:
        return "true"
    return s + ")"


def get_hyvar_impl(x,y):
    if x == "false" or y == "true":
        return "true"
    if y == "false":
        return "true"
    if x == "true":
        return "( " + y + ")"
    else:
        return "( " + x + " impl " + y + ")"

def get_hyvar_package(id):
    return "feature[p" + id + "]"

def get_hyvar_flag(id):
    return "feature[f" + id + "]"

def get_hyvar_context():
    return "context[c]"


def get_hyvar_slot(id):
    return "attribute[s" + id + "]"

def get_hyvar_subslot(id):
    return "attribute[ss" + id + "]"



