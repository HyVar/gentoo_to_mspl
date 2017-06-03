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
### ID GENERATION
######################################################################


__id_current = 0
__id_current_lock = multiprocessing.Lock()

def new_id():
    global __id_current
    global __id_current_lock
    with __id_current_lock:
        __id_current = __id_current + 1
    return unicode(__id_current)


def finish_map(target_dir):
    global map_name_id
    global map_id_name
    map_name_id = {'package': map_name_id_package,
        'flag': map_name_id_flag,
        'slot': map_name_id_slot,
        'subslot': map_name_id_subslot,
        'context': map_name_id_context }
    logging.info("Write map of names in " + utils.NAME_MAP_FILE)
    with open(os.path.join(target_dir, utils.NAME_MAP_FILE), 'w') as f:
        json.dump({"name_to_id": map_name_id, "id_to_name": map_id_name}, f)

            if not name.startswith("-"):
                if not name in map_name_id['context']:
                    map_name_id["context"][name] = len(map_name_id["context"])


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



