"""
settings.py: file containing some variables used by other modules 
"""
__author__ = "Jacopo Mauro"
__copyright__ = "Copyright 2017, Jacopo Mauro"
__license__ = "ISC"
__version__ = "0.1"
__maintainer__ = "Jacopo Mauro"
__email__ = "mauro.jacopo@gmail.com"
__status__ = "Prototype"

import re
import uuid
import threading

PACKAGE_NAME_SEPARATOR = '/'
TEMP_DIR = 'tmp'
NAME_MAP_FILE = 'name_maps.json'

ROOT_SPL_NAME ="__root__"


VERSION_RE = "-[0-9]+(\.[0-9]+)*[a-zA-Z]?((_alpha|_beta|_pre|_rc|_p)[0-9]*)*(-r[0-9]+)?$"

# List of the temp files.
TMP_FILES = []
TMP_FILES_LOCK = threading.Lock()

def get_new_temp_file(extension):
  global TMP_FILES_LOCK
  global TMP_FILES
  name = '/tmp/' + uuid.uuid4().hex + '.' + extension
  TMP_FILES_LOCK.acquire()
  TMP_FILES.append(name)
  TMP_FILES_LOCK.release()
  return name


id_count = 0
def get_new_id():
    global id_count
    id_count += 1
    return unicode(id_count)


def process_envirnoment_name(s):
    if s[0] == "~":  # testing env are equivalent for us to stable env
        return s[1:]
    return s


def get_hyvar_or(ls):
    ls = [x for x in ls if x != "false"]
    if "true" in ls:
        return "true"
    s = ""
    if ls:
        s += "( " + ls[0] + ")"
        for i in ls[1:]:
            s += " or (" + i + ")"
    else:
        return "false"
    return s

def get_hyvar_and(ls):
    ls = [x for x in ls if x != "true"]
    if "false" in ls:
        return "false"
    s = ""
    if ls:
        s += "( " + ls[0] + ")"
        for i in ls[1:]:
            s += " and (" + i + ")"
    else:
        return "true"
    return s


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



