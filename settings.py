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

PACKAGE_NAME_SEPARATOR = '/'
TEMP_DIR = 'tmp'
NAME_MAP_FILE = 'name_maps.json'

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
    s = ""
    if ls:
        s += "( " + ls[0] + ")"
        for i in ls[1:]:
            s += " or (" + i + ")"
    else:
        return "false"
    return s

def get_hyvar_and(ls):
    s = ""
    if ls:
        s += "( " + ls[0] + ")"
        for i in ls[1:]:
            s += " and (" + i + ")"
    else:
        return "true"
    return s


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



