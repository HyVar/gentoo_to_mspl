"""
gentoo_rec.py:

Tool to convert the prepocessed gentoo files

Usage: gentoo_rec.py ...
"""
__author__ = "Jacopo Mauro"
__copyright__ = "Copyright 2017, Jacopo Mauro"
__license__ = "ISC"
__version__ = "0.1"
__maintainer__ = "Jacopo Mauro"
__email__ = "mauro.jacopo@gmail.com"
__status__ = "Prototype"


import json
import uuid
import sys
import settings
import logging
import os
import tarfile
import re


# Global variables

# stores the mapping between names and ids
map_name_id = {"package": {}, "flag": {}, "slot": {}, "subslot": {}, "context": {}}

# stores the mapping between ids and names
map_id_name = {}

# stores the json info related to the mspl produced processing the gentoo files
mspl = {}


# logging.basicConfig(filename='example.log',level=log.DEBUG)
logging.basicConfig(level=logging.DEBUG)

def usage():
    """Print usage"""
    print(__doc__)


def read_json(json_file):
    """
    loads the json file
    """
    with open(json_file) as data_file:
        data = json.load(data_file)
    return data


def load_mspl(mspl_dir):
    """
    loads in memory the json files of the mspl in the directory mspl_dir
    """

    global mspl
    dirs = os.listdir(mspl_dir)
    for i in dirs:
        logging.debug("Loading json files from dir " + i)
        files = os.listdir(os.path.join(mspl_dir,i))
        for f in files:
            mspl[i + settings.PACKAGE_NAME_SEPARATOR + re.sub('\.json$','',f)] = read_json(os.path.join(mspl_dir,i,f))


def generate_name_mapping_file(target_dir):
    """
    Generates the name mapping file
    Requires the load of the mspl
    """
    global mspl
    global map_name_id
    global map_id_name
    for i in mspl.keys():
        id = settings.get_new_id()
        map_name_id["package"][i] = id
        map_id_name[id] = {"type": "package", "name": i}
    logging.info("Generate the name maps for flags, domain for slots, subslots and environment")
    for i in mspl.keys():
        for j in mspl[i]["features"].keys():
            if j != "__main__":
                id = settings.get_new_id()
                map_name_id["flag"][i] = {}
                map_name_id["flag"][i][j] = id
                map_id_name[id] = {"type": "flag", "name": j, "package": i}
            else:
                # process slots (conversion from name into a range of integers)
                map_name_id["slot"][i] = {}
                counter = 0
                for k in mspl[i]["features"]["__main__"]["slots"]:
                    map_name_id["slot"][i][k] = counter
                    counter += 1
                # process slots (conversion from name into a range of integers)
                map_name_id["subslot"][i] = {}
                counter = 0
                for k in mspl[i]["features"]["__main__"]["subslots"]:
                    map_name_id["subslot"][i][k] = counter
                    counter += 1
        # process environment (conversion from name into a range of integers)
        for j in mspl[i]["environment"]:
            name = settings.process_envirnoment_name(j)
            if not name in map_name_id["context"]:
                map_name_id["context"][name] = len(map_name_id["context"])
    logging.info("Write map of names in " + settings.NAME_MAP_FILE)
    with open(os.path.join(target_dir, settings.NAME_MAP_FILE), 'w') as f:
        json.dump({"name_to_id": map_name_id, "id_to_name": map_id_name}, f)


def convert(package,target_dir):

    data = { "attributes": [], "constraints": [] }

    # add slot and subslot as attributes
    # TODO

    # process constraints
    # TODO

    # add validity formulas. Context must be one of the possible env
    ls = set([ map_name_id["context"][settings.process_envirnoment_name(x)] for x in mspl[package]["environment"]])
    data["constraints"].append(
        settings.get_hyvar_package(map_name_id["package"][package]) + " = 1 imply (" +
        settings.get_hyvar_or( [ settings.get_hyvar_context() + " = " + unicode(x) for x in ls]) + ")")

    logging.debug("Writing file " + os.path.join(target_dir, package + ".json"))
    d = package.split(settings.PACKAGE_NAME_SEPARATOR)[0]
    if not os.path.exists(os.path.join(target_dir,d)):
        os.makedirs(os.path.join(target_dir,d))
    with open(os.path.join(target_dir, package + ".json"), 'w') as f:
        json.dump(data, f, indent=1)



def main(argv):
    """
    Main procedure
    """

    mspl_dir = "in"
    target_dir = "out"
    global map_name_id
    global map_id_name
    global mspl
    # try:
    #   opts, args = getopt.getopt(argv,"ho:vks:d:",["help","ofile=","verbose","keep","solver","dotfiles"])
    # except getopt.GetoptError as err:
    #   print str(err)
    #   usage()
    #   sys.exit(1)
    # for opt, arg in opts:
    #   if opt == '-h':
    #     usage()
    #     sys.exit()
    #   elif opt in ("-o", "--ofile"):
    #     output_file = arg
    #   elif opt in ("-k", "--keep"):
    #     global KEEP
    #     KEEP = True
    #   elif opt in ("-v", "--verbose"):
    #     log.basicConfig(format="%(levelname)s: %(message)s", level=log.DEBUG)
    #     log.info("Verbose output.")
    #   elif opt in ("-s", "--solver"):
    #     if arg == 'chuffed':
    #       zephyrus_solver = 'lex-chuffed'
    #     elif arg == 'smt':
    #       zephyrus_solver = 'smt'
    #     elif arg == 'gecode':
    #       zephyrus_solver = 'lex-gecode'
    #     else:
    #       print "Solver not recognized"
    #       usage()
    #       sys.exit(1)
    #   elif opt in ('-d', '--dotfiles'):
    #     dot_file_prefix = arg

    # if len(args) < 1:
    #   print "1 argument is required"
    #   usage()
    #   sys.exit(1)

    logging.info("Load the MSPL. This may take a while")
    load_mspl(os.path.join(mspl_dir,'mspl'))

    if os.path.isfile(os.path.join(target_dir,settings.NAME_MAP_FILE)):
        logging.info("Use the exising " + settings.NAME_MAP_FILE + " file. No computation of new ids")
        data = read_json(os.path.join(target_dir,settings.NAME_MAP_FILE))
        map_name_id = data["name_to_id"]
        map_id_name = data["id_to_name"]
    else:
        logging.info("Generate the name maps for packages and stores in a file")
        generate_name_mapping_file(target_dir)

    logging.info("Start converting files of the MSPL. Skipping existing ones")
    for i in mspl.keys():
        if not os.path.isfile(os.path.join(target_dir,i+".json")):
            logging.debug("Processing package " + i)
            convert(i, target_dir)

if __name__ == "__main__":
    main(sys.argv[1:])