"""
reconfigure.py:

Tool that taking in input the gentoo mspl calls hyvar-rec producing a valid configuration, if any

Usage: reconfigure.py <directory containing the mspl> <request package list> <configuration_file> <environment>
"""
__author__ = "Jacopo Mauro"
__copyright__ = "Copyright 2017, Jacopo Mauro"
__license__ = "ISC"
__version__ = "0.1"
__maintainer__ = "Jacopo Mauro"
__email__ = "mauro.jacopo@gmail.com"
__status__ = "Prototype"


import json
import sys
import settings
import logging
import os
import re
import utils
import getopt
from subprocess import Popen,PIPE
import psutil

# Global variables

# stores the json info related to the mspl produced processing the gentoo files
mspl = {}

# stores the mapping between names and ids
map_name_id = {}

# keep temporary files
KEEP = False

def clean():
  """
  Utility for (possibly) cleaning temporary files
  """
  if not KEEP:
    settings.TMP_FILES_LOCK.acquire()
    for f in settings.TMP_FILES:
      if os.path.exists(f):
        os.remove(f)
    settings.TMP_FILES_LOCK.release()

def read_json(json_file):
    """
    loads the json file
    """
    with open(json_file) as data_file:
        data = json.load(data_file)
    return data


def run_hyvar(json_data):
    """
    Run hyvar
    """
    file_name = settings.get_new_temp_file("json")
    with open(file_name,"w") as f:
        json.dump(json_data, f)
    cmd = ["hyvar-rec", "--explain", file_name]
    logging.debug("Running command " + unicode(cmd))
    process = psutil.Popen(cmd,stdout=PIPE,stderr=PIPE)
    out, err = process.communicate()
    logging.debug('Stdout of ' + unicode(cmd))
    logging.debug(out)
    logging.debug('Stderr of ' + unicode(cmd))
    logging.debug(err)
    logging.debug('Return code of ' + unicode(cmd) + ': ' + str(process.returncode))
    return json.loads(out)

def load_mspl(mspl_dir):
    """
    loads in memory the json files of the mspl in the directory mspl_dir
    """
    global mspl
    dirs = os.listdir(mspl_dir)
    for i in dirs:
        logging.debug("Loading json files from dir " + i)
        if os.path.isdir(os.path.join(mspl_dir,i)):
            files = os.listdir(os.path.join(mspl_dir,i))
            for f in files:
                name = i + settings.PACKAGE_NAME_SEPARATOR + re.sub('\.json$','',f)
                mspl[name] = read_json(os.path.join(mspl_dir,i,f))


def get_all_dependencies(pkg):
    base_pkg = re.sub(settings.VERSION_RE, "",pkg)
    configures = set(mspl[base_pkg]["loop"] + mspl[base_pkg]["descendants"])
    # add the packages with versions
    for j in list(configures):
        configures.update(mspl[j]["implementations"].values())
    depends = set()
    for j in configures:
        depends.update(mspl[j]["dependencies"])
    depends.difference_update(configures)
    return configures,depends


def create_hyvarrec_spls(package_request,contex_value,no_selected_pkgs):
    """
    Given a list of packages it creates its hyvarrec SPL
    """
    # todo handle intial configuration
    # read list of configures and depends for all packages

    spls = {}
    dconf = {}
    ddep = {}
    for i in package_request:
        dconf[i],ddep[i] = get_all_dependencies(i)
        spls[i] = dconf[i].union(ddep[i])

        intersections = [x for x in spls.keys() if spls[i].intersection(spls[x]) and x != i]
        if intersections:
            pivot = intersections.pop()
            for j in intersections + [i]:
                spls[pivot].update(spls[j])
                dconf[pivot].update(dconf[j])
                ddep[pivot].update(ddep[j])
                del(spls[j])
                del(dconf[j])
                del(ddep[j])


    logging.debug("SPLs to generate: " + unicode(len(spls)))

    jsons = []
    for i in spls.keys():
        json = {"attributes": [],
                "contexts": [{"id": settings.get_hyvar_context(),
                              "min": 0,
                              "max": len(map_name_id["name_to_id"]["context"])-1}],
                "configuration": {
                    "selectedFeatures": [],
                    "attribute_values": [],
                    "context_values": [{"id": settings.get_hyvar_context(),
                                        "value": map_name_id["name_to_id"]["context"][contex_value]}]},
                "constraints": [],
                "preferences": []}

        # process configures
        for j in dconf[i]:
            json["attributes"].extend(mspl[j]["attributes"])
            json["constraints"].extend(mspl[j]["constraints"])
        # the constraints added should also require the depends, if any.
        # hence, no need to add additional constraints for them
        # add constraints to impose selection of requested packages
        for j in package_request:
            if j in dconf[i]:
                json["constraints"].append(settings.get_hyvar_package(map_name_id["name_to_id"]["package"][j]) + " = 1")
        # add constraints to impose deselection of not selected packages
        for j in no_selected_pkgs:
            if j in dconf[i] or j in ddep[i]:
                json["constraints"].append(
                    settings.get_hyvar_package(map_name_id["name_to_id"]["package"][j]) + " = 0")

        logging.debug("SPL created : attributes " + unicode(len(json["attributes"])) +
                      ", constraints " + unicode(len(json["constraints"])) +
                      ", packages to configure " + unicode(len(spls[i])))

        ddep[i].difference_update(dconf[i])
        if ddep[i]:
            logging.debug("Dependencies not in configure: " + unicode(len(ddep[i])))
        jsons.append({"json":json, "confs": dconf[i],"deps": ddep[i]})

    return jsons


def update_configuration(hyvarrec_out,configuration):
    pkgs = []
    flags = []
    for i in hyvarrec_out["features"]:
        el = map_name_id["id_to_name"][i[1:]]
        if el["type"] == "package":
            pkgs.append(el["name"])
        else: # "type" == "flag"
            flags.append((el["package"],el["name"]))

    for p in pkgs:
        if p not in configuration:
            configuration[p] = []
    for p,f in flags:
        if p not in configuration:
            logging.error("The output of hyvar-rec sets the flag " + f + " but its package " + p +
                          " was not selected.")
        else:
            configuration[p].append(f)


def main(argv):
    """
    Main procedure
    """

    global map_name_id
    global mspl
    try:
        opts, args = getopt.getopt(argv,"hv",["help","verbose"])
    except getopt.GetoptError as err:
        print str(err)
        print(__doc__)
        sys.exit(1)
    for opt, arg in opts:
        if opt == '-h':
            print(__doc__)
            sys.exit()
        elif opt in ("-v", "--verbose"):
            logging.basicConfig(format="%(levelname)s: %(message)s", level=logging.DEBUG)
            logging.info("Verbose output.")

    # if len(args) != 2:
    #   print "2 argument are required"
    #   print(__doc__)
    #   sys.exit(1)
    #
    input_dir = os.path.abspath(args[0])
    request_file = os.path.abspath(args[1])
    configuration_file = os.path.abspath(args[2])
    environment = args[3]

    logging.info("Load the MSPL. This may take a while.")
    load_mspl(input_dir)

    logging.info("Load the mapping between names and ids. This may take a while.")
    map_name_id = read_json(os.path.join(input_dir,settings.NAME_MAP_FILE))

    logging.info("Load the request package list.")
    package_request = [x.strip() for x in open(request_file,"r").read().split() if x.strip() != ""]
    # todo Allow the possibility to require packages in a specific slot/subslot or version
    package_request = [re.sub(":.*$", "",x) for x in package_request]
    package_request = set([x for x in package_request if x in mspl])
    logging.debug("Packages required: " + unicode(package_request))

    non_valid_requests = [x for x in package_request if x not in mspl]
    if non_valid_requests:
        logging.warning("The requested packages " + unicode(non_valid_requests) +
                        " are not found and they will be ignored.")

    logging.info("Load the configuration file.")
    initial_configuration = read_json(configuration_file)

    # logging.info("Generate the root of the MSPL")
    # mspl[settings.ROOT_SPL_NAME] = generate_root_spl(package_request)

    logging.info("Process the MSPL based on its dependencies graph")
    utils.preprocess(mspl,initial_configuration,package_request)

    # start solving the reconfiguration problem for the package_requests
    configuration = {}
    confs_deselected = set()
    deps_selected = set()
    to_solve = create_hyvarrec_spls(package_request, environment,confs_deselected)

    while to_solve:
        json_result = run_hyvar(to_solve[0]["json"])
        if json_result["result"] != "sat":
            logging.error("Conflict detected. Impossible to satisfy the request. Exiting.")
            exit(1)
        # update the info on the final configuration
        update_configuration(json_result,configuration)
        confs_deselected.update([x for x in to_solve[0]["confs"] if x not in configuration])
        confs_deselected.update([x for x in to_solve[0]["deps"] if x not in configuration])
        deps_selected.update(to_solve[0]["deps"])
        if deps_selected:
            deps_selected.difference_update(configuration.keys())
        if deps_selected:
            deps_selected.difference_update(confs_deselected)
        logging.debug("Remaining number of dependency: " + unicode(len(deps_selected)))
        # run hyvarrec on the remaining dependencies selected (deep first search of the MSPL)
        if deps_selected:
            p = deps_selected.pop()
            logging.debug("Attemping to configure dependency " + p)
            ls = create_hyvarrec_spls([p], environment,confs_deselected)
            assert len(ls) == 1
            to_solve.insert(0,ls[0])






    # with open('/tmp/prova.json', 'w') as f:
    #     json.dump(spls[0],f,indent=1)




    # if os.path.isfile(os.path.join(target_dir,settings.NAME_MAP_FILE)):
    #     logging.info("Use the exising " + settings.NAME_MAP_FILE + " file. No computation of new ids")
    #     data = read_json(os.path.join(target_dir,settings.NAME_MAP_FILE))
    #     map_name_id = data["name_to_id"]
    #     map_id_name = data["id_to_name"]
    # else:
    #     logging.info("Generate the name maps for packages and stores in a file")
    #     generate_name_mapping_file(target_dir)

    logging.info("Execution terminated correctly.")



if __name__ == "__main__":
    main(sys.argv[1:])