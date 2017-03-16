"""
reconfigure.py:

Tool that taking in input the gentoo mspl calls hyvar-rec producing a valid configuration, if any

Usage: reconfigure.py [options] <directory containing the mspl> <request package list> <configuration_file> <environment>
 --url url of the hyvar-rec service (e.g. http://158.37.63.154:80)
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
import requests

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
    Run hyvar locally assuming that there is a command hyvar-rec
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

def run_remote_hyvar(json_data,url):
    """
    Run hyvar
    """
    logging.debug("Invoking service at url " + url)
    response = requests.post(url + "/explain",
                             data=json.dumps(json_data),
                             headers={'content-type': 'application/json'})
    return response.json()


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


def create_hyvarrec_spls(package_request,initial_configuration,contex_value,no_selected_pkgs):
    """
    Given a list of packages it creates its hyvarrec SPL
    """
    # todo handle intial configuration
    # read list of configures and depends for all packages

    spls = {}
    dconf = {}
    ddep = {}
    for i in [x[0] for x in package_request]:
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
                "preferences": [],
                "smt_constraints": {
                    "formulas": [],
                    "features": [],
                    "other_int_symbols": [] }
                }

        # process configures
        other_symbols = set()
        feature_symbols = set()
        for j in dconf[i]:
            json["attributes"].extend(mspl[j]["attributes"])
            json["constraints"].extend(mspl[j]["constraints"])
            if "smt_constraints" in mspl[j]:
                json["smt_constraints"]["formulas"].extend(mspl[j]["smt_constraints"]["formulas"])
                other_symbols.update(mspl[j]["smt_constraints"]["other_int_symbols"])
                print mspl[j]["smt_constraints"]["features"]
                print j
                feature_symbols.update(mspl[j]["smt_constraints"]["features"])
        # if other_symbols:
        json["smt_constraints"]["other_int_symbols"] = list(other_symbols)
        # if feature_symbols:
        json["smt_constraints"]["features"] = list(feature_symbols)

        # the constraints added should also require the depends, if any.
        # hence, no need to add additional constraints for them

        # add constraints to impose selection of requested packages
        for j in package_request:
            p = j[0]
            if p in dconf[i]: # packages needs to be configured
                if len(j) == 1:
                    json["constraints"].append(settings.get_hyvar_package(map_name_id["name_to_id"]["package"][p]) + " = 1")
                elif len(j) == 2: # the package requires a specific subslot
                    vs = [x for x in mspl[re.sub(settings.VERSION_RE, "", p)]["implementations"].values()
                          if j[1] in map_name_id["name_to_id"]["slot"][x]]
                    # here we assume that a version can be installed only in one slots
                    c = settings.get_hyvar_or(
                        [settings.get_hyvar_package(map_name_id["name_to_id"]["package"][x]) + " = 1" for x in vs])
                    if c == "false":
                        logging.error("Package " + p + " can not be installed with subslot " + j[1] + ". Existing.")
                        exit(1)
                    json["constraints"].append(c)
                else: # slot and subslot
                    vs = [x for x in mspl[re.sub(settings.VERSION_RE, "", p)]["implementations"].values()
                          if j[1] in map_name_id["name_to_id"]["slot"][x] and j[2] in map_name_id["name_to_id"]["subslot"][x]]
                    # here we assume that a version can be installed only in one slots + subslot
                    c = settings.get_hyvar_or(
                        [settings.get_hyvar_package(map_name_id["name_to_id"]["package"][x]) + " = 1" for x in vs])
                    if c == "false":
                        logging.error("Package " + p + " can not be installed with subslot " + j[1] + " and subslot "+
                            j[2] + ". Existing.")
                        exit(1)
                    json["constraints"].append(c)

        # add constraints to impose deselection of not selected packages
        for j in no_selected_pkgs:
            if j in dconf[i] or j in ddep[i]:
                json["constraints"].append(
                    settings.get_hyvar_package(map_name_id["name_to_id"]["package"][j]) + " = 0")

        # add info about the initial configuration
        for j in initial_configuration.keys():
            if j in dconf[i]:
                json["configuration"]["selectedFeatures"].append(
                    settings.get_hyvar_package(map_name_id["name_to_id"]["package"][j]))
                for k in initial_configuration[j]:
                    json["configuration"]["selectedFeatures"].append(
                        settings.get_hyvar_flag(map_name_id["name_to_id"]["flag"][j][k]))
            elif j in ddep[i]:
                json["configuration"]["selectedFeatures"].append(
                    settings.get_hyvar_package(map_name_id["name_to_id"]["package"][j]))


        logging.debug("SPL created : attributes " + unicode(len(json["attributes"])) +
                      ", constraints " + unicode(len(json["constraints"])) +
                      ", smt formulas " + unicode(len(json["smt_constraints"]["formulas"])) +
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
    global KEEP
    url = ""

    try:
        opts, args = getopt.getopt(argv,"hvk",["help","verbose", "keep","url="])
    except getopt.GetoptError as err:
        print str(err)
        print(__doc__)
        sys.exit(1)
    for opt, arg in opts:
        if opt in ("-h", "--help"):
            print(__doc__)
            sys.exit()
        if opt in ("-k", "--keep"):
            KEEP = True
        if opt in ("--url"):
            url = arg
        elif opt in ("-v", "--verbose"):
            logging.basicConfig(format="%(levelname)s: %(message)s", level=logging.DEBUG)
            logging.info("Verbose output.")

    if len(args) != 4:
       print "4 argument are required, " + unicode(len(args)) + " found"
       print(__doc__)
       sys.exit(1)

    input_dir = os.path.abspath(args[0])
    request_file = os.path.abspath(args[1])
    configuration_file = os.path.abspath(args[2])
    environment = args[3]

    logging.info("Load the MSPL. This may take a while.")
    load_mspl(input_dir)

    logging.info("Load the mapping between names and ids. This may take a while.")
    map_name_id = read_json(os.path.join(input_dir,settings.NAME_MAP_FILE))

    logging.info("Load the request package list.")
    lines = [x.strip().split(":") for x in open(request_file,"r").read().split() if x.strip() != ""]
    # todo Allow the possibility to require packages in a specific slot/subslot or version
    package_request = []
    for i in lines:
        assert i
        if i[0] not in mspl:
            logging.warning("The requested package " + i + " is not found and will be ignored.")
        else:
            if len(i) > 1:
                package_request.append([i[0]] + i[1].split("/"))
            else:
                package_request.append(i)

    logging.info("Load the configuration file.")
    initial_configuration = read_json(configuration_file)
    for i in initial_configuration.keys():
        if i in mspl:
            initial_configuration[i] = [x[1:] for x in initial_configuration[i]
                                        if x.startswith("+") and x[1:] in map_name_id["name_to_id"]["flag"][i]]
        else:
            logging.warning("Not found the package " + i + " defined in the initial configuration.")
            del(initial_configuration[i])


    logging.info("Process the MSPL based on its dependencies graph")
    utils.preprocess(mspl,initial_configuration,set([x[0] for x in package_request]))

    # start solving the reconfiguration problem for the package_requests
    configuration = {}
    confs_deselected = set()
    deps_selected = set()
    # todo remove reverse list (just for testing purposes)
    to_solve = list(reversed(create_hyvarrec_spls(package_request,initial_configuration,environment,confs_deselected)))

    while to_solve:
        job = to_solve.pop()
        if url:
            json_result = run_remote_hyvar(job["json"],url)
        else:
            json_result = run_hyvar(job["json"])
        logging.debug("Answer obtained: " + unicode(json_result))
        if json_result["result"] != "sat":
            logging.error("Conflict detected. Impossible to satisfy the request. Exiting.")
            exit(1)
        # update the info on the final configuration
        update_configuration(json_result,configuration)
        confs_deselected.update([x for x in job["confs"] if x not in configuration])
        confs_deselected.update([x for x in job["deps"] if x not in configuration])
        deps_selected.update(job["deps"])
        if deps_selected:
            deps_selected.difference_update(configuration.keys())
        if deps_selected:
            deps_selected.difference_update(confs_deselected)
        logging.debug("Remaining number of dependencies: " + unicode(len(deps_selected)))
        # run hyvarrec on the remaining dependencies selected (deep first search of the MSPL)
        if deps_selected:
            p = deps_selected.pop()
            logging.debug("Attemping to configure dependency " + p)
            ls = create_hyvarrec_spls([[p]],initial_configuration,environment,confs_deselected)
            assert len(ls) == 1
            to_solve.append(ls[0])

    print json.dumps(configuration,indent=1)

    logging.info("Cleaning.")
    clean()
    logging.info("Execution terminated correctly.")



if __name__ == "__main__":
    main(sys.argv[1:])