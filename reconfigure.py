"""
reconfigure.py:

Tool that taking in input the gentoo mspl calls hyvar-rec producing a valid configuration, if any

Usage: reconfigure.py <directory containing the mspl> <request package list> <configuration_file>
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

# Global variables

# stores the json info related to the mspl produced processing the gentoo files
mspl = {}

# stores the mapping between names and ids
map_name_id = {}


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
        if os.path.isdir(os.path.join(mspl_dir,i)):
            files = os.listdir(os.path.join(mspl_dir,i))
            for f in files:
                name = i + settings.PACKAGE_NAME_SEPARATOR + re.sub('\.json$','',f)
                mspl[name] = read_json(os.path.join(mspl_dir,i,f))



def generate_root_spl(spls):
    json = {"attributes": [], "dependencies": [], "configures": [], "constraints": []}
    for i in spls:
        name = re.sub(":.*$","",i)
        if name in mspl:
            json["dependencies"].append(name)
        else:
            logging.warning("The package " + name + " requested can not be found. Skipping.")
    json["configures"] = json["dependencies"]
    json["constraints"].append(settings.get_hyvar_and(
        [settings.get_hyvar_package(map_name_id["name_to_id"]["package"][i]) + " = 1" for i in json["configures"]]))
    return json


def get_conf_and_dep(pkg):
    """
    Based on the graph analyisis this procedure list all the packages to include in the SPL for full or just as
    a dependency
    """
    configures = set(mspl[pkg]["configures"])
    for i in mspl[pkg]["include"]:
        configures.update([i])
        configures.update(mspl[i]["implementations"].values())
    depends = set(mspl[pkg]["dependencies"])
    for i in depends.copy():
        depends.update(mspl[i]["dependencies"])
    return configures,depends.difference_update(configures)


def create_hyvarrec_spl(pkg,contex_value):
    """
    Given a name of the package it creates its hyvarrec SPL
    """
    # todo handle intial configuration
    configures, depends = get_conf_and_dep(pkg)
    configures.update([pkg])
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
    for i in configures:
        json["attributes"].extend(mspl[i]["attributes"])
        json["constraints"].extend(mspl[i]["constraints"])
    # the constraints added should also require the depends, if any.
    # hence, no need to add additional constraints for them
    logging.debug("SPL of package " + pkg + " created: attributes " + unicode(len(json["attributes"])) +
                  ", constraints " + unicode(len(json["constraints"])) +
                  ", packages to configure " + unicode(len(configures)))
    if depends:
        logging.debug("Dependencies not in configure: " + unicode(len(depends)))

    return json


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

    logging.info("Load the MSPL. This may take a while.")
    load_mspl(input_dir)

    logging.info("Load the mapping between names and ids. This may take a while.")
    map_name_id = read_json(os.path.join(input_dir,settings.NAME_MAP_FILE))

    logging.info("Load the request package list.")
    package_request = [x.strip() for x in open(request_file,"r").read().split() if x.strip() != ""]
    # todo Allow the possibility to require packages in a specific slot/subslot
    package_request = [re.sub(":.*$", "",x) for x in package_request]
    package_request = [x for x in package_request if x in mspl]
    non_valid_requests = [x for x in package_request if x not in mspl]
    if non_valid_requests:
        logging.warning("The requested packages " + unicode(non_valid_requests) +
                        " are not found and they will be ignored.")

    logging.info("Load the configuration file.")
    initial_configuration = read_json(configuration_file)

    logging.info("Generate the root of the MSPL")
    mspl[settings.ROOT_SPL_NAME] = generate_root_spl(package_request)

    logging.info("Process the MSPL based on its dependencies graph")
    utils.preprocess(mspl,initial_configuration)

    spl = create_hyvarrec_spl(settings.ROOT_SPL_NAME,"x86")
    with open('/tmp/prova.json', 'w') as f:
        json.dump(spl, f,indent=1)



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