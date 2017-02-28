"""
gentoo_rec.py:

Tool to convert the prepocessed gentoo files

Usage: gentoo_rec.py <directory containing the mspl and spl directories> <output directory>
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
import dep_translator
import getopt


# Global variables

# stores the mapping between names and ids
map_name_id = {"package": {}, "flag": {}, "slot": {}, "subslot": {}, "context": {}}

# stores the mapping between ids and names
map_id_name = {}

# stores the json info related to the mspl and spl produced processing the gentoo files
mspl = {}
spl = {}


# logging.basicConfig(filename='example.log',level=log.DEBUG)
logging.basicConfig(level=logging.DEBUG)

def usage():
    """Print usage"""
    print(__doc__)


def is_base_package(package):
    """
    :param package: name of the package
    :return: true if the name of the package is not a version
    """
    return "implementations" in mspl[package]

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


def load_spl(spl_dir):
    """
    loads in memory the json files of the mspl in the directory mspl_dir
    """
    global spl
    dirs = os.listdir(spl_dir)
    for i in dirs:
        logging.debug("Loading json files from dir " + i)
        files = os.listdir(os.path.join(spl_dir,i))
        for f in files:
            spl[i + settings.PACKAGE_NAME_SEPARATOR + re.sub('\.json$','',f)] = read_json(os.path.join(spl_dir,i,f))
            # TODO ask michael to avoid to generate this info
            del(spl[i + settings.PACKAGE_NAME_SEPARATOR + re.sub('\.json$','',f)]["dependencies"])


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
        map_name_id["flag"][i] = {}
        map_name_id["slot"][i] = {}
        map_name_id["subslot"][i] = {}
        if not is_base_package(i):
            # add flags
            for j in spl[i]["features_used"]["external"].values():
                for k in j:
                    if k not in map_name_id["flag"][i]:
                        id = settings.get_new_id()
                        map_name_id["flag"][i][k] = id
                        map_id_name[id] = {"type": "flag", "name": k, "package": i}
            for j in spl[i]["features_used"]["local"]:
                id = settings.get_new_id()
                map_name_id["flag"][i][j] = id
                map_id_name[id] = {"type": "flag", "name": j, "package": i}
            # add slots and subslots
            j = mspl[i]["features"]["__main__"]
            # process slots (conversion from name into a range of integers)
            counter = 0
            for k in mspl[i]["features"]["__main__"]["slots"]:
                map_name_id["slot"][i][k] = counter
                counter += 1
            # process subslots (conversion from name into a range of integers)
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

    assert mspl
    if not package in mspl:
        raise Exception("Package " + package + " not found in the MSPL JSON files")

    data = {"attributes": [], "constraints": [], "configures": mspl[package]["configures"],
            "dependencies": mspl[package]["dependencies"]}

    if is_base_package(package):
        versions = mspl[package]["implementations"].values()
        # if installed then one of its version should be installed as well
        data["constraints"].append(
            settings.get_hyvar_package(map_name_id["package"][package]) +
            " = 1 impl (" +
            settings.get_hyvar_or([settings.get_hyvar_package(map_name_id["package"][i]) for i in versions]) + ")")
        # two versions should have different slots or subslots
        for i in versions:
            for j in versions:
                if i < j:
                    data["constraints"].append(
                        "( " + settings.get_hyvar_package(map_name_id["package"][i]) + "= 1 and " +
                        settings.get_hyvar_package(map_name_id["package"][j]) + " = 1) impl (" +
                        settings.get_hyvar_slot(map_name_id["package"][i]) + " != " +
                        settings.get_hyvar_slot(map_name_id["package"][i]) + " or " +
                        settings.get_hyvar_subslot(map_name_id["package"][i]) + " != " +
                        settings.get_hyvar_subslot(map_name_id["package"][i]) + ")")

    else:

        # add slot and subslot as attributes
        assert len(map_name_id["slot"][package]) > 0
        assert len(map_name_id["subslot"][package]) > 0

        data["attributes"].append( {
            "id": settings.get_hyvar_slot(map_name_id["package"][package]),
            "min": 0,
            "max": len(map_name_id["slot"][package]) -1,
            "featureId": settings.get_hyvar_package(map_name_id["package"][package])})

        data["attributes"].append({
            "id": settings.get_hyvar_subslot(map_name_id["package"][package]),
            "min": 0,
            "max": len(map_name_id["subslot"][package]) - 1,
            "featureId": settings.get_hyvar_package(map_name_id["package"][package])})

        # add constraints
        assert "fm" in mspl[package]
        assert "external" in mspl[package]["fm"]
        assert "local" in mspl[package]["fm"]
        visitor = dep_translator.DepVisitor(mspl, map_name_id, package)
        if mspl[package]["fm"]["external"]:
            parser = visitor.parser(mspl[package]["fm"]["external"])
            tree = parser.depend()
            visitor.visit(tree)
        if mspl[package]["fm"]["local"]:
            parser = visitor.parser(mspl[package]["fm"]["local"])
            tree = parser.localDEP()
            visitor.visit(tree)
        data["constraints"].extend(visitor.constraints)

    # add validity formulas. Context must be one of the possible env
    ls = set([ map_name_id["context"][settings.process_envirnoment_name(x)] for x in mspl[package]["environment"]])
    data["constraints"].append(
        settings.get_hyvar_package(map_name_id["package"][package]) + " = 1 impl (" +
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

    global map_name_id
    global map_id_name
    global mspl
    try:
        opts, args = getopt.getopt(argv,"hv",["help","verbose"])
    except getopt.GetoptError as err:
        print str(err)
        usage()
        sys.exit(1)
    for opt, arg in opts:
        if opt == '-h':
            usage()
            sys.exit()
        elif opt in ("-v", "--verbose"):
            logging.basicConfig(format="%(levelname)s: %(message)s", level=logging.DEBUG)
            logging.info("Verbose output.")

    if len(args) != 2:
      print "2 argument are required"
      print(__doc__)
      sys.exit(1)

    input_dir = os.path.abspath(args[0])
    target_dir = os.path.abspath(args[1])

    logging.info("Load the MSPL. This may take a while")
    load_mspl(os.path.join(input_dir,'mspl'))
    logging.info("Load the SPL. This may take a while")
    load_spl(os.path.join(input_dir,'spl'))

    if os.path.isfile(os.path.join(target_dir,settings.NAME_MAP_FILE)):
        logging.info("Use the exising " + settings.NAME_MAP_FILE + " file. No computation of new ids")
        data = read_json(os.path.join(target_dir,settings.NAME_MAP_FILE))
        map_name_id = data["name_to_id"]
        map_id_name = data["id_to_name"]
    else:
        logging.info("Generate the name maps for packages and stores in a file")
        generate_name_mapping_file(target_dir)

    logging.info("Start converting files of the MSPL. Skipping existing ones")

    # test instances

    # convert("games-kids/gcompris-15.10", target_dir)
    # convert("dev-java/jython-2.7.0", target_dir)
    # convert("dev-texlive/texlive-latexextra-2014", target_dir) -> no pacchetti
    # exit(0)

    counter = 0
    for i in mspl.keys():
        if not os.path.isfile(os.path.join(target_dir,i+".json")):
            logging.debug("Processing package " + i)
            convert(i, target_dir)
            counter += 1
            # if counter == 100:
            #     exit(0)

if __name__ == "__main__":
    main(sys.argv[1:])