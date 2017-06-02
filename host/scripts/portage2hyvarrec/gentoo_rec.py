"""
gentoo_rec.py:

Tool to convert the prepocessed gentoo files

Usage: gentoo_rec.py <options> <directory containing the mspl and spl directories> <output directory>
    --no_opt: disable the conversion in SMTLIB of the formulas
    -p --par: cores to use
"""
__author__ = "Michael Lienhardt & Jacopo Mauro"
__copyright__ = "Copyright 2017, Michael Lienhardt & Jacopo Mauro"
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
import z3
import SpecificationGrammar.SpecTranslator as SpecTranslator
import multiprocessing

def usage():
    """Print usage"""
    print(__doc__)


#####################################################################################
### GLOBAL VARVIABLES
#####################################################################################

# stores the mapping between names and ids
map_name_id = {'package': {}, 'flag': {}, 'slot': {}, 'subslot': {}, 'context': {}}

# stores the mapping between ids and names
map_id_name = {}

# stores the json info related to the mspl produced processing the gentoo files
mspl = {}
# stores the package group
pgroups = set()

## TOOL SETTINGS
# encode into z3 SMT representation directly
to_smt = True
# trust feature declaration in portage file
trust_feature_declaration = True
# number of core to use
available_core = 3

######################################################################
### FUNCTIONS UTILS
######################################################################

def structure_filename(filename):
    """
    this function splits a portage md5-cache filename into relevant information
    """
    filename_split = filename.split("-")
    tmp = filename_split[-1]
    if tmp.startswith("r"):
        revision = tmp
        version = filename_split[-2]
        del filename_split[-2:]
        version_all = version + "-" + revision
    else:
        revision = "r0"
        version = filename_split[-1]
        del filename_split[-1]
        version_all = version
    package = "-".join(filename_split)
    return (package, version_all, version, revision)

def get_egencache_files(path):
    """
    returns the set of portage files to load
    """
    files = []
    for root, dirnames, filenames in os.walk(path):
        files.extend([os.path.join(root, filename)] for filename in filenames)
    return files

def is_base_package(package_name):
    """
    this function tests if an spl is an implementation or a package group
    :param package: name of the package
    :return: true if the name of the package is not a version
    """
    return "implementations" in mspl[package_name]

######################################################################
### FUNCTIONS TO LOAD A PORTAGE MD5-CACHE REPOSITORY
######################################################################

def construct_spl(name, versions, environment, slots, features, fm_local, fm_external, fm_runtime):
    """
    create the spl structure from the extracted information
    """
    version_all, version, revision = versions
    environment = environment.split() if environment else ["*"]
    slots = slots.split("/") if slots else [0, 0]
    slot = str(slots[0])
    has_subslot = (len(slots) == 2)
    subslot = (str(slots[1]) if has_subslot else "0")
    features = features.split() if features else []
    features = { (feature[1:] if (feature[0] in ['+', '-']) else feature): {} for feature in features }
    fm_local = fm_local if fm_local else ""     
    fm_external = fm_external if fm_external else ""    
    fm_runtime = fm_runtime if fm_runtime else ""
    data = { 'name': name, 'features': features, 'environment': environment,
        'fm': { 'local': fm_local, 'external': fm_external, 'runtime': fm_runtime },
        'versions': { 'full': str(version_all), 'base': str(version), 'revision': str(revision) },
        'slots': { 'slot': slot, 'subslot': subslot } }
    return data


def load_file_egencache(filepath):
    """
    create the spl structure of a portage md5-cache file, and stores it in the mspl global variable
    """
    # 1. base information from the file name
    path_to_file, filename=os.path.split(filepath)
    path_to_category, category = os.path.split(path_to_file)
    package, version_all, version, revision = structure_filename(filename)
    name = category + "/" + filename
    # 2. informations from the file content
    data_tmp = {}
    with open(filepath, 'r') as f:
        for line in f:
            array = string.split(line, "=", 1)
            data_tmp[array[0]] = array[1][:-1] # remove the \n at the end of the line
    # 3. return the data
    versions = (version_all, version, revision)
    mspl[name] = construct_spl(
            name,
            versions,
            data_tmp.get('KEYWORDS'),
            data_tmp.get('SLOT'),
            data_tmp.get('IUSE'),
            data_tmp.get('REQUIRED_USE'),
            data_tmp.get('DEPEND'),
            data_tmp.get('RDEPEND'))
    pgroups.add(category + "/" + package)

def load_repository_egencache(path):
    """
    this function loads a full portage egencache repository.
    """
    pool = multiprocessing.Pool(available_core)
    pool.map(load_file_egencache,get_egencache_files(path))


######################################################################
### FUNCTIONS TO PARSE THE CONSTRAINTS
######################################################################

class SPLParserErrorListener(ErrorListener):
    def __init__(self):
        super(ErrorListener, self).__init__()
    def syntaxError(self, recognizer, offendingSymbol, line, column, msg, e):
        msg = "Parsing error in \"" + self.processing + "\" (stage " + self.stage + "): column " + str(column) + " " + msg + "\nSentence: " + self.parsed_string
        raise Exception(msg)

syntax_error_listener = SPLParserErrorListener()

def SPLParserlocal(self, to_parse):
    parser = __SPLParserparser(to_parse)
    return parser.required()

def SPLParserexternal(self, to_parse):
    parser = __SPLParserparser(to_parse)
    return parser.depend()

def __SPLParserparser(self, to_parse):
    lexer = DepGrammarLexer(InputStream(to_parse))
    lexer._listeners = [ syntax_error_listener ]
    parser = DepGrammarParser(CommonTokenStream(lexer))
    parser._listeners = [ syntax_error_listener ]
    return parser

def parse_spl(spl):
    spl['fm']['local-ast'] = SPLParserlocal(spl['fm']['local'])
    spl['fm']['external-ast'] = SPLParserexternal(spl['fm']['external'])
    spl['fm']['runtime-ast'] = SPLParserexternal(spl['fm']['runtime'])

def parse_mspl():
    for spl in mspl.values():
        parse_spl(spl)

######################################################################
### FUNCTIONS TO CREATE THE NAME <-> ID DICTIONARY
######################################################################

__id_current = 0
__id_lock = Lock.Lock()
def get_new_id():
    with __id_lock.lock:
        res = __id_current
        __id_current += 1
    return res

def generate_name_mapping_file(spl, target_dir):
    """
    Fill the name mapping file with information from one spl
    """
    global map_name_id
    global map_id_name
    name = spl['name']
    id = get_new_id()
    map_name_id["package"][name] = id
    map_id_name[id] = {"type": "package", "name": name}
    map_name_id["flag"][name] = {}
    map_name_id["slot"][name] = {}
    map_name_id["subslot"][name] = {}
    # 1. features
    if trust_feature_declaration:
        for feature in spl['features']:
            id = get_new_id()
            map_name_id["flag"][name][feature] = id
            map_id_name[id] = {"type": "flag", "name": feature, "package": name}
    else:
        # need a visitor for this
        pass
    # 2. slots
missing id to name for slots and environment: is it an error

##########################################################
##########################################################


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
            # consider also the flags in the "features" key of the mspl
            for j in [x for x in mspl[i]["features"] if x != "__main__"]:
                if j not in map_name_id["flag"][i]:
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
            if counter > 1:
                logging.error("Find more than one slot for package " + i)
            # process subslots (conversion from name into a range of integers)
            counter = 0
            for k in mspl[i]["features"]["__main__"]["subslots"]:
                map_name_id["subslot"][i][k] = counter
                counter += 1
            if counter > 1:
                logging.error("Find more than one subslot for package " + i)
        # process environment (conversion from name into a range of integers)
        for j in mspl[i]["environment"]:
            name = settings.process_envirnoment_name(j)
            # consider only envirnoments that we are sure the component can be installed
            # * and ** are treated the same, ~x and x are treated the same
            if not name.startswith("-"):
                if not name in map_name_id["context"]:
                    map_name_id["context"][name] = len(map_name_id["context"])
    logging.info("Write map of names in " + settings.NAME_MAP_FILE)
    with open(os.path.join(target_dir, settings.NAME_MAP_FILE), 'w') as f:
        json.dump({"name_to_id": map_name_id, "id_to_name": map_id_name}, f)




##########################################################
##########################################################
##########################################################






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
            # consider also the flags in the "features" key of the mspl
            for j in [x for x in mspl[i]["features"] if x != "__main__"]:
                if j not in map_name_id["flag"][i]:
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
            if counter > 1:
                logging.error("Find more than one slot for package " + i)
            # process subslots (conversion from name into a range of integers)
            counter = 0
            for k in mspl[i]["features"]["__main__"]["subslots"]:
                map_name_id["subslot"][i][k] = counter
                counter += 1
            if counter > 1:
                logging.error("Find more than one subslot for package " + i)
        # process environment (conversion from name into a range of integers)
        for j in mspl[i]["environment"]:
            name = settings.process_envirnoment_name(j)
            # consider only envirnoments that we are sure the component can be installed
            # * and ** are treated the same, ~x and x are treated the same
            if not name.startswith("-"):
                if not name in map_name_id["context"]:
                    map_name_id["context"][name] = len(map_name_id["context"])
    logging.info("Write map of names in " + settings.NAME_MAP_FILE)
    with open(os.path.join(target_dir, settings.NAME_MAP_FILE), 'w') as f:
        json.dump({"name_to_id": map_name_id, "id_to_name": map_id_name}, f)


# function to encode SMT expression into SMTLIB
# ; benchmark
# (set-info :status unknown)
# (set-logic QF_LIA)
# (declare-fun b () Int)
# (declare-fun a () Int)
# (assert ...)
# (check-sat)
# // empty line
def toSMT2(f, status="unknown", name="benchmark", logic=""):
  v = (z3.Ast * 0)()
  return z3.Z3_benchmark_to_smtlib_string(f.ctx_ref(), name, logic, status, "", 0, v, f.as_ast()).replace(
      "\n"," ").replace("(check-sat)","").replace("; benchmark (set-info :status unknown)","").strip()

def convert(package,target_dir):

    logging.debug("Processing package " + package)
    assert mspl
    if not package in mspl:
        raise Exception("Package " + package + " not found in the MSPL JSON files")

    data = {"attributes": [], "constraints": [], "configures": [],
            "dependencies": []}

    # add "dependencies" and "configures"
    for i in mspl[package]["configures"]:
        if i in mspl:
            data["configures"].append(i)
        else:
            logging.warning("The package " + i + " find in configures is not found. It will be ignored")

    for i in mspl[package]["dependencies"]:
        if i in mspl:
            data["dependencies"].append(i)
        else:
            logging.warning("The package " + i + " find in dependencies is not found. It will be ignored")

    if is_base_package(package):
        data["implementations"] = mspl[package]["implementations"]
        versions = mspl[package]["implementations"].values()
        # if installed then one of its version should be installed as well
        data["constraints"].append(
            settings.get_hyvar_package(map_name_id["package"][package]) +
            " = 1 impl (" +
            settings.get_hyvar_or([settings.get_hyvar_package(map_name_id["package"][i]) + " = 1" for i in versions]) + ")")
        # two versions should have different slots or subslots
        possible_slot_matches = [(i,j,unicode(map_name_id["slot"][i][s]),unicode(map_name_id["slot"][j][s]))
                                 for i in versions for j in versions for s in map_name_id["slot"][i] if
                                 i<j and s in map_name_id["slot"][j]]
        possible_subslot_matches = [(i, j, unicode(map_name_id["subslot"][i][s]),unicode(map_name_id["subslot"][j][s]))
                                    for i in versions for j in versions for s in map_name_id["subslot"][i] if
                                    i < j and s in map_name_id["subslot"][j]]
        for i in versions:
            for j in versions:
                if i < j:
                    slots = [(x[2],x[3]) for x in possible_slot_matches if x[0] == i and x[1] == j]
                    subslots = [(x[2], x[3]) for x in possible_subslot_matches if x[0] == i and x[1] == j]
                    c = settings.get_hyvar_impl(
                            settings.get_hyvar_and(
                                [settings.get_hyvar_package(map_name_id["package"][i]) + "= 1",
                                 settings.get_hyvar_package(map_name_id["package"][j]) + " = 1"]),
                            settings.get_hyvar_impl(
                                settings.get_hyvar_or(
                                    [settings.get_hyvar_slot(map_name_id["package"][i]) + " = " + x[0] + " and " +
                                    settings.get_hyvar_slot(map_name_id["package"][j]) + " = " + x[1] for x in slots]),
                                settings.get_hyvar_or(
                                    [settings.get_hyvar_subslot(map_name_id["package"][i]) + " = " + x[0] + " xor " +
                                    settings.get_hyvar_subslot(map_name_id["package"][j]) + " = " + x[1] for x in subslots])))
                    if c != "true":
                        data["constraints"].append(c)
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

        # package with version needs its base package to be selected
        data["constraints"].append(settings.get_hyvar_package(map_name_id["package"][package]) + " = 1 impl 1 = " +
                                settings.get_hyvar_package(map_name_id["package"][re.sub(settings.VERSION_RE,"",package)]))

        # if package is not selected its flags are not selected either
        data["constraints"].append(settings.get_hyvar_impl(
            settings.get_hyvar_package(map_name_id["package"][package]) + " = 0",
            settings.get_hyvar_and([settings.get_hyvar_flag(x) + " = 0" for x in map_name_id["flag"][package].values()])))

        # if flag is selected then its package is selected too
        for i in map_name_id["flag"][package].values():
            data["constraints"].append(settings.get_hyvar_impl(
                settings.get_hyvar_flag(i) + " = 1",
                settings.get_hyvar_package(map_name_id["package"][package]) + " = 1"))

    # add validity formulas. Context must be one of the possible env
    envs = [settings.process_envirnoment_name(x) for x in mspl[package]["environment"]]
    envs = [x for x in envs if not x.startswith("-")]
    if envs:
        if "*" not in envs:
            data["constraints"].append(
                settings.get_hyvar_package(map_name_id["package"][package]) + " = 1 impl (" +
                settings.get_hyvar_or(
                    [settings.get_hyvar_context() + " = " + unicode(map_name_id["context"][x]) for x in envs]) + ")")
    else:
        logging.warning("Environment empty for package " + package + ". This package will be treated as not installable.")
        data["constraints"] = ["false"]

    # if activated, for performance reasons do the encoding directly into z3 smt formulas
    if to_smt:
        features = set()
        ls = []
        for i in data["constraints"]:
            try:
                # logging.debug("Processing " + i)
                d = SpecTranslator.translate_constraint(i, {})
                # other.update(d["contexts"])
                # other.update(d["attributes"])
                features.update(d["features"])
                ls.append(d["formula"])
            except Exception as e:
                logging.error("Parsing failed while converting into SMT " + i + ": " + unicode(e))
                logging.error("Exiting")
                sys.exit(1)
        formula = z3.simplify(z3.And(ls))
        s = toSMT2(formula)
        data["smt_constraints"] = {}
        data["smt_constraints"]["formulas"] = [s]
        data["smt_constraints"]["features"] = list(features)
        # data["smt_constraints"]["other_int_symbols"] = list(other)
        data["constraints"] = []

    logging.debug("Writing file " + os.path.join(target_dir, package + ".json"))
    d = package.split(settings.PACKAGE_NAME_SEPARATOR)[0]
    try:
        if not os.path.exists(os.path.join(target_dir, d)):
            os.makedirs(os.path.join(target_dir, d))
    except OSError, e:
        if e.errno != 17:
            raise
        # if e.errno == 17 another thread already created the directory (race condition)
    with open(os.path.join(target_dir, package + ".json"), 'w') as f:
        json.dump(data, f, indent=1)
    return True

# worker for a thread
def worker(pair):
    pkg,target_dir = pair
    convert(pkg,target_dir)
    return True

def main(argv):
    """
    Main procedure
    """

    global map_name_id
    global map_id_name
    global mspl
    global to_smt

    cores_to_use = max(1,multiprocessing.cpu_count()-1)

    try:
        opts, args = getopt.getopt(argv,"hvp:",["help","verbose","no_opt","par="])
    except getopt.GetoptError as err:
        print str(err)
        usage()
        sys.exit(1)
    for opt, arg in opts:
        if opt == '-h':
            usage()
            sys.exit()
        elif opt in ("--no_opt"):
            to_smt = False
        elif opt in ("-p", "--par"):
            cores_to_use = int(arg)
        elif opt in ("-v", "--verbose"):
            logging.basicConfig(format="%(levelname)s: %(message)s", level=logging.DEBUG)
            logging.info("Verbose output.")

    if len(args) != 2:
      print "2 argument are required"
      print(__doc__)
      sys.exit(1)

    input_dir = os.path.abspath(args[0])
    target_dir = os.path.abspath(args[1])

    if not os.path.exists(target_dir):
        os.makedirs(target_dir)

    logging.info("Load the MSPL. This may take a while")
    load_mspl(os.path.join(input_dir,'mspl'))
    logging.info("Load the SPL. This may take a while")
    load_spl(os.path.join(input_dir,os.path.join('catalog','spl')))

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

    #convert("sys-libs/db-4.5.20_p2-r1", target_dir)
    # convert("dev-db/oracle-instantclient-basic-10.2.0.3-r1", target_dir)
    # convert("app-dicts/sword-asv-1.3", target_dir)
    # exit(0)

    to_convert = [x for x in spl.keys() if not os.path.isfile(os.path.join(target_dir,x+".json"))]
    # if more than one thread is used python go into segmentation fault
    logging.info("Starting to convert packages using " + unicode(cores_to_use) + " processes.")
    logging.info("Number of packages to convert: " + unicode(len(to_convert)))

    pool = multiprocessing.Pool(cores_to_use)
    pool.map(worker,[(x,target_dir) for x in to_convert])
    logging.info("Execution terminated.")

if __name__ == "__main__":
    main(sys.argv[1:])