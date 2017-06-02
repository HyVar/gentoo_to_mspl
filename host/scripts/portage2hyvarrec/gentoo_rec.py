
__author__ = "Michael Lienhardt & Jacopo Mauro"
__copyright__ = "Copyright 2017, Michael Lienhardt & Jacopo Mauro"
__license__ = "ISC"
__version__ = "0.1"
__maintainer__ = "Jacopo Mauro"
__email__ = "mauro.jacopo@gmail.com"
__status__ = "Prototype"

import os
import utils

import json
import sys
import logging
import re
import dep_translator
import z3
import SpecificationGrammar.SpecTranslator as SpecTranslator
import multiprocessing
import click

def usage():
    """Print usage"""
    print(__doc__)


#####################################################################################
### GLOBAL VARVIABLES
#####################################################################################

# stores the json info related to the mspl produced processing the gentoo files
mspl = None
# stores the ast of the spl's constraints
asts = None

# stores the package group
pgroups = None

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

def construct_spl(names, versions, environment, slots, features, fm_local, fm_external, fm_runtime):
    """
    create the spl structure from the extracted information
    """
    name, group_name = names
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
    data = { 'name': name, 'group_name': group_name, 'features': features, 'environment': environment,
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
    return construct_spl(
            (name, category + "/" + package ),
            (version_all, version, revision),
            data_tmp.get('KEYWORDS'),
            data_tmp.get('SLOT'),
            data_tmp.get('IUSE'),
            data_tmp.get('REQUIRED_USE'),
            data_tmp.get('DEPEND'),
            data_tmp.get('RDEPEND'))
      

def load_repository_egencache(path):
    """
    this function loads a full portage egencache repository.
    """
    global mspl
    pool = multiprocessing.dummy.Pool(available_core)
    mspl = pool.map(load_file_egencache, get_egencache_files(path))


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

def SPLParserlocal(to_parse):
    parser = __SPLParserparser(to_parse)
    return parser.required()

def SPLParserexternal(to_parse):
    parser = __SPLParserparser(to_parse)
    return parser.depend()

def __SPLParserparser(to_parse):
    lexer = DepGrammarLexer(InputStream(to_parse))
    lexer._listeners = [ syntax_error_listener ]
    parser = DepGrammarParser(CommonTokenStream(lexer))
    parser._listeners = [ syntax_error_listener ]
    return parser

lass SPLParserGetUses(DepGrammarVisitor):
    """
    this class fill the dictionary from an spl's constraints
    """
    def __init__(self):
        super(DepGrammarVisitor, self).__init__()
    def visitRequired(self, ctx):
        return [ self.visitRequiredEL()self.visitChildren(ctx)


    # Visit a parse tree produced by DepGrammarParser#requiredSIMPLE.
    def visitRequiredSIMPLE(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by DepGrammarParser#requiredCONDITION.
    def visitRequiredCONDITION(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by DepGrammarParser#requiredCHOICE.
    def visitRequiredCHOICE(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by DepGrammarParser#requiredINNER.
    def visitRequiredINNER(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by DepGrammarParser#depend.
    def visitDepend(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by DepGrammarParser#dependSIMPLE.
    def visitDependSIMPLE(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by DepGrammarParser#dependCONDITION.
    def visitDependCONDITION(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by DepGrammarParser#dependCHOICE.
    def visitDependCHOICE(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by DepGrammarParser#dependINNER.
    def visitDependINNER(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by DepGrammarParser#choice.
    def visitChoice(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by DepGrammarParser#condition.
    def visitCondition(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by DepGrammarParser#atom.
    def visitAtom(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by DepGrammarParser#version_op.
    def visitVersion_op(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by DepGrammarParser#slotSIMPLE.
    def visitSlotSIMPLE(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by DepGrammarParser#slotFULL.
    def visitSlotFULL(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by DepGrammarParser#slotEQ.
    def visitSlotEQ(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by DepGrammarParser#slotSTAR.
    def visitSlotSTAR(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by DepGrammarParser#slotSIMPLEEQ.
    def visitSlotSIMPLEEQ(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by DepGrammarParser#selection.
    def visitSelection(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by DepGrammarParser#prefix.
    def visitPrefix(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by DepGrammarParser#preference.
    def visitPreference(self, ctx):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by DepGrammarParser#suffix.
    def visitSuffix(self, ctx):
        return self.visitChildren(ctx)


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

# note that ANTLR4 visitors are thread safe
class SPLParserGetUses(DepGrammarVisitor):
    """
    this class fill the dictionary from an spl's constraints
    """
    def __init__(self):
        super(DepGrammarVisitor, self).__init__()
    def visit_spl(self, spl):
        self.name = spl['name']
        self.visitRequired(spl['fm']['local-ast'])
        self.visitDepend(spl['fm']['external-ast'])
        self.visitDepend(spl['fm']['runtime-ast'])
    def visitCondition(self, ctx):
        use = ctx.getID().getText()
        utils.update_map('flag', self.name, use)
    def visitAtom(self, ctx):
        self.package = ctx.getID().getText()
    def visitSelection(self, ctx):
        use = ctx.getID().getText()        
        utils.update_map('flag', self.package, use)


def generate_name_mapping(spl):
    """
    Fill the name mapping file with information from one spl
    """
    name = spl['name']
    utils.update_map_spl(name)
    # 1. features
    if trust_feature_declaration:
        for use in spl['features']:
            utils.update_map('flag', package, use)
    else:
        SPLParserGetUses().visit_spl(spl)
    # 2. slots
    utils.update_map('slot', name, spl['slots']['slot'])
    utils.update_map('subslot', name, spl['slots']['subslot'])
    # 3. keywords
    for keyword in spl['environment']:
            name = utils.update_map('context',keyword)


def generate_name_mapping(target_dir):
    """
    this function extracts the name mapping from the loaded mspl, and save it in the specified directory.
    """
    pool = multiprocessing.Pool(available_core)
    pool.map(generate_name_mapping,mspl.values())
    utils.finish_update_map(target_dir)


######################################################################
### FUNCTIONS FOR MSPL TRANSLATION
######################################################################

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
        if mspl[package]["fm"]["runtime"] and mspl[package]["fm"]["runtime"] != mspl[package]["fm"]["external"]:
            parser = visitor.parser(mspl[package]["fm"]["runtime"])
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

@click.command()
@click.argument(
    'input_dir',
    type=click.Path(exists=True, file_okay=False, dir_okay=True, writable=False, readable=True, resolve_path=True))
@click.argument(
    'target_dir',
    type=click.Path(exists=False, file_okay=False, dir_okay=True, writable=True, readable=True, resolve_path=True))
@click.option('--no-opt', is_flag=True, help="Do not convert dependencies into SMT formulas.")
@click.option('--verbose', '-v', is_flag=True, help="Print debug messages.")
@click.option('--par', '-p', type=click.INT, default=-1, help='Number of process to use for translating the dependencies.')
@click.option('--translate-only', '-p', default="", help='Package to convert - Do not convert all the other ones.')
def main(input_dir,target_dir,no_opt,verbose,par,translate_only):
    """
    Tool that converts the gentoo files

    INPUT_DIR directory containing the mspl and spl directories

    TARGET_DIR output directory
    """
    global map_name_id
    global map_id_name
    global mspl
    global to_smt

    if par > 1:
        cores_to_use = max(par, multiprocessing.cpu_count())
    else:
        cores_to_use = max(1, multiprocessing.cpu_count() - 1)
    if verbose:
        logging.basicConfig(format="%(levelname)s: %(message)s", level=logging.DEBUG)
        logging.info("Verbose output.")

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

    if translate_only:
        convert(translate_only, target_dir)
    else:
        to_convert = [x for x in spl.keys() if not os.path.isfile(os.path.join(target_dir,x+".json"))]
        # if more than one thread is used python goes into segmentation fault
        logging.info("Starting to convert packages using " + unicode(cores_to_use) + " processes.")
        logging.info("Number of packages to convert: " + unicode(len(to_convert)))

        pool = multiprocessing.Pool(cores_to_use)
        pool.map(worker,[(x,target_dir) for x in to_convert])
    logging.info("Execution terminated.")

if __name__ == "__main__":
    main()