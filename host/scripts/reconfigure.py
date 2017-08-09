__author__ = "Jacopo Mauro"
__copyright__ = "Copyright 2017, Jacopo Mauro"
__license__ = "ISC"
__version__ = "0.1"
__maintainer__ = "Jacopo Mauro"
__email__ = "mauro.jacopo@gmail.com"
__status__ = "Prototype"


import json
import sys
import utils
import logging
import os
from subprocess import PIPE
import psutil
import requests
import click
import time
import multiprocessing
import constraint_parser
import smt_encoding
import extract_dependencies
import pysmt.shortcuts
import re


from pysmt.smtlib.parser import SmtLib20Parser
import cStringIO


# Global variables

# keep temporary files
KEEP = False

REQUEST_DUMMY_PACKAGE_NAME = "request"

def clean():
  """
  Utility for (possibly) cleaning temporary files
  """
  if not KEEP:
    utils.TMP_FILES_LOCK.acquire()
    for f in utils.TMP_FILES:
      if os.path.exists(f):
        os.remove(f)
    utils.TMP_FILES_LOCK.release()

def read_json(json_file):
    """
    loads the json file
    """
    with open(json_file) as data_file:
        data = json.load(data_file)
    return data


def load_request_file(file_name,concurrent_map,mspl, map_name_id):
    """
    Parses the request file which is composed by one or more dependencies
    """
    constraints = []
    with open(file_name,"r") as f:
        lines = f.readlines()
    # data structure to reuse the parse_spl function
    spls = [{"name": unicode(i), "group_name" : "",
              'fm': {'local': "", 'external': "", 'runtime': lines[i]}} for i in range(len(lines))]
    # get the asts
    asts = concurrent_map(constraint_parser.parse_spl, spls)
    asts = [x for (_,_,x) in asts ]
    # get the dependencies
    visitor = extract_dependencies.GenerateDependenciesAST()
    dependencies = concurrent_map(visitor.visitDepend,asts)
    dependencies = [x for sublist in dependencies for x in set(sublist) if x in mspl]
    # get constraints
    visitor = smt_encoding.ASTtoSMTVisitor(mspl, map_name_id, "")
    constraints = [smt_encoding.toSMT2(visitor.visitDepend(ast)) for ast in asts]

    return dependencies,constraints


def load_configuration_file(file_name,mspl,map_name_id):
    initial_configuration = read_json(file_name)
    for i in initial_configuration:
        if i in mspl:
            initial_configuration[i] = [x[1:] for x in initial_configuration[i]
                                        if x.startswith("+") and x[1:] in map_name_id["flag"][i]]
        else:
            logging.warning("Not found the package " + i + " defined in the initial configuration. It will be ignored.")
            del(initial_configuration[i])
    return initial_configuration


def run_hyvar(json_data,par,explain_modality):
    """
    Run hyvar locally assuming that there is a command hyvar-rec
    """
    file_name = utils.get_new_temp_file("json")
    with open(file_name,"w") as f:
        json.dump(json_data, f)
        # json.dump(json_data, f,indent=1)
    cmd = ["hyvar-rec","--features-as-boolean"]
    if par > 1:
        cmd += ["-p",unicode(par)]
    if explain_modality:
        cmd.append("--explain")
    cmd.append(file_name)
    logging.debug("Running command " + unicode(cmd))
    process = psutil.Popen(cmd,stdout=PIPE,stderr=PIPE)
    out, err = process.communicate()
    logging.debug('Stdout of ' + unicode(cmd))
    logging.debug(out)
    logging.debug('Stderr of ' + unicode(cmd))
    logging.debug(err)
    logging.debug('Return code of ' + unicode(cmd) + ': ' + str(process.returncode))
    # in explain modality prints the output to detect which constraints are unsat
    if explain_modality:
        print(out)
    return json.loads(out)

# def run_remote_hyvar(json_data,url):
#     """
#     Run hyvar
#     """
#     logging.debug("Invoking service at url " + url)
#     response = requests.post(url + "/explain",
#                              data=json.dumps(json_data),
#                              headers={'content-type': 'application/json'})
#     return response.json()


def get_transitive_closure_of_dependencies(mspl,pkgs):
    # returns the transitive closure of the dependencies
    deps = set(pkgs)
    to_check = pkgs
    checked = set()
    while to_check:
        p = to_check.pop()
        for i in mspl[p]["dependencies"]:
            if i not in checked:
                to_check.append(i)
                deps.add(i)
        checked.add(p)
    return deps


def create_hyvarrec_spls(package_request,
                         request_constraints,
                         initial_configuration,
                         contex_value,
                         mspl,
                         map_name_id,
                         map_id_name):
    """
    Given a list of packages it creates its hyvarrec SPL
    """
    # todo read list of configures and depends for all packages

    spls = {}

    to_process = set(package_request)
    # todo: this part can be more efficient using union find
    while to_process:
        i = to_process.pop()
        spls[i] = get_transitive_closure_of_dependencies(mspl,[i]+initial_configuration.keys())
        to_process.difference_update(spls[i])
        intersections = [x for x in spls if spls[i].intersection(spls[x]) and x != i]
        if intersections:
            for j in intersections:
                spls[i].update(spls[j])
                del(spls[j])

    jsons = []
    for i in spls:
        data = {"attributes": [],
                "contexts": [{"id": "context[" + utils.CONTEXT_VAR_NAME + "]",
                              "min": 0,
                              "max": len(map_name_id["context_int"])-1}],
                "configuration": {
                    "selectedFeatures": [],
                    "attribute_values": [],
                    "context_values": [{"id": "context[" + utils.CONTEXT_VAR_NAME + "]",
                                        "value": map_name_id["context_int"][contex_value]}]},
                "constraints": [],
                "preferences": [],
                "smt_constraints": {
                    "formulas": [],
                    "features": [],
                    "other_int_symbols": [ "context[" + utils.CONTEXT_VAR_NAME + "]"] }
                }

        # add the constraints of the packages
        for j in spls[i]:
            if not "implementations" in mspl[j]:
                data["smt_constraints"]["formulas"].extend(mspl[j]["smt_constraints"])
            # no need to add features since they are already boolean values

        # add constraints to select the required packages
        data["smt_constraints"]["formulas"].extend(request_constraints)

        # add info about the initial configuration
        for j in initial_configuration:
            if j in mspl[i]:
                for k in initial_configuration[j]:
                    data["configuration"]["selectedFeatures"].append(
                        smt_encoding.get_hyvar_use(map_name_id,j,k))

        # add preferences: do not remove packages already installed
        data["preferences"].append( " + ".join(
            [smt_encoding.get_hyvar_spl_name(map_name_id, pkg) for pkg in initial_configuration
			 if pkg in spls[i]]))

        logging.debug("SPL created : constraints " + unicode(len(data["constraints"])) +
                      ", smt formulas " + unicode(len(data["smt_constraints"]["formulas"])))
        logging.debug("Packages to configure " + unicode(len(mspl[i])))

        jsons.append({"json":data, "deps": spls[i]})
    return jsons


def update_configuration(hyvarrec_out,configuration,map_name_id,map_id_name):
    pkgs = []
    flags = []
    for i in hyvarrec_out["features"]:
        el = map_id_name[i[1:]]
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


def get_diff_configuration(new_conf,old_conf,mspl):
    data = {"toUpdate": {}, "toInstall": {}, "toRemove": {}}
    for i in new_conf.keys():
        if "implementations" not in mspl[i]:
            if i in old_conf:
                if set(new_conf[i]) != set(old_conf[i]):
                    data["toUpdate"][i] = new_conf[i]
            else:
                data["toInstall"][i] = new_conf[i]
    for i in old_conf.keys():
        if i not in new_conf:
            data["toRemove"][i] = {}
    return data


def get_conf_with_negative_use_flags(conf,map_name_id):
    data = {}
    for i in conf.keys():
        all_flags = map_name_id["flag"][i].keys()
        positive_flags = conf[i]
        negative_flags = set(all_flags)
        negative_flags.difference_update(positive_flags)
        data[i] = positive_flags + [ "-" + x for x in negative_flags]
    return data

def get_better_constraint_visualization(constraints,mspl,map_name_id,map_id_name):
    ls = []
    parser = SmtLib20Parser()
    for i in constraints:
        f = cStringIO.StringIO(i)
        script = parser.get_script(f)
        f.close()
        formula = script.get_last_formula()
        formula = pysmt.shortcuts.to_smtlib(formula,daggify=False)
        # translate contexts
        nums = re.findall('\(=\s*' + utils.CONTEXT_VAR_NAME + '\s*([0-9]+)\)',formula)
        for i in nums:
            num = int(i)
            env = [ x for x in map_name_id['context_int'] if map_name_id['context_int'][x] == num]
            assert len(env) == 1
            formula = re.sub('\(=\s*' + utils.CONTEXT_VAR_NAME + '\s' + i + '\)', 'env(' + env[0] + ')',formula)
        # translate packages
        where_declared = "user-required: "
        pkgs = set(re.findall('p([0-9]+)',formula))
        for pkg in pkgs:
            name = map_id_name[pkg]["name"]
            formula = re.sub('p' + pkg,name,formula)
            if i in mspl[name]["smt_constraints"]:
                where_declared = name + ": "

        # translate uses
        uses = set(re.findall('u([0-9]+)', formula))
        for use in uses:
            formula = re.sub('u' + use, map_id_name[use]["package"] +  "[[" + map_id_name[use]["name"] + "]]", formula)
        ls.append(where_declared + formula)
    return ls



@click.command()
@click.argument(
    'input_file',
    type=click.Path(exists=True, file_okay=True, dir_okay=False, readable=True, resolve_path=True))
@click.argument(
    'request_file',
    type=click.Path(exists=True, file_okay=True, dir_okay=False, writable=False, readable=True, resolve_path=True))
@click.argument(
    'configuration_file',
    type=click.Path(exists=True, file_okay=True, dir_okay=False, writable=False, readable=True, resolve_path=True))
@click.argument(
    'new_configuration_file',
    type=click.Path(exists=False, file_okay=True, dir_okay=False, writable=True, readable=True, resolve_path=True))
@click.argument(
    'package_use_file',
    type=click.Path(exists=False, file_okay=True, dir_okay=False, writable=True, readable=True, resolve_path=True))
@click.argument(
    'emerge_commands_file',
    type=click.Path(exists=False, file_okay=True, dir_okay=False, writable=True, readable=True, resolve_path=True))
@click.option('--environment', default="amd64", help="Keyword identifying the architecture to use.")
@click.option('--verbose', '-v', is_flag=True, help="Print debug messages.")
@click.option('--keep', '-k', is_flag=True, help="Do not delete intermediate files.")
@click.option('--explain', is_flag=True, help="Run HyVarRec in explanation mode.")
@click.option('--url', '-r', default="", help='URL of the remote hyvarrec to use if available (local command otherwise used).')
@click.option('--par', '-p', type=click.INT, default=-1, help='Number of process to use for running the local HyVarRec.')
@click.option('--save-modality', default="json", type=click.Choice(["json","marshal"]),
              help='Saving modality. Marshal is supposed to be faster but python version specific.')
def main(input_file,
         request_file,
         configuration_file,
         new_configuration_file,
         package_use_file,
         emerge_commands_file,
         environment,
         verbose,
         keep,
         explain,
         url,
         par,
         save_modality):
    """
    Uses HyVarRec to produce a valid configuration of packages to install.

    INPUT_DIR Input directory containing the hyvar mspl json translation files

    REQUEST_FILE File containing the request

    CONFIGURATION_FILE File containing the current configuration

    NEW_CONFIGURATION_FILE File containing the new_configuration_file that will be generated

    PACKAGE_USE_FILE File containing the package.use file that will be generated and copied into the guest

    EMERGE_COMMANDS_FILE File containing the script to run in the guest to generate the configuration

    Exampe: python reconfigure.py -v --save-modality marshal --environment amd64 ../../../host/portage/json/hyvarrec/hyvar_mspl.gentoorec ../../../git ../../../host/configuration/json/configuration.json ../../../host/configuration/json/new_configuration.json ../../../host/configuration/package.use ../../../host/configuration/update.sh 2>&1 | tee log1.log
    """

    # OPTION: keep intermediate file options. Useful for debug
    if keep:
        global KEEP
        KEEP = True

    # OPTION: manage verbosity
    if verbose:
        logging.basicConfig(format="%(levelname)s: %(message)s", level=logging.DEBUG)
        logging.info("Verbose output.")

    # OPTION: manage number of parallel threads
    if par != -1:
        available_cores = min(par, multiprocessing.cpu_count())
    else:
        available_cores = 1

    # manage concurrency
    if available_cores > 1:
        pool = multiprocessing.Pool(available_cores)
        concurrent_map = pool.map
    else:
        concurrent_map = map

    logging.info("Load the MSPL. This may take a while.")
    t = time.time()
    data = utils.load_data_file(input_file,save_modality)
    mspl,map_name_id,map_id_name = data["mspl"],data["map_name_id"],data["map_id_name"]
    logging.info("Loading completed in " + unicode(time.time() - t) + " seconds.")


    logging.info("Load the request package list.")
    t = time.time()
    dependencies,constraints = load_request_file(request_file, concurrent_map, mspl, map_name_id)
    logging.info("Loading completed in " + unicode(time.time() - t) + " seconds.")
    logging.debug("Dependencies: " + unicode(dependencies))
    logging.debug("Constraints: " + unicode(constraints))

    logging.info("Load the configuration file.")
    t = time.time()
    initial_configuration = load_configuration_file(configuration_file, mspl, map_name_id)
    logging.info("Loading completed in " + unicode(time.time() - t) + " seconds.")

    logging.info("Computing the SPLs.")
    t = time.time()
    to_solve = create_hyvarrec_spls(dependencies,
                                    constraints,
                                    initial_configuration,
                                    environment,
                                    mspl,
                                    map_name_id,
                                    map_id_name)
    logging.info("Computation completed in " + unicode(time.time() - t) + " seconds.")

    configuration = {}
    for job in to_solve:
        logging.info("Running HyVarRec.")
        t = time.time()
        # if url:
        #     json_result = run_remote_hyvar(job["json"],url)
        # else:
        json_result = run_hyvar(job["json"],par,explain)
        logging.info("Execution of HyVarRec took " + unicode(time.time() - t) + " seconds.")
        if json_result["result"] != "sat":
            if explain:
                # try to print a better explanation of the constraints
                constraints = get_better_constraint_visualization(
                    json_result["constraints"],mspl,map_name_id,map_id_name)
                sys.stderr.write("Conflict detected. Explanation:\n" + "\n".join(constraints) + '\n')
            logging.error("Conflict detected. Impossible to satisfy the request. Exiting.")
            sys.exit(1)
        logging.debug("HyVarRec output: " + unicode(json_result))
        # update the info on the final configuration
        update_configuration(json_result,configuration,map_name_id,map_id_name)

    # remove all the pacakges without version from final configuration
    for i in configuration.keys():
        if "implementations" in mspl[i]:
            del(configuration[i])

    configuration_diff = get_diff_configuration(configuration,initial_configuration,mspl)
    logging.debug("Packages to update flags: " + unicode(len(configuration_diff["toUpdate"])))
    logging.debug("Packages to install: " + unicode(len(configuration_diff["toInstall"])))
    logging.debug("Packages to remove: " + unicode(len(configuration_diff["toRemove"])))
    print(json.dumps(configuration_diff,indent=1))

    logging.debug("Generate emerge commands to run.")
    with open(emerge_commands_file, "w") as f:
        f.write("#!/bin/bash\n")
        if configuration_diff["toRemove"].keys():
            f.write("emerge --unmerge " + " ".join(["=" + x for x in configuration_diff["toRemove"].keys()]) + "\n")
        if configuration_diff["toUpdate"].keys() + configuration_diff["toInstall"].keys():
            f.write("emerge -a --newuse " + " ".join(["=" + x for x in configuration_diff["toUpdate"].keys()]) +
                " " + " ".join(["=" + x for x in configuration_diff["toInstall"].keys()]) + "\n")

    logging.debug("Printing the final configuration with all the positive and negative use flags.")
    final_conf = get_conf_with_negative_use_flags(configuration,map_name_id)
    with open(new_configuration_file,"w") as f:
        json.dump(final_conf,f,indent=1)

    logging.debug("Printing the package.use file.")
    with open(package_use_file,"w") as f:
        for i in final_conf.keys():
            f.write("=" + i + " " + " ".join(final_conf[i]) + "\n")

    logging.info("Cleaning.")
    clean()
    logging.info("Execution terminated correctly.")


if __name__ == "__main__":
    main()