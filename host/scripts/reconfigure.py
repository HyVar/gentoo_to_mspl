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
# import constraint_parser
import smt_encoding
# import extract_dependencies
import pysmt.shortcuts
import re
import translate_portage

import hyportage_data
import hyportage_from_egencache
import hyportage_ids
import hyportage_pattern
import hyportage_configuration

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


def load_request_file(file_name,pattern_repository,id_repository,mspl,spl_groups,core_configuration):
    """
    Parses the request file which is composed by one or more dependencies
    """
    with open(file_name,"r") as f:
        lines = f.readlines()

    # todo add in the request the default pattern request (assuming that is in core_configuration)
    # add core_configuration profile does not work (some constraints there make the problem unsat since some patterns
    # can not be installed
    # lines.extend([hyportage_pattern.pattern_to_atom(x) for x in hyportage_configuration.core_configuration_get_profile_patterns(core_configuration)])
    smt_visitor = smt_encoding.ASTtoSMTVisitor(pattern_repository, id_repository, "dummy_pkg_name")

    dependencies = set()
    smt_constraints = []

    for l in lines:
        parsed_line = hyportage_from_egencache.translate_depend(l)
        dep_visitor = hyportage_from_egencache.GETDependenciesVisitor("dummy_pkg_name")
        dep_visitor.visitDepend(parsed_line)
        patterns = dep_visitor.res[1]
        for pattern in patterns:
            if not hyportage_pattern.is_pattern_in_pattern_repository(pattern_repository, pattern):
                hyportage_pattern.pattern_repository_add_pattern(pattern_repository, mspl, spl_groups, pattern)
        dependencies.update([pattern[1] for pattern in patterns])
        smt_constraints.append(smt_visitor.visitDepend(parsed_line))
        print smt_constraints[-1]
        print patterns
        print [pattern[1] for pattern in patterns]
    smt_constraints = smt_encoding.simplify_constraints("user_req", smt_constraints, "individual")
    return dependencies,smt_constraints


# def load_configuration_file(file_name):
#     """
#     returns the mapping between the packages installed and their use selected
#     :param file_name:
#     :param id_repository:
#     :return:
#     """
#     with open(file_name,"r") as f:
#         lines = f.readlines()
#     initial_configuration = {}
#     for l in lines:
#         ls = l.split(" ")
#         assert ls
#         assert ls[0][0] == "="
#         pkg_name = ls[0][1:]
#         initial_configuration[pkg_name] = [x for x in ls[1:]
#                                     if not x.startswith("-")]
#     return initial_configuration


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


def get_transitive_closure_of_dependencies(mspl,spl_groups,pkg):
    # returns the transitive closure of the dependencies
    deps = set([pkg])
    to_check = [pkg]
    checked = set()
    while to_check:
        p = to_check.pop()
        if p in spl_groups:
            ls = hyportage_data.spl_group_get_references(spl_groups[p])
        elif p in mspl:
            ls = [pattern[1] for pattern in hyportage_data.spl_get_dependencies(mspl[p])]
        else:
            ls = []
            logging.warning("Package " + p + " not found in the mspl or spl groups.")
        for i in ls:
            if i not in checked:
                to_check.append(i)
                deps.add(i)
        checked.add(p)
    return deps


def create_hyvarrec_spls(package_request,
                         request_constraints,
                         initial_configuration,
                         # contex_value,
                         mspl,
                         spl_groups,
                         id_repository):
    """
    Given a list of packages it creates its hyvarrec SPL
    """

    spls = {}

    logging.debug("Start computing the transitive closure of dependencies")
    to_process = set(package_request)
    to_process.update(initial_configuration.keys())
    # todo: this part can be more efficient using union find
    while to_process:
        i = to_process.pop()
        spls[i] = get_transitive_closure_of_dependencies(mspl,spl_groups,i)
        to_process.difference_update(spls[i])
        intersections = [x for x in spls if spls[i].intersection(spls[x]) and x != i]
        if intersections:
            for j in intersections:
                spls[i].update(spls[j])
                del(spls[j])
    logging.debug("Transitive closure of dependencies computed.")

    jsons = []
    for i in spls:
        data = {"attributes": [],
                "contexts": [],
                    # {"id": "context[" + utils.CONTEXT_VAR_NAME + "]",
                    #           "min": 0,
                    #           "max": len(map_name_id["context_int"])-1}],
                "configuration": {
                    "selectedFeatures": [],
                    "attribute_values": [],
                    "context_values": []},
                    # "context_values": [{"id": "context[" + utils.CONTEXT_VAR_NAME + "]",
                    #                     "value": map_name_id["context_int"][contex_value]}]},
                "constraints": [],
                "preferences": [],
                "smt_constraints": {
                    "formulas": [],
                    "features": [],
                    "other_int_symbols": [ "context[" + utils.CONTEXT_VAR_NAME + "]"] }
                }

        # add the constraints of the packages
        for j in spls[i]:
            if j in mspl:
                data["smt_constraints"]["formulas"].extend(hyportage_data.spl_get_smt_constraint(mspl[j]))
            # no need to add features since they are already boolean values

        # add constraints to select the required packages
        data["smt_constraints"]["formulas"].extend(request_constraints)

        # add info about the initial configuration
        for j in initial_configuration:
            if j in mspl and j in spls[i]:
                for k in initial_configuration[j][0]:
                    if k in hyportage_ids.id_repository_get_use_flag_from_spl_name(id_repository,j):
                        data["configuration"]["selectedFeatures"].append(
                            smt_encoding.get_hyvar_use(id_repository,j,k))
                    else:
                        logging.warning("The initial flag " + k + " was not available for the package " + j)

        # add preferences: do not remove packages already installed
        data["preferences"].append( " + ".join(
            [smt_encoding.get_hyvar_spl_name(id_repository,pkg) for pkg in initial_configuration
			 if pkg in spls[i]]))

        logging.debug("SPL created : constraints " + unicode(len(data["constraints"])) +
                      ", smt formulas " + unicode(len(data["smt_constraints"]["formulas"])))
        logging.debug("Packages to configure " + unicode(len(spls[i])))

        jsons.append({"json":data, "deps": spls[i]})
    return jsons


def update_configuration(hyvarrec_out,configuration,id_repository):
    pkgs = []
    flags = []
    for i in hyvarrec_out["features"]:
        el = hyportage_ids.id_repository_get_ids(id_repository)[i[1:]]
        if el[0] == "package": # el = ("package", spl_name)
            pkgs.append(el[1])
        else: # el = ("use", use, spl_name)
            flags.append((el[2],el[0]))

    for p in pkgs:
        if p not in configuration:
            configuration[p] = []
    for p,f in flags:
        if p not in configuration:
            logging.error("The output of hyvar-rec sets the flag " + f + " but its package " + p +
                          " was not selected.")
        else:
            configuration[p].append(f)


def get_diff_configuration(new_conf,old_conf):
    """
    Compute the diff from the intial configuration
    Assumes that in new_conf there are not spl_group packages
    """
    data = {"toUpdate": {}, "toInstall": {}, "toRemove": {}}
    for i in new_conf:
        if i in old_conf:
            if set(new_conf[i]) != set(old_conf[i][0]):
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


def get_better_constraint_visualization(constraints,mspl,id_repository):
    ls = []
    parser = SmtLib20Parser()
    for i in constraints:
        f = cStringIO.StringIO(i)
        script = parser.get_script(f)
        f.close()
        formula = script.get_last_formula()
        formula = pysmt.shortcuts.to_smtlib(formula,daggify=False)
        # # translate contexts
        # nums = re.findall('\(=\s*' + utils.CONTEXT_VAR_NAME + '\s*([0-9]+)\)',formula)
        # for i in nums:
        #     num = int(i)
        #     env = [ x for x in map_name_id['context_int'] if map_name_id['context_int'][x] == num]
        #     assert len(env) == 1
        #     formula = re.sub('\(=\s*' + utils.CONTEXT_VAR_NAME + '\s' + i + '\)', 'env(' + env[0] + ')',formula)
        # translate packages
        where_declared = "user-required: "
        pkgs = set(re.findall('p([0-9]+)',formula))
        for pkg in pkgs:
            name = id_repository.ids[pkg][1]
            formula = re.sub('p' + pkg,name,formula)
            if i in hyportage_data.spl_get_smt_constraint(mspl[name]):
                where_declared = name + ": "

        # translate uses
        uses = set(re.findall('u([0-9]+)', formula))
        for use in uses:
            formula = re.sub('u' + use, id_repository.ids[pkg][2] + "[[" + id_repository.ids[pkg][1] + "]]", formula)
        ls.append(where_declared + formula)
    return ls



@click.command()
@click.option(
	'--input-file', '-i',
    type=click.Path(exists=True, file_okay=True, dir_okay=False, writable=False, readable=True, resolve_path=True),
    help="File generated by using the hyportage translate functionality",
    default="host/data/hyportage/hyportage.enc")
@click.option(
    '--request-file',
    type=click.Path(exists=True, file_okay=True, dir_okay=False, writable=False, readable=True, resolve_path=True),
    help="Request file, following the dependency syntax (more than one line is allowed)",
    default="myreq")
# @click.option(
#     '--configuration_file',
#     type=click.Path(exists=True, file_okay=True, dir_okay=False, writable=False, readable=True, resolve_path=True),
#     help="File representing the current configuration of the system",
#     default="host/configuration/package.use")
# @click.option(
#     'new_configuration_file',
#     type=click.Path(exists=False, file_okay=True, dir_okay=False, writable=True, readable=True, resolve_path=True))
# @click.option(
#     'package_use_file',
#     type=click.Path(exists=False, file_okay=True, dir_okay=False, writable=True, readable=True, resolve_path=True))
@click.option(
    '--emerge_commands_file',
    type=click.Path(exists=False, file_okay=True, dir_okay=False, writable=True, readable=True, resolve_path=True),
    help="Script command to execute emerge to install the computed packages",
    default="emerge.sh")

# @click.option('--environment', default="amd64", help="Keyword identifying the architecture to use.")
@click.option(
	'--verbose', '-v',
	count=True,
	help="Print debug messages.")
@click.option('--keep', '-k', is_flag=True, help="Do not delete intermediate files.")
@click.option('--explain', is_flag=True, help="Run HyVarRec in explanation mode.")
@click.option('--url', '-r', default="", help='URL of the remote hyvarrec to use if available (local command otherwise used).')
@click.option('--par', '-p', type=click.INT, default=-1, help='Number of process to use for running the local HyVarRec.')
@click.option(
	'--save-modality',
	type=click.Choice(["json", "gzjson", "marshal", "pickle"]), default="pickle",
	help='Saving modality. Marshal is supposed to be faster but python version specific.')
def main(input_file,
         request_file,
         emerge_commands_file,
         # environment,
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
    if verbose != 0:
        if verbose == 1:
            logging.basicConfig(format="%(levelname)s: %(message)s", level=logging.WARNING)
        elif verbose == 2:
            logging.basicConfig(format="%(levelname)s: %(message)s", level=logging.INFO)
        elif verbose >= 3:
            logging.basicConfig(format="%(levelname)s: %(message)s", level=logging.DEBUG)
        logging.warning("Verbose (" + str(verbose) + ") output.")
    else:
        logging.basicConfig(format="%(levelname)s: %(message)s", level=logging.ERROR)

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

    # logging.info("Load the MSPL. This may take a while.")
    # t = time.time()
    # data = utils.load_data_file(input_file,save_modality)
    # mspl,map_name_id,map_id_name = data["mspl"],data["map_name_id"],data["map_id_name"]
    # logging.info("Loading completed in " + unicode(time.time() - t) + " seconds.")

    logging.info("Loading the stored hyportage data.")
    t = time.time()
    hyportage_file_path = os.path.abspath(input_file)
    pattern_repository, id_repository, mspl, spl_groups, core_configuration, installed_spls = \
        translate_portage.load_hyportage(hyportage_file_path, save_modality)
    logging.info("Loading completed in " + unicode(time.time() - t) + " seconds.")

    logging.info("Load the request package list.")
    t = time.time()
    dependencies,constraints = load_request_file(request_file,pattern_repository,id_repository,mspl,spl_groups,core_configuration)
    logging.info("Loading completed in " + unicode(time.time() - t) + " seconds.")
    logging.debug("Dependencies: " + unicode(dependencies))
    logging.debug("Constraints: " + unicode(constraints))

    # logging.info("Load the configuration file.")
    # t = time.time()
    # initial_configuration = load_configuration_file(configuration_file)
    # logging.info("Loading completed in " + unicode(time.time() - t) + " seconds.")
    #

    logging.info("Computing the SPLs.")
    t = time.time()
    to_solve = create_hyvarrec_spls(dependencies,
                                    constraints,
                                    installed_spls,
                                    # environment,
                                    mspl,
                                    spl_groups,
                                    id_repository)
    logging.info("Computation completed in " + unicode(time.time() - t) + " seconds.")
    logging.info("SPL to process: " + unicode(len(to_solve)))

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
                    json_result["constraints"],mspl,id_repository)
                sys.stderr.write("Conflict detected. Explanation:\n" + "\n".join(constraints) + '\n')
            logging.error("Conflict detected. Impossible to satisfy the request. Exiting.")
            sys.exit(1)
        logging.debug("HyVarRec output: " + unicode(json_result))
        # update the info on the final configuration
        update_configuration(json_result,configuration,id_repository)

    # remove all the pacakges without version from final configuration
    for i in configuration.keys():
        if i in mspl:
            del(configuration[i])

    configuration_diff = get_diff_configuration(configuration,installed_spls)
    logging.debug("Packages to update flags: " + unicode(len(configuration_diff["toUpdate"])))
    logging.debug("Packages to install: " + unicode(len(configuration_diff["toInstall"])))
    logging.debug("Packages to remove: " + unicode(len(configuration_diff["toRemove"])))
    # print in std out the diff of the new configuration
    print(json.dumps(configuration_diff,indent=1))

    logging.debug("Generate emerge commands to run.")
    with open(emerge_commands_file, "w") as f:
        f.write("#!/bin/bash\n")
        if configuration_diff["toRemove"].keys():
            f.write("emerge --unmerge " + " ".join(["=" + x for x in configuration_diff["toRemove"].keys()]) + "\n")
        if configuration_diff["toUpdate"].keys() + configuration_diff["toInstall"].keys():
            f.write("emerge -a --newuse " + " ".join(["=" + x for x in configuration_diff["toUpdate"].keys()]) +
                " " + " ".join(["=" + x for x in configuration_diff["toInstall"].keys()]) + "\n")

    # logging.debug("Printing the final configuration with all the positive and negative use flags.")
    # final_conf = get_conf_with_negative_use_flags(configuration,map_name_id)
    # with open(new_configuration_file,"w") as f:
    #     json.dump(final_conf,f,indent=1)

    # logging.debug("Printing the package.use file.")
    # with open(package_use_file,"w") as f:
    #     for i in final_conf.keys():
    #         f.write("=" + i + " " + " ".join(final_conf[i]) + "\n")

    logging.info("Cleaning.")
    clean()
    logging.info("Execution terminated correctly.")


if __name__ == "__main__":
    main()