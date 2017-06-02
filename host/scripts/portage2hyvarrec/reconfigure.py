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
from subprocess import PIPE
import psutil
import requests
import click

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


def run_hyvar(json_data,par,explain_modality):
    """
    Run hyvar locally assuming that there is a command hyvar-rec
    """
    file_name = settings.get_new_temp_file("json")
    with open(file_name,"w") as f:
        json.dump(json_data, f)
        # json.dump(json_data, f,indent=1)
    cmd = ["hyvar-rec"]
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


def get_transitive_closure_of_dependencies(pkgs):
    # returns the transitive closure of the dependencies as the set of packages to configure
    # dependencies left to configure is left as an empty set
    # the graph is not needed if we just want the close of the dependencies
    configures = set(pkgs)
    to_check = pkgs
    checked = set()
    while to_check:
        p = to_check.pop()
        for i in mspl[p]["configures"]:
            if i not in checked:
                to_check.append(i)
                configures.add(i)
        for i in mspl[p]["dependencies"]:
            if i not in checked:
                to_check.append(i)
                configures.add(i)
        checked.add(p)
    return configures,set()


def get_all_dependencies(pkg):
    # this fucntion get the transitive closure of all the configures exploitng the graph info
    # it also returns the first level of dependencies
    # unfortunately this is not enought since missing CTC between dependencies and configures are not captured
    base_pkg = re.sub(settings.VERSION_RE, "",pkg)
    # compute the configures. One level is enough because descendants contains already the transitive closure
    configures = set(mspl[base_pkg]["loop"] + mspl[base_pkg]["descendants"])
    # add the packages with versions
    for j in list(configures):
        configures.update(mspl[j]["implementations"].values())
    # compute the dependencies. One level should be enough
    depends = set()
    for j in configures:
        depends.update(mspl[j]["dependencies"])
    depends.difference_update(configures)
    return configures,depends


def create_hyvarrec_spls(package_request,initial_configuration,contex_value,no_selected_pkgs):
    """
    Given a list of packages it creates its hyvarrec SPL
    """
    # todo read list of configures and depends for all packages

    logging.info("Computing the SPL to generate")
    spls = {}
    dconf = {}
    ddep = {}

    to_process = set(package_request.keys())
    while to_process:
        i = to_process.pop()
        # dconf[i],ddep[i] = get_all_dependencies(i)
        # compute the transitive closure of the dependencies considering also the initial packages
        # initial packages are needed because we can not trust the initial configuration
        # and modification could brake it
        dconf[i], ddep[i] = get_transitive_closure_of_dependencies([i]+initial_configuration.keys())
        spls[i] = dconf[i].union(ddep[i])
        to_process.difference_update(spls[i])
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
        feature_symbols = set()
        for j in dconf[i]:
            json["attributes"].extend(mspl[j]["attributes"])
            json["constraints"].extend(mspl[j]["constraints"])
            if "smt_constraints" in mspl[j]:
                json["smt_constraints"]["formulas"].extend(mspl[j]["smt_constraints"]["formulas"])
                feature_symbols.update(mspl[j]["smt_constraints"]["features"])
        json["smt_constraints"]["features"] = list(feature_symbols)



        # add constraints to impose selection of requested packages considering slot and subslots
        for p in package_request.keys():
            if p in dconf[i]: # packages needs to be configured
                if "subslot" in package_request[p]:  # the package requires a specific slot/subslot
                    vs = [x for x in mspl[re.sub(settings.VERSION_RE, "", p)]["implementations"].values()
                          if package_request[p]["slot"] in map_name_id["name_to_id"]["slot"][x] and
                          package_request[p]["subslot"] in map_name_id["name_to_id"]["subslot"][x]]
                    # here we assume that a version can be installed only in one slots + subslot
                    c = settings.get_hyvar_or(
                        [settings.get_hyvar_package(map_name_id["name_to_id"]["package"][x]) + " = 1" for x in vs])
                    if c == "false":
                        logging.error("Package " + p + " can not be installed with desired slot/subslot. Existing.")
                        exit(1)
                    json["constraints"].append(c)
                elif "slot" in package_request[p]:
                    vs = [x for x in mspl[re.sub(settings.VERSION_RE, "", p)]["implementations"].values()
                          if package_request[p]["slot"] in map_name_id["name_to_id"]["slot"][x]]
                    # here we assume that a version can be installed only in one slots + subslot
                    c = settings.get_hyvar_or(
                        [settings.get_hyvar_package(map_name_id["name_to_id"]["package"][x]) + " = 1" for x in vs])
                    if c == "false":
                        logging.error("Package " + p + " can not be installed with desired slot. Existing.")
                        exit(1)
                    json["constraints"].append(c)
                else:
                    json["constraints"].append(
                        settings.get_hyvar_package(map_name_id["name_to_id"]["package"][p]) + " = 1")

                # add constraints to impose selection of requested features
                if "features" in package_request[p]:
                    json["constraints"].append(settings.get_hyvar_and(
                        [settings.get_hyvar_flag(map_name_id["name_to_id"]["flag"][p][x]) + " = 1"
                                                 for x in package_request[p]["features"]]))

        # the constraints added should also require the dependencies, if any.
        # the only missing constraint is the implication that a versioned package implies its base one
        ddep[i].difference_update(dconf[i])
        if ddep[i]:
            for j in ddep[i]:
                for k in mspl[j]["implementations"].values():
                    json["constraints"].append(settings.get_hyvar_impl(
                        settings.get_hyvar_package(map_name_id["name_to_id"]["package"][k]) + " = 1",
                        settings.get_hyvar_package(map_name_id["name_to_id"]["package"][j]) + " = 1"))

        # add constraints to impose deselection of not selected packages
        for j in no_selected_pkgs:
            if j in dconf[i] or j in ddep[i]:
                json["constraints"].append(
                    settings.get_hyvar_package(map_name_id["name_to_id"]["package"][j]) + " = 0")

        # add info about the initial configuration
        # only the flag features need to be defined. Preferences take care about packages
        for j in initial_configuration.keys():
            if j in dconf[i]:
                for k in initial_configuration[j]:
                    json["configuration"]["selectedFeatures"].append(
                        settings.get_hyvar_flag(map_name_id["name_to_id"]["flag"][j][k]))

        # add preferences: do not remove packages already installed
        c = "0 "
        for j in initial_configuration.keys():
            if j in dconf[i]:
                c += " + " + settings.get_hyvar_package(map_name_id["name_to_id"]["package"][j])
            elif j in ddep[i]:
                c += " + " + settings.get_hyvar_package(map_name_id["name_to_id"]["package"][j])
        json["preferences"].append(c)

        logging.debug("SPL created : attributes " + unicode(len(json["attributes"])) +
                      ", constraints " + unicode(len(json["constraints"])) +
                      ", smt formulas " + unicode(len(json["smt_constraints"]["formulas"])))
        logging.debug("Packages to configure " + unicode(len(dconf[i]))) # + " (" + unicode(dconf[i]) + ")")

        if ddep[i]:
            logging.debug("Dependencies not in configure: " + unicode(len(ddep[i])) + " (" + unicode(ddep[i]) + ")")
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


def get_diff_configuration(new_conf,old_conf):
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


def get_conf_with_negative_use_flags(conf):
    data = {}
    for i in conf.keys():
        all_flags = map_name_id["name_to_id"]["flag"][i].keys()
        positive_flags = conf[i]
        negative_flags = set(all_flags)
        negative_flags.difference_update(positive_flags)
        data[i] = positive_flags + [ "-" + x for x in negative_flags]
    return data



@click.command()
@click.argument(
    'input_dir',
    type=click.Path(exists=True, file_okay=False, dir_okay=True, writable=False, readable=True, resolve_path=True))
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
def main(input_dir,
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
         par):
    """
        input_dir -> Input directory containing the hyvar mspl json translation files
        request_file -> File containing the request
        configuration_file -> File containing the current configuration
        new_configuration_file -> File containing the new_configuration_file that will be generated
        package_use_file -> File containing the package.use file that will be generated and copied into the guest
        emerge_commands_file -> File containing the script to run in the guest to generate the configuration
    """

    global map_name_id
    global mspl
    global KEEP

    if keep:
        KEEP = True
    if verbose:
        logging.basicConfig(format="%(levelname)s: %(message)s", level=logging.DEBUG)
        logging.info("Verbose output.")

    logging.info("Load the MSPL. This may take a while.")
    load_mspl(input_dir)

    logging.info("Load the mapping between names and ids. This may take a while.")
    map_name_id = read_json(os.path.join(input_dir,settings.NAME_MAP_FILE))

    logging.info("Load the request package list.")
    # features can be requested only when the version of the package is defined
    package_request = read_json(request_file)
    for i in package_request.keys():
        if i not in mspl:
            logging.warning("The requested package " + i + " is not found and will be ignored.")
            del package_request[i]
        else:
            if "features" in package_request[i]:
                for j in list(package_request[i]["features"]):
                    if j not in map_name_id["name_to_id"]["flag"][i]:
                        logging.warning("The flag " + j + " for package "+ i + " is not found. Will be ignored.")
                        package_request[i]["features"].remove(j)

    logging.info("Load the configuration file.")
    initial_configuration = read_json(configuration_file)
    for i in initial_configuration.keys():
        if i in mspl:
            initial_configuration[i] = [x[1:] for x in initial_configuration[i]
                                        if x.startswith("+") and x[1:] in map_name_id["name_to_id"]["flag"][i]]
        else:
            logging.warning("Not found the package " + i + " defined in the initial configuration.")
            del(initial_configuration[i])

    # logging.info("Process the MSPL based on its dependencies graph")
    # utils.preprocess(mspl,initial_configuration,set(package_request.keys()))

    # start solving the reconfiguration problem for the package_requests
    configuration = {}
    confs_selected = set()
    confs_deselected = set() # includes also deps not selected
    deps_selected = set() # deps that were selected but not yet configured
    to_solve = create_hyvarrec_spls(package_request,initial_configuration,environment,confs_deselected)

    while to_solve:
        job = to_solve.pop()
        if url:
            json_result = run_remote_hyvar(job["json"],url)
        else:
            json_result = run_hyvar(job["json"],par,explain)
        #logging.debug("Answer obtained: " + unicode(json_result))
        if json_result["result"] != "sat":
            logging.error("Conflict detected. Impossible to satisfy the request. Exiting.")
            exit(1)
        logging.debug("HyVarRec output: " + unicode(json_result))
        # update the info on the final configuration
        update_configuration(json_result,configuration)
        confs_selected.update([x for x in job["confs"] if x in configuration])
        confs_deselected.update([x for x in job["confs"] if x not in configuration])
        confs_deselected.update([x for x in job["deps"] if x not in configuration])
        deps_selected.update(job["deps"])
        if deps_selected:
            deps_selected.difference_update(confs_selected)
        if deps_selected:
            deps_selected.difference_update(confs_deselected)
        # logging.debug("Configured " + unicode(confs_selected))
        # logging.debug("Not selected " + unicode(confs_deselected))
        # logging.debug("Remaining number of dependencies: " + unicode(len(deps_selected)) +
        #               "(" + unicode(deps_selected) + ")")
        # run hyvarrec on the remaining dependencies selected (deep first search of the MSPL)
        if len(to_solve) == 0 and deps_selected:
            logging.debug("Attemping to configure remaining dependency " + unicode(deps_selected))
            to_solve = create_hyvarrec_spls({p: {} for p in deps_selected},
                                      initial_configuration, environment, confs_deselected)

    # remove all the pacakges without version from final configuration
    for i in configuration.keys():
        if "implementations" in mspl[i]:
            del(configuration[i])

    configuration_diff = get_diff_configuration(configuration,initial_configuration)
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
    final_conf = get_conf_with_negative_use_flags(configuration)
    with open(new_configuration_file,"w") as f:
        json.dump(final_conf,f,indent=1)

    logging.debug("Printing the package.use file.")
    with open(package_use_file,"w") as f:
        for i in final_conf.keys():
            f.write("=" + i + " " + " ".join(final_conf[i]) + "\n")

    logging.info("Cleaning.")
    clean()
    logging.info("Execution gterminated correctly.")



if __name__ == "__main__":
    main()