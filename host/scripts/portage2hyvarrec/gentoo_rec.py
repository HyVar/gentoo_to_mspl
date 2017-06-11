
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
import logging
import multiprocessing
import click
import time
import sys

import egencache_utils
import constraint_parser
import extract_id_maps
import extract_dependencies
import extract_package_groups
import smt_encoding


def usage():
    """Print usage"""
    print(__doc__)


def read_load_data_file(file_name):
    with open(file_name, "r") as f:
        data = json.load(f)
    return data["mspl"],data["map_name_id"],data["map_id_name"]


def store_data_file(file_name,mspl,map_name_id,map_id_name):
    final_data = {
        "mspl": mspl,
        "map_name_id": map_name_id,
        "map_id_name": map_id_name }
    with open(file_name, 'w') as f:
        json.dump(final_data, f)


@click.command()
@click.argument(
    'input_dir',
    type=click.Path(exists=True, file_okay=False, dir_okay=True, writable=False, readable=True, resolve_path=True))
@click.argument(
    'target_dir',
    type=click.Path(exists=False, file_okay=False, dir_okay=True, writable=True, readable=True, resolve_path=True))
@click.option('--verbose', '-v', is_flag=True, help="Print debug messages.")
@click.option('--par', '-p', type=click.INT, default=-1,
              help='Number of process to use for translating the dependencies. Default all processors available - 1.')
@click.option('--translate-only-package', default="", help='Package to convert - Do not convert all the other ones.')
@click.option('--simplify-mode', default="default", type=click.Choice(["default","individual"]),
              help='Simplify the dependencies togheter of just one by one (useful for getting explanations.')
@click.option('--use-existing-data', default="",
              help='File path of existing file to load.')
@click.option('--translate-only', is_flag=True, help="Performs only the translation into SMT formulas." + 
              " Requires the flag --use-existing-data.")
@click.option('--output-file-name', '-o', default="hyvar_mspl.json",
              help='Name (not path!) of the output file.')
def main(input_dir,
         target_dir,
         verbose,
         par,
         translate_only_package,
         simplify_mode,
         use_existing_data,
         translate_only,
         output_file_name):
    """
    Tool that converts the gentoo files

    INPUT_DIR directory containing the engencache portage files (see https://wiki.gentoo.org/wiki/Egencache).
    Usually it is ../../../host/portage/gen/md5-cache

    TARGET_DIR directory where all the files resulting of the translation will be put
    Usually it is ../../../host/portage/json

    Example: python gentoo_rec.py -v --translate-only "sys-fs/udev-232-r2" ../../../host/portage/usr/portage/metadata/md5-cache ../../../host/portage/json/hyvarrec
    Example: python gentoo_rec.py -v ../../../host/portage/usr/portage/metadata/md5-cache ../../../host/portage/json/hyvarrec
    Example: python gentoo_rec.py -v -p 1 --use-existing-data ../../../host/portage/json/hyvarrec/hyvar_mspl.json --translate-only ../../../host/portage/usr/portage/metadata/md5-cache ../../../host/portage/json/hyvarrec

    """

    # todo handle trust feature declaration in portage file
    # trust_feature_declaration = True

    # OPTION: manage number of parallel threads
    if par != -1:
        available_cores = min(par, multiprocessing.cpu_count())
    else:
        available_cores = max(1, multiprocessing.cpu_count() - 1)

    # manage concurrency
    if available_cores > 1 and not translate_only_package:
        pool = multiprocessing.Pool(available_cores)
        concurrent_map = pool.map
    else:
        concurrent_map = map

    # OPTION: manage verbosity
    if verbose:
        logging.basicConfig(format="%(levelname)s: %(message)s", level=logging.DEBUG)
        logging.info("Verbose output.")

    # OPTION: load data file if available
    if use_existing_data:
        if os.path.isfile(use_existing_data):
            logging.info("Loading the existing file.")
            t = time.time()
            mspl,map_name_id, map_id_name = read_load_data_file(use_existing_data)
            logging.info("Loading completed in " + unicode(time.time() - t) + " seconds.")
        else:
            logging.critical("The file " + use_existing_data + " can not be found.")
            sys.exit(1)

    # OPTION: check if the flag --translate-only is properly used
    if translate_only:
        if not use_existing_data:
            logging.critical("The option --translate-only requires the option --use-existing-data.")
            sys.exit(1)

    # setup the output directory
    if not os.path.exists(target_dir):
        os.makedirs(target_dir)

    if not translate_only:
        # starts the extraction
        logging.info("Load the egencache files.")
        if translate_only_package: # process just one package
            t = time.time()
            files = [os.path.join(input_dir,translate_only_package)]
            logging.info("Loading completed in " + unicode(time.time() - t) + " seconds.")
        else:
            files = egencache_utils.get_egencache_files(input_dir)

        # continues the translation, following the different steps
        logging.debug("Considering " + unicode(len(files)) + " files")
        t = time.time()
        raw_mspl = concurrent_map(egencache_utils.load_file_egencache, files)
        logging.info("Loading completed in " + unicode(time.time() - t) + " seconds.")
        assert raw_mspl
    
        logging.info("Converting the gentoo dependencies into internal AST representation.")
        t = time.time()
        asts = concurrent_map(constraint_parser.parse_spl, raw_mspl)
        #asts = map(constraint_parser.parse_spl, raw_mspl)
        logging.info("Conversion completed in " + unicode(time.time() - t) + " seconds.")
        assert asts
    
        logging.info("Extracting ids information from ASTs.")
        t = time.time()
        mappings = extract_id_maps.create_empty_name_mappings()
        map_id_name, map_name_id = mappings
        mappings_list = concurrent_map(extract_id_maps.generate_name_mappings_spl, raw_mspl)
        map(lambda x: extract_id_maps.update_name_mappings(mappings, x), mappings_list)
        # TODO: must remove the following lines when we start loading the profile
        mappings_list = concurrent_map(extract_id_maps.generate_use_mappings_ast, asts)
        map(lambda x: extract_id_maps.update_name_mappings(mappings, x), mappings_list)
        #map_id_name, map_name_id = extract_id_maps.generate_name_mappings(concurrent_map,raw_mspl,asts)
        logging.info("Extraction completed in " + unicode(time.time() - t) + " seconds.")

        logging.info("Extract dependencies information from ASTs.")
        t = time.time()
        dependencies = concurrent_map(extract_dependencies.generate_dependencies_ast, asts)
        t = time.time() - t
        logging.info("Extraction completed in " + unicode(t) + " seconds.")
    
    
        logging.info("Start to create the mspl dictionary.")
        # add name : spl
        mspl = {spl['name']: spl for spl in raw_mspl}
        # add dependencies
        for spl_name,deps in dependencies:
            mspl[spl_name]['dependencies'] = deps
        # add asts
        for spl_name, local_ast, combined_ast in asts:
            mspl[spl_name]['fm'] = {'local': local_ast, 'combined': combined_ast}
        # generate the package groups
        package_groups = extract_package_groups.create_empty_package_groups()
        package_groups_list = concurrent_map(extract_package_groups.generate_package_group_spl, raw_mspl)
        map(lambda x: extract_package_groups.update_package_groups(package_groups, x), package_groups_list)
        # update the mspl dictionary with the package groups
        extract_id_maps.update_name_mappings(mappings, extract_id_maps.generate_name_mappings_package_groups(package_groups))
        #package_groups = generate_package_groups(concurrent_map,raw_mspl,map_name_id,map_id_name)
        # add the package groups to the mspl
        mspl.update(package_groups)

    logging.info("Generation of SMT formulas.")
    t = time.time()
    formulas = smt_encoding.generate_formulas(concurrent_map,mspl,map_name_id,simplify_mode)
    logging.info("Generation completed in " + unicode(time.time() - t) + " seconds.")
    # add formulas in mspl
    for spl_name, formula_list in formulas:
        mspl[spl_name]["smt_constraints"] = {"formulas": formula_list, "features": []}

    # todo save into file (compressed if possible and option using marshal)
    logging.info("Saving the file.")
    t = time.time()
    store_data_file(os.path.join(target_dir, output_file_name),mspl,map_name_id,map_id_name)
    logging.info("Saving completed in " + unicode(time.time() - t) + " seconds.")

if __name__ == "__main__":
    main()

