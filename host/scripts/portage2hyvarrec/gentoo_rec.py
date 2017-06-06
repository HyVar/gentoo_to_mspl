
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

import md5_cache_utils
import parser
import ast_visitor
import extract_id_maps


def usage():
    """Print usage"""
    print(__doc__)


# extracting package groups
def generate_package_groups(pool,mspl):
    global package_groups
    information_list = pool.map(__gpg_util, mspl)
    package_groups = {}
    for group_name, version, spl_name in information_list:
        if group_name in package_groups:
            package_groups[group_name]['implementations'][version] = spl_name
            package_groups[group_name]['dependencies'].extend(spl_name)
        else:
            package_groups[group_name] = {'implementations': {version: spl_name}, 'dependencies': [spl_name]}
    return package_groups
def __gpg_util(spl):
    '''
    Auxiliary function used for a pool.map call in generate_package_groups
    '''
    return ( spl['group_name'], spl['versions']['full'], spl['name'])


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
@click.option('--translate-only', default="", help='Package to convert - Do not convert all the other ones.')
def main(input_dir,target_dir,no_opt,verbose,par,translate_only):
    """
    Tool that converts the gentoo files

    INPUT_DIR directory containing the mspl and spl directories.
    Usually it is ../../../host/portage/gen/md5-cache

    TARGET_DIR output directory

    Example: python gentoo_rec.py --translate-only "sys-fs/udev-232-r2" "../../../host/portage/gen/md5-cache" /dev/null
    """

    # todo handle trust feature declaration in portage file
    # trust_feature_declaration = True

    if par > 1:
        available_cores = max(par, multiprocessing.cpu_count())
    else:
        available_cores = max(1, multiprocessing.cpu_count() - 1)
    if verbose:
        logging.basicConfig(format="%(levelname)s: %(message)s", level=logging.DEBUG)
        logging.info("Verbose output.")

    if not os.path.exists(target_dir):
        os.makedirs(target_dir)


    logging.info("Load the md5_cache files.")
    if translate_only:
        # process just one package
        files = [os.path.join(input_dir,translate_only)]
    else:
        files = md5_cache_utils.get_egencache_files(input_dir)
    t = time.time()
    if available_cores > 1 and len(files) > 1:
        pool = multiprocessing.Pool(available_cores)
        mspl = pool.map(md5_cache_utils.load_file_egencache, )
    else:
        mspl = map(md5_cache_utils.load_file_egencache, md5_cache_utils.get_egencache_files(input_dir))
    t = time.time() - t
    logging.info("Loading completed in " + unicode(t))
    assert mspl

    logging.info("Converting the gentoo dependencies into internal AST representation.")
    t = time.time()
    if available_cores > 1 and len(files) > 1:
        pool = multiprocessing.Pool(available_cores)
        asts = pool.map(parser.parse_spl, mspl)
    else:
        asts = map(parser.parse_spl, mspl)
    t = time.time() - t
    logging.info("Conversion completed in " + unicode(t))
    assert asts


    logging.info("Extracting ids information from ASTs.")
    t = time.time()
    pool = multiprocessing.dummy.Pool(available_cores)
    map_name_id, map_id_name = extract_id_maps.generate_name_mappings(pool,mspl,asts)
    t = time.time() - t
    logging.info("Extraction completed in " + unicode(t))

    #logging.info("Write map of names in " + utils.NAME_MAP_FILE)
    # with open(os.path.join(target_dir, utils.NAME_MAP_FILE), 'w') as f:
    #     json.dump({"name_to_id": map_name_id, "id_to_name": map_id_name}, f)
    # 2. generate the dependencies

    logging.info("Extract dependecies information from ASTs.")
    t = time.time()
    if available_cores > 1 and len(files) > 1:
        pool = multiprocessing.dummy.Pool(available_cores)
        dependencies = pool.map(extract_id_maps.generate_dependencies_ast,asts)
    else:
        dependencies = map(extract_id_maps.generate_dependencies_ast, asts)
    t = time.time() - t
    logging.info("Extraction completed in " + unicode(t))


    logging.info("Start to create the data dictionary.")
    # add name : spl
    data = {spl['name']: spl for spl in mspl}
    # add dependencies
    for spl_name,deps in dependencies:
        data[spl_name]['dependencies'] = deps
    # add asts
    for spl_name, local_ast, combined_ast in asts:
        data[spl_name]['fm'] = {'local': local_ast, 'combined': combined_ast}
    # generate the package groups
    pool = multiprocessing.dummy.Pool(available_cores)
    package_groups = generate_package_groups(pool,mspl)
    data.update(package_groups)

    # todo conversion into smt
    # todo save into file (compressed if possible and option using marshal)


if __name__ == "__main__":
    main()

