
__author__ = "Michael Lienhardt & Jacopo Mauro"
__copyright__ = "Copyright 2017, Michael Lienhardt & Jacopo Mauro"
__license__ = "ISC"
__version__ = "0.5"
__maintainer__ = "Michael Lienhardt & Jacopo Mauro"
__email__ = "michael.lienhardt@laposte.net & mauro.jacopo@gmail.com"
__status__ = "Prototype"

import os
import utils
import json
import logging
import multiprocessing
import click
import time
import sys

import hyportage_from_egencache
import hyportage_data
#import constraint_parser
#import extract_id_maps
#import extract_dependencies
#import extract_package_groups
import smt_encoding


def usage():
	"""Print usage"""
	print(__doc__)


######################################################################
### LOADING SPL FROM EGENCACHE FILE
######################################################################

def filter_egencache_file(path_file, last_update):
	return last_update < os.path.getmtime(path_file)

def filter_egencache_file_full(path_file, last_update, patterns):
	if last_update < os.path.getmtime(path_file):
		return True
	for pattern in patterns:
		if hyportage_pattern.match_package_path(path_file):
			return True
	return False


######################################################################
### USE CONFIGURATION MANIPULATION
######################################################################

@click.command()
@click.argument(
	'dir_portage',
	#help="the directory containing the portage files",
	type=click.Path(exists=True, file_okay=False, dir_okay=True, writable=False, readable=True, resolve_path=True))
@click.argument(
	'dir_hyportage',
	#help="the directory containing the hyportage files (generate by this tool)",
	type=click.Path(exists=False, file_okay=False, dir_okay=True, writable=True, readable=True, resolve_path=True))
@click.option(
	'--input-files', '-i',
	nargs=4,
	default=("profile_configuration.json", "user_configuration.json", "installed_packages.json", "packages"),
	help='the three json files in which are stored the portage data, plus the folder in which the egencache portage files can be found')
@click.option(
	'--output-files', '-o',
	nargs=2,
	default=("hyportage.enc", "annex.enc"),
	help='the file in which are saved the hyportage data')
@click.option(
	'--verbose', '-v',
	count=True,
	help="Print debug messages.")
@click.option(
	'--par', '-p',
	type=click.INT, default=-1,
	help='Number of process to use for translating the dependencies. Default all processors available - 1.')
@click.option(
	'--force',
	default=None,
	help='force the translation of the given packages.')
@click.option(
	'--simplify-mode',
	type=click.Choice(["default","individual"]), default="default",			   # UNCLEAR
	help='Simplify the dependencies togheter of just one by one (useful for getting explanations.')  # UNCLEAR
#@click.option('--translate-only',
#	is_flag=True,
#	help="Only performs only the translation into SMT formulas.")
@click.option(
	'--save-modality',
	type=click.Choice(["json","marshal"]), default="json",
	help='Saving modality. Marshal is supposed to be faster but python version specific.')
def main(
	dir_portage,
	dir_hyportage,
	input_files,
	output_files,
	verbose,
	par,
	force,
	simplify_mode,
	save_modality
	):
	"""
	Tool that converts the gentoo files

	dir_portage directory containing the engencache portage files (see https://wiki.gentoo.org/wiki/Egencache).
	Usually it is ../../../host/portage/gen/md5-cache

	dir_hyportage directory where all the files resulting of the translation will be put
	Usually it is ../../../host/portage/json

	Example: python translate_portage.py -v --translate-only "sys-fs/udev-232-r2" ../../../host/portage/usr/portage/metadata/md5-cache ../../../host/portage/json/hyvarrec
	Example: python translate_portage.py -v ../../../host/portage/usr/portage/metadata/md5-cache ../../../host/portage/json/hyvarrec
	Example: python translate_portage.py -v -p 1 --use-existing-data ../../../host/portage/json/hyvarrec/hyvar_mspl.gentoorec --translate-only ../../../host/portage/usr/portage/metadata/md5-cache ../../../host/portage/json/hyvarrec

	"""

	##########################################################################
	### 1. OPTIONS
	##########################################################################

	# OPTION: manage number of parallel threads
	if par != -1:
		available_cores = min(par, multiprocessing.cpu_count())
	else:
		available_cores = max(1, multiprocessing.cpu_count() - 1)

	# create concurrency maps
	if available_cores > 1 and not force:
		pool = multiprocessing.Pool(available_cores)
		pool_thread = multiprocessing.dummy.Pool(available_cores)
		concurrent_map = pool.map
		concurrent_thread_map = pool_thread.map
	else:
		concurrent_map = map
		concurrent_thread_map = map

	# OPTION: manage verbosity
	logging.basicConfig(format="%(levelname)s: %(message)s", level=logging.INFO)
	if verbose != 0: logging.info("Verbose (" + str(verbose) + ") output.")
	else: logging.basicConfig(format="%(levelname)s: %(message)s", level=logging.ERROR)

	if verbose == 1: logging.basicConfig(format="%(levelname)s: %(message)s", level=logging.WARNING)
	elif verbose == 2: logging.basicConfig(format="%(levelname)s: %(message)s", level=logging.DEBUG)
	elif verbose >= 3: logging.basicConfig(format="%(levelname)s: %(message)s", level=logging.INFO)


	##########################################################################
	### 2. COMPUTE WHAT TO DO
	##########################################################################

	dir_portage = os.path.abspath(dir_portage)
	dir_hyportage = os.path.abspath(dir_hyportage)

	input_files_portage_profile_configuration, input_files_portage_user_configuration, input_files_portage_installed_packages, input_files_portage_packages = input_files
	path_portage_profile_configuration = os.path.join(dir_portage, input_files_portage_profile_configuration)
	path_portage_user_configuration = os.path.join(dir_portage, input_files_portage_user_configuration)
	path_portage_installed_packages = os.path.join(dir_portage, input_files_portage_installed_packages)
	path_portage_packages = os.path.join(dir_portage, input_files_portage_packages)

	output_files_hyportage, output_files_annex = output_files
	path_hyportage = os.path.join(dir_hyportage, output_files_hyportage)
	path_hyportage_annex = os.path.join(dir_hyportage, output_files_annex)

	## compute the difference from the previous state

	logging.info("Computing what to do.")
	t = time.time()
	last_update = 0.0
	if os.path.exists(path_hyportage_annex):
		last_update = os.path.getmtime(path_hyportage_annex)
		with open(path_hyportage_annex, 'r') as f:
			hyportage_annex = hyportage_annex_from_save_format(utils.load_data_file(f, save_modality))
	else:
		hyportage_annex = hyportage_data.hyportage_annex_create()

	must_apply_profile = ( last_update < os.path.getmtime(path_portage_profile_configuration) )
	must_apply_user = ( last_update < os.path.getmtime(path_portage_user_configuration) )

	egencache_files = hyportage_from_egencache.get_egencache_files()
	if force:
		patterns = [ hyportage_pattern.pattern_create_from_atom(atom) for atom in force.split() ]
		filter_function = lambda path_file: filter_egencache_file_full(path_file, last_update, patterns)
	else:
		filter_function = lambda path_file: filter_egencache_file(path_file, last_update)
	egencache_files_to_load = filter(filter_function, egencache_files)

	logging.info("Computation completed in " + unicode(time.time() - t) + " seconds.")


	##########################################################################
	### 3. UPDATE THE MSPL DATA IF NECESSARY
	##########################################################################

	nb_egencache_files_to_load = len(egencache_files_to_load)
	if nb_egencache_files_to_load > 0:
		mspl_loaded = True

		## load hyportage files

		logging.info("Loading the " + str(len(egencache_files_to_load)) + "egencache files.")
		raw_spls = concurrent_map(load_spl_from_egencache_file, egencache_files_to_load)
		logging.info("Loading completed in " + unicode(time.time() - t) + " seconds.")

		## load the full mspl data, and remove overwritten data

		logging.info("Loading the stored mspl.")
		with open(path_hyportage, 'r') as f:
			pattern_repository, id_repository, mspl, spl_groups = hyportage_data.hyportage_from_save_format(utils.load_data_file(f, save_modality))		

		package_to_add	= []
		package_to_update = []
		for spl in raw_spls:
			if hyportage_data.spl_get_name(spl) in mspl: package_to_update.append(spl)
			else: package_to_add.append(spl)
		package_name_to_remove = hyportage_data.hyportage_annex_get_package_list(hyportage_annex) - [ hyportage_from_egencache.get_package_name_from_path(f)[0] for f in egencache_files ]
		package_update_info = [ (hyportage_data.spl_get_name(spl), spl) for spl in package_to_update ] + [ (el, None) for el in package_name_to_remove ]

		for package_name, new_spl in package_update_info: # remove these spl from the loaded data if present
			old_spl = mspl.pop(package_name)
			# update pattern repository
			if new_spl:
				hyportage_pattern.pattern_repository_update(pattern_repository, old_spl, new_spl)
				hyportage_data.spl_group_replace_spl(spl_groups, old_spl, new_spl)
			else:
				hyportage_pattern.pattern_repository_remove(pattern_repository, old_spl)
				hyportage_data.spl_group_remove_spl(spl_groups, old_spl)
			# remove entries from id repository: must be entierly re-generated
			hyportage_ids.hyportage_id_repository_remove_spl(id_repository, package_name)
		logging.info("Loading completed in " + unicode(time.time() - t) + " seconds.")

	else: # no update to perform on the content of the mspl data, do not load anything
		mspl_loaded = False
		#logging.info("Loading the stored mspl.")
		#with open(path_hyportage, 'r') as f:
		#	pattern_repository, id_repository, mspl, spl_groups = hyportage_data.hyportage_from_save_format(utils.load_data_file(f, save_modality))		
		#logging.info("Loading completed in " + unicode(time.time() - t) + " seconds.")


	##########################################################################
	### 4. APPLY THE CONFIGURATION IF NECESSARY, AND REGENERATE THE IDS
	##########################################################################

## DONE UNTIL HERE

	# profile configuration
	if must_apply_profile:
		if not mspl_loaded:
			mspl_loaded = True
			logging.info("Loading the stored mspl.")
			with open(path_hyportage, 'r') as f:
				pattern_repository, id_repository, mspl, spl_groups = hyportage_data.hyportage_from_save_format(utils.load_data_file(f, save_modality))		
			logging.info("Loading completed in " + unicode(time.time() - t) + " seconds.")
		with open(path_portage_profile_configuration, 'r') as f:
			profile_configuration = configuration.configuration_from_save_format(utils.load_data_file(f, save_modality))
		# apply the configuration on all spl in the mspl

	elif nb_egencache_files_to_load > 0:
		with open(path_portage_profile_configuration, 'r') as f:
			profile_configuration = configuration.configuration_from_save_format(utils.load_data_file(f, save_modality))
		# apply the configuratin on all spl in raw_spl


	# user configuration


	# 3.3. update the ids
		with open(path_portage_user_configuration, 'r') as f:
			user_configuration = configuration.configuration_from_save_format(utils.load_data_file(f, save_modality))

	if os.path.exists(path_hyportage):
		logging.info("Loading the existing file.")
		t = time.time()
		last_update = os.path.getmtime(path_hyportage)
		hyportage = utils.load_data_file(path_hyportage, save_modality)
		logging.info("Loading completed in " + unicode(time.time() - t) + " seconds.")
	else:
		hyportage = { 'arch': [], 'mspl': {}, 'patterns': {}, 'name_to_id': {}, 'id_to_name': {} }

	# 2. check if there is something to do
	logging.info("Load the egencache files.")
	t = time.time()




	if force:
		patterns = [ constraint_parser.pattern_create_from_atom(atom) for atom in force.split() ]
		filter_function = lambda path_file: filter_egencache_file_full(path_file, last_update, patterns)
	else:
		filter_function = lambda path_file: filter_egencache_file(path_file, last_update)

	# NOT WORKING: need to know also which packages are removed
	egencache_files_to_load = utils_portage.get_egencache_files(os.path.join(dir_portage, path_portage_packages), filter_function)

	fully_apply_profile = ( last_update < os.path.getmtime(os.path.join(dir_portage, filename_portage_profile_configuration)) )
	fully_apply_user = ( last_update < os.path.getmtime(os.path.join(dir_portage, filename_portage_user_configuration)) )

	logging.debug("Considering " + unicode(len(egencache_files_to_load)) + " files")

	# 3. load the new data
	spls = concurrent_map(load_spl_from_egencache_file, egencache_files_to_load)
	logging.info("Loading completed in " + unicode(time.time() - t) + " seconds.")

	# need to update the package group, the pattern mapping, and the other data in a consistent way






"""


	# setup the output directory
	if not os.path.exists(dir_hyportage):
		os.makedirs(dir_hyportage)

	if not translate_only:
		logging.info("Load the egencache files.")
		t = time.time()
		if translate_only_package: # process just one package
			files = [os.path.join(dir_portage,translate_only_package)]
			logging.info("Loading completed in " + unicode(time.time() - t) + " seconds.")
		else:
			files = egencache_utils.get_egencache_files(dir_portage)
			logging.info("Loading completed in " + unicode(time.time() - t) + " seconds.")

		# continues the translation, following the different steps
		logging.debug("Considering " + unicode(len(files)) + " files")
		t = time.time()
		raw_mspl = egencache_utils.load_files_egencache(concurrent_thread_map, files)
		logging.info("Loading completed in " + unicode(time.time() - t) + " seconds.")
		assert raw_mspl
	
		logging.info("Converting the gentoo dependencies into internal AST representation.")
		t = time.time()
		asts = constraint_parser.parse_mspl(concurrent_map, raw_mspl)
		#asts = map(constraint_parser.parse_spl, raw_mspl)
		logging.info("Conversion completed in " + unicode(time.time() - t) + " seconds.")
		assert asts

		logging.info("Creating the package group information.")
		package_groups = extract_package_groups.from_mspl_list(concurrent_map, raw_mspl)
		assert package_groups

		logging.info("Matching every atoms constraint to the list of its correponding spls.")
		t = time.time()
		atom_mapping = atom_matching.extract_atom_mapping(concurrent_thread_map, package_groups, asts)
		logging.info("Extraction completed in " + unicode(time.time() - t) + " seconds.")
		assert atom_mapping
	
		logging.info("Extending spl with implicit iuse declarations")
		t = time.time()
		# profile_iuse = ???
		#apply_profile.on_mspl(concurrent_map, atom_mapping, asts, profile_iuse)
		logging.info("Completion completed in " + unicode(time.time() - t) + " seconds.")

		logging.info("Extracting ids information from ASTs.")
		t = time.time()
		mappings = extract_id_maps.create_empty_name_mappings()
		map_id_name, map_name_id = mappings
		mappings_list = concurrent_thread_map(extract_id_maps.generate_name_mappings_spl, raw_mspl)
		map(lambda x: extract_id_maps.update_name_mappings(mappings, x), mappings_list)
		#map_id_name, map_name_id = extract_id_maps.generate_name_mappings(concurrent_map,raw_mspl,asts)
		logging.info("Extraction completed in " + unicode(time.time() - t) + " seconds.")

		logging.info("Start to create the mspl dictionary.")
		# add name : spl
		mspl = {spl['name']: spl for spl in raw_mspl}
		# add asts
		for spl, local_ast, combined_ast in asts:
			spl['fm'] = {'local': local_ast, 'combined': combined_ast}

		logging.info("Extract dependencies information from ASTs.")
		all_pkg_names = set(mspl.keys())
		t = time.time()
		extract_dependencies.generate_dependencies_mspl(concurrent_thread_map, mspl)
		t = time.time() - t
		logging.info("Extraction completed in " + unicode(t) + " seconds.")
	
		# clean the package groups from links to their different implementations
		extract_package_groups.clean(concurrent_map, package_groups)
		# update the mspl dictionary with the package groups
		extract_id_maps.update_name_mappings(mappings, extract_id_maps.generate_name_mappings_package_groups(package_groups))
		#package_groups = generate_package_groups(concurrent_map,raw_mspl,map_name_id,map_id_name)
		# add the package groups to the mspl
		# context keywords are treaded differently
		extract_id_maps.add_context_ints(map_name_id)
		mspl.update(package_groups)

	logging.info("Generation of SMT formulas.")
	t = time.time()
	# this process is too memory consuming. Using map instead of a concurrent map
	# not possible to use threads due to the use of z3 :-(
	if translate_only_package:
		formulas = [smt_encoding.convert((mspl, map_name_id, simplify_mode, translate_only_package))]
	else:
		formulas = smt_encoding.generate_formulas(map,mspl,map_name_id,simplify_mode)
	logging.info("Generation completed in " + unicode(time.time() - t) + " seconds.")
	# add formulas in mspl
	for spl_name, formula_list in formulas:
		mspl[spl_name]["smt_constraints"] = formula_list

	# todo save into file (compressed if possible and option using marshal)
	logging.info("Saving the file.")
	t = time.time()
	final_data = { "mspl": mspl, "map_name_id": map_name_id, "map_id_name": map_id_name }
	utils.store_data_file(os.path.join(dir_hyportage, output_file_name),final_data,save_modality)
	logging.info("Saving completed in " + unicode(time.time() - t) + " seconds.")"""

if __name__ == "__main__":
	main()

