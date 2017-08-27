
import os
import utils
import logging
import multiprocessing
import click


import hyportage_translation
import reconfigure

import core_data
import portage_data
import hyportage_data
import hyportage_pattern
import hyportage_ids
import hyportage_configuration


__author__ = "Michael Lienhardt & Jacopo Mauro"
__copyright__ = "Copyright 2017, Michael Lienhardt & Jacopo Mauro"
__license__ = "ISC"
__version__ = "0.5"
__maintainer__ = "Michael Lienhardt & Jacopo Mauro"
__email__ = "michael.lienhardt@laposte.net & mauro.jacopo@gmail.com"
__status__ = "Prototype"



def usage():
	"""Print usage"""
	print(__doc__)


######################################################################
# UTILITY FUNCTIONS
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


def load_hyportage(path_hyportage, save_modality):
	if os.path.exists(path_hyportage):
		if save_modality.endswith("json"):
			return hyportage_data.hyportage_data_from_save_format(utils.load_data_file(path_hyportage, save_modality))
		else:
			return utils.load_data_file(path_hyportage, save_modality)
	else:
		pattern_repository = hyportage_pattern.pattern_repository_create()
		id_repository = hyportage_ids.id_repository_create()
		mspl = hyportage_data.mspl_create()
		spl_groups = hyportage_data.spl_groups_create()
		core_configuration = hyportage_configuration.core_configuration_create()
		installed_spls = core_data.package_installed_create()
		return pattern_repository, id_repository, mspl, spl_groups, core_configuration, installed_spls


def load_configurations(path_profile_configuration, path_user_configuration):
	profile = portage_data.configuration_from_save_format(utils.load_data_file(path_profile_configuration, "json"))
	user = portage_data.configuration_from_save_format(utils.load_data_file(path_user_configuration, "json"))
	return profile, user


def save_hyportage(path_hyportage, pattern_repository, id_repository, mspl, spl_groups, core_configuration, installed_spls, save_modality):
	if save_modality.endswith("json"):
		utils.store_data_file(path_hyportage, hyportage_data.hyportage_data_to_save_format(
			pattern_repository, id_repository, mspl, spl_groups, core_configuration, installed_spls), save_modality)
	else:
		data = pattern_repository, id_repository, mspl, spl_groups, core_configuration, installed_spls
		utils.store_data_file(path_hyportage, data, save_modality)



######################################################################
# USE CONFIGURATION MANIPULATION
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
@click.argument(
	'dir_install',
	#help="the directory containing the hyportage files (generate by this tool)",
	type=click.Path(exists=False, file_okay=False, dir_okay=True, writable=True, readable=True, resolve_path=True))
@click.option(
	'--portage_files', '-i',
	nargs=4,
	default=("profile_configuration.json", "user_configuration.json", "keywords.json", "installed_packages.json", "packages"),
	help='the five json files in which are stored the portage data, plus the folder in which the egencache portage files can be found')
@click.option(
	'--hyportage_file', '-o',
	default="hyportage.enc",
	help='the file in which are saved the hyportage data')
@click.option(
	'--generated_install_files', '-u',
	default=("emerge.sh", "package.use"),
	help='the file in which are saved the installation script and use flag configuration')
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
	default=False,
	help='force the translation of the given packages.')
@click.option(
	'--simplify_mode',
	type=click.Choice(["default","individual"]), default="default",
	help='Simplify the dependencies togheter of just one by one (useful for getting explanations.')
@click.option(
	'--save-modality',
	type=click.Choice(["json", "gzjson", "marshal", "pickle"]), default="gzjson",
	help='Saving modality. Marshal is supposed to be faster but python version specific.')
@click.option(
	'--mode',
	type=click.Choice(["update", "emerge"]), default="update",
	help='Temporary option that states if the tool is used in translate mode or reconfigure mode.')
@click.argument(
	'atoms',
	nargs=-1)
def main(
		dir_portage,
		dir_hyportage,
		dir_install,
		portage_files,
		hyportage_file,
		generated_install_files,
		verbose,
		par,
		force,
		simplify_mode,
		save_modality,
		mode,
		atoms):
	"""
	Tool that converts the gentoo files

	dir_portage directory containing the engencache portage files (see https://wiki.gentoo.org/wiki/Egencache).
	Usually it is ../../../host/portage/gen/md5-cache

	dir_hyportage directory where all the files resulting of the translation will be put
	Usually it is ../../../host/portage/json

	Example: python hyportage.py -v --translate-only "sys-fs/udev-232-r2" ../../../host/portage/usr/portage/metadata/md5-cache ../../../host/portage/json/hyvarrec
	Example: python hyportage.py -v ../../../host/portage/usr/portage/metadata/md5-cache ../../../host/portage/json/hyvarrec
	Example: python hyportage.py -v -p 1 --use-existing-data ../../../host/portage/json/hyvarrec/hyvar_mspl.gentoorec --translate-only ../../../host/portage/usr/portage/metadata/md5-cache ../../../host/portage/json/hyvarrec

	"""

	##########################################################################
	# 1. OPTIONS
	##########################################################################

	# 1.1. verbose option
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

	# 1.2. parallel process option
	if par != -1: available_cores = min(par, multiprocessing.cpu_count())
	else: available_cores = 1
	logging.info("number of available cores: " + str(available_cores))

	if available_cores > 1:
		pool = multiprocessing.Pool(available_cores)
		concurrent_map = pool.map
	else: concurrent_map = map

	todo_update_hyportage = mode == "update"
	todo_emerge = mode == "emerge"

	##########################################################################
	# 2. SET THE FILE PATHS
	##########################################################################

	dir_portage = os.path.abspath(dir_portage)
	dir_hyportage = os.path.abspath(dir_hyportage)
	dir_install = os.path.abspath(dir_install)

	file_profile_configuration, file_user_configuration, file_keywords, file_installed_packages, file_egencache_packages = portage_files
	path_profile_configuration = os.path.join(dir_portage, file_profile_configuration)
	path_user_configuration = os.path.join(dir_portage, file_user_configuration)
	path_keywords = os.path.join(dir_portage, file_keywords)
	path_installed_packages = os.path.join(dir_portage, file_installed_packages)
	path_egencache_packages = os.path.join(dir_portage, file_egencache_packages)

	path_db_hyportage = os.path.join(dir_hyportage, hyportage_file)

	file_install_script, file_use_flag_configuration = generated_install_files
	path_install_script = os.path.join(dir_install, file_install_script)
	path_use_flag_configuration = os.path.join(dir_install, file_use_flag_configuration)

	##########################################################################
	# 3. COMPUTE WHAT TO DO
	##########################################################################

	if todo_update_hyportage:
		last_db_hyportage_update = os.path.getmtime(path_db_hyportage) if os.path.exists(path_db_hyportage) else 0.0

		todo_list = hyportage_translation.compute_portage_diff(
			concurrent_map,	last_db_hyportage_update, force,
			path_profile_configuration, path_user_configuration,
			path_keywords, path_installed_packages, path_egencache_packages)

		must_apply_profile, must_apply_user, must_regenerate_keywords_ids = todo_list[0], todo_list[1], todo_list[2]
		must_regenerate_installed_packages, spl_name_list, loaded_spls = todo_list[3], todo_list[4], todo_list[5]

	##########################################################################
	# 4. LOAD THE HYPORTAGE DATABASE
	##########################################################################

	utils.phase_start("Loading the stored hyportage data.")
	pattern_repository, id_repository, mspl, spl_groups, core_configuration, installed_spls =\
		load_hyportage(path_db_hyportage, save_modality)
	profile_configuration, user_configuration = load_configurations(path_profile_configuration, path_user_configuration)
	utils.phase_end("Loading completed")

	##########################################################################
	# 5. UPDATE THE HYPORTAGE DATABASE IF NECESSARY
	##########################################################################

	if todo_update_hyportage:
		# update the hyportage spl database
		spl_db_diff = hyportage_translation.update_mspl_and_groups(mspl, spl_groups, spl_name_list, loaded_spls)
		spl_added, spl_updated, spl_removed, spl_groups_added, spl_groups_updated, spl_groups_removed = spl_db_diff
		print("spl_updated = " + str(spl_updated))
		zipped = zip(*spl_updated)
		spl_added_full, spl_removed_full = (list(zipped[0]), list(zipped[1])) if len(zipped) > 0 else (list(), list())
		spl_added_full.extend(spl_added)
		spl_removed_full.extend(spl_removed)

		# update the hyportage pattern repository
		pattern_added, pattern_updated, pattern_removed = hyportage_translation.update_pattern_repository_with_spl_diff(
			pattern_repository, mspl, spl_groups, spl_added_full, spl_removed_full)
		pattern_added_conf, pattern_removed_conf = hyportage_translation.update_pattern_repository_with_configuration_diff(
			pattern_repository, mspl, spl_groups, core_configuration,
			must_apply_profile, must_apply_user, profile_configuration, user_configuration)

		# update arch, keyword id list, and initialize iuses
		arch_changed = hyportage_translation.update_arch(
			core_configuration, mspl, spl_added_full, must_apply_profile, profile_configuration)
		if must_regenerate_keywords_ids: hyportage_translation.update_keywords_ids(id_repository, path_keywords)

		# update the hyportage database with the configurations
		spl_modified_data, spl_modified_visibility = hyportage_translation.apply_configurations(
			pattern_repository, mspl, spl_added_full,
			profile_configuration, user_configuration, must_apply_profile, must_apply_user)

		# finalize iuse list for the packages
		spl_iuse_reset = hyportage_translation.initialize_iuse_flags(
			pattern_repository, spl_modified_data, pattern_added, pattern_updated, pattern_removed)

		# update the id repository
		hyportage_translation.update_id_repository(
			pattern_repository, id_repository, spl_iuse_reset, spl_groups_removed, spl_groups_added)

		# update the smt
		hyportage_translation.update_smt_constraints(
			pattern_repository, id_repository, mspl, spl_groups, arch_changed, simplify_mode,
			pattern_added, pattern_updated, pattern_removed,
			spl_iuse_reset, spl_modified_visibility)

		# save the hypotage database
		save_hyportage(
			path_db_hyportage, pattern_repository, id_repository, mspl, spl_groups, core_configuration,
			installed_spls, save_modality)

	##########################################################################
	# 6. RUN RECONFIGURE IF NECESSARY
	##########################################################################

	if todo_emerge:
		explain_modality = verbose >= 3
		# compute what to install
		requested_patterns, default_patterns, use_selection = reconfigure.compute_request(
			atoms, profile_configuration, user_configuration)
		smt_constraint, requested_spls, all_spls = reconfigure.process_request(
			pattern_repository, id_repository, requested_patterns, default_patterns)

		# extends the pattern repository with user-defined patterns
		reconfigure.extends_pattern_repository_with_request(pattern_repository, requested_patterns)

		# adds the user required iuses to the id_repository
		reconfigure.extends_id_repository_with_requested_use_flags(
			id_repository, installed_spls, requested_spls, use_selection)

		# apply the user-specific use selection to the mspl
		reconfigure.apply_requested_use_selection(requested_spls, use_selection)

		# compute the new configuration
		to_install_spls = reconfigure.get_hyvarrec_input_monolithic(
			pattern_repository, id_repository, mspl, spl_groups, installed_spls,
			all_spls, smt_constraint, par, explain_modality)

		# generate the emerge script and use configuration files
		reconfigure.generate_emerge_script_file(path_install_script, installed_spls, to_install_spls)
		reconfigure.generate_package_use_file(path_use_flag_configuration, to_install_spls)


"""
	# compute the difference from the previous state

	logging.info("Computing what to do.")
	t = time.time()
	last_update = 0.0

	if os.path.exists(path_db_hyportage):
		last_update = os.path.getmtime(path_db_hyportage)

	must_apply_profile = (last_update < os.path.getmtime(path_profile_configuration))
	must_apply_user = (last_update < os.path.getmtime(path_user_configuration))
	must_regenerate_keywords_ids = (last_update < os.path.getmtime(path_keywords))
	must_regenerate_installed_packages = (last_update < os.path.getmtime(path_installed_packages))

	egencache_files = hyportage_from_egencache.get_egencache_files(path_egencache_packages)
	if force:
		patterns = [ hyportage_pattern.pattern_create_from_atom(atom) for atom in force.split() ]
		def filter_function(path_file): return filter_egencache_file_full(path_file, last_update, patterns)
	else:
		def filter_function(path_file): return filter_egencache_file(path_file, last_update)
	egencache_files_to_load = filter(filter_function, egencache_files)
	logging.info("number of egencache files found: " + str(len(egencache_files)))
	logging.info("number of egencache files to load: " + str(len(egencache_files_to_load)))

	logging.info("Computation completed in " + unicode(time.time() - t) + " seconds.")

	##########################################################################
	# 3. UPDATE THE MSPL DATA IF NECESSARY
	##########################################################################

	nb_egencache_files_to_load = len(egencache_files_to_load)
	if nb_egencache_files_to_load > 0:  # load new hyportage spls  from egencache files
		logging.info("Loading the " + str(len(egencache_files_to_load)) + " egencache files.")
		raw_spls = concurrent_map(hyportage_from_egencache.create_spl_from_egencache_file, egencache_files_to_load)
		#raw_spls = map(hyportage_from_egencache.create_spl_from_egencache_file, egencache_files_to_load)
		logging.info("Loading completed in " + unicode(time.time() - t) + " seconds.")
	else: raw_spls = []

	# load the full hyportage data, remove overwritten data and update the pattern_repository

	logging.info("Loading the stored hyportage data.")
	t = time.time()
	pattern_repository, id_repository, mspl, spl_groups, core_configuration, installed_spls =\
		load_hyportage(path_db_hyportage, save_modality)
	logging.info("Loading completed in " + unicode(time.time() - t) + " seconds.")

	logging.info("Updating the core hyportage data (pattern_repository, spl_groups).")
	t = time.time()
	package_to_add = []
	package_to_update = []
	for spl in raw_spls:
		if hyportage_data.spl_get_name(spl) in mspl: package_to_update.append(spl)
		else: package_to_add.append(spl)
	package_name_to_remove = [
		spl_name for spl_name in mspl.keys()
		if spl_name not in set([hyportage_from_egencache.get_package_name_from_path(f)[0] for f in egencache_files])]
	package_update_info = (
		[ (hyportage_data.spl_get_name(spl), spl) for spl in package_to_update ]
		+ [ (el, None) for el in package_name_to_remove ])

	spl_groups_removed = []
	spl_groups_added = []
	# add the added spls
	for new_spl in package_to_add:
		hyportage_data.mspl_add_spl(mspl, new_spl)
		added_group = hyportage_data.spl_groups_add_spl(spl_groups, new_spl)
		if added_group is not None: spl_groups_added.append(added_group)
		hyportage_pattern.pattern_repository_add_spl(pattern_repository, new_spl)
	for new_spl in package_to_add:
		for pattern, required_use in hyportage_data.spl_get_dependencies(new_spl).iteritems():
			hyportage_pattern.pattern_repository_add_pattern(pattern_repository, mspl, spl_groups, pattern, required_use)
	# update or removed the updated spls
	for package_name, new_spl in package_update_info:  # remove the removed spls, and update the updated ones
		old_spl = mspl.pop(package_name)
		# update pattern repository
		if new_spl:
			hyportage_pattern.pattern_repository_update(pattern_repository, old_spl, new_spl)
			hyportage_data.spl_groups_replace_spl(spl_groups, old_spl, new_spl)
		else:
			hyportage_pattern.pattern_repository_remove(pattern_repository, old_spl)
			removed_group = hyportage_data.spl_groups_remove_spl(spl_groups, old_spl)
			if removed_group is not None: spl_groups_removed.append(removed_group)
			# remove entries from id repository: must be entierly re-generated
			hyportage_ids.id_repository_remove_spl(id_repository, old_spl)

	# update the spls required iuse list, for the new spls and the old ones, and regenerate the ids
	spl_updated_iuses = set(raw_spls)
	for spl in raw_spls:
		for pattern, iuses in hyportage_data.spl_get_dependencies(spl).iteritems():
			el = hyportage_pattern.pattern_repository_get(pattern_repository, pattern)  # hmm, did I forget to update the pattern repository at that point?
			spl_updated_iuses.update(hyportage_pattern.pattern_repository_element_get_spls(el))

	logging.info("Update completed in " + unicode(time.time() - t) + " seconds.")

	##########################################################################
	# 4. REGENERATE THE KEYWORD IDS IF NECESSARY
	##########################################################################

	if must_regenerate_keywords_ids:
		logging.info("Regenerating the keyword list")
		t = time.time()
		keywords_list = portage_data.keyword_set_from_save_format(utils.load_data_file(path_keywords, "json"))
		hyportage_ids.id_repository_set_keywords(id_repository, keywords_list)
		logging.info("Regeneration completed in " + unicode(time.time() - t) + " seconds.")

	##########################################################################
	# 5. APPLY THE CONFIGURATION IF NECESSARY
	##########################################################################

	logging.info("Applying the configuration if necessary")
	t = time.time()
	new_spls_loaded = len(raw_spls) > 0
	if new_spls_loaded or must_apply_profile:
		conf_profile = portage_data.configuration_from_save_format(utils.load_data_file(path_profile_configuration, "json"))
	else: conf_profile = None
	if new_spls_loaded or must_apply_user:
		conf_user = portage_data.configuration_from_save_format(utils.load_data_file(path_user_configuration, "json"))
	else: conf_user = None
	if (conf_profile is not None) or (conf_user is not None):
		spl_modified_data, spl_modified_visibility = hyportage_configuration.apply_configurations(
			core_configuration, conf_profile, conf_user, must_apply_profile, must_apply_user,
			raw_spls, mspl, spl_groups, pattern_repository)
	logging.info("Application completed in " + unicode(time.time() - t) + " seconds.")

	##########################################################################
	# 6. REGENERATE THE IDS IF NECESSARY
	##########################################################################

	logging.info("Generating the ids if necessary")
	t = time.time()
	for spl in spl_updated_iuses:
		hyportage_data.spl_reset_required_iuses(spl, pattern_repository)
		hyportage_ids.id_repository_add_spl(id_repository, spl)

	for spl_group in spl_groups_removed:
		hyportage_ids.id_repository_remove_spl_group(id_repository, spl_group)
	for spl_group in spl_groups_added:
		hyportage_ids.id_repository_add_spl_group(id_repository, spl_group)
	logging.info("Generation completed in " + unicode(time.time() - t) + " seconds.")

	##########################################################################
	# 7. GENERATE THE SMT CONSTRAINTS
	##########################################################################
	
	logging.info("Generating the SMT Constraints")
	t = time.time()
	# generate everything for now: laziness for the win
	spl_smts = map(
		lambda spl: smt_encoding.convert_spl(pattern_repository, id_repository, spl, simplify_mode), mspl.values())
	spl_group_smts = map(
		lambda spl_group: smt_encoding.convert_spl_group(id_repository, spl_group, simplify_mode), spl_groups.values())

	for spl_name, smt in spl_smts: hyportage_data.spl_set_smt_constraint(mspl[spl_name], smt)
	for spl_group_name, smt in spl_group_smts: hyportage_data.spl_group_set_smt_constraint(spl_groups[spl_group_name], smt)
	logging.info("Generation completed in " + unicode(time.time() - t) + " seconds.")

	##########################################################################
	# 7. REGENERATE THE INSTALLED PACKAGE INFORMATION IF NECESSARY
	##########################################################################

	if must_regenerate_installed_packages:
		installed_spls = core_data.package_installed_from_save_format(utils.load_data_file(path_installed_packages, "json"))

	##########################################################################
	# 8. WRITE THE FILES
	##########################################################################

	logging.info("Saving the hyportage data")
	t = time.time()
	save_hyportage(
		path_db_hyportage, pattern_repository, id_repository, mspl, spl_groups,
		core_configuration, installed_spls, save_modality)
	logging.info("Saving completed in " + unicode(time.time() - t) + " seconds.")"""


##

if __name__ == "__main__":
	main()

