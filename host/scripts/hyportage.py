
import os
import utils
import logging
import multiprocessing
import click


import hyportage_translation
import reconfigure

import hyportage_data
import hyportage_pattern
import hyportage_ids


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
		#core_configuration = hyportage_configuration.core_configuration_create()
		#installed_spls = core_data.package_installed_create()
		#return pattern_repository, id_repository, mspl, spl_groups, core_configuration, installed_spls
		return pattern_repository, id_repository, mspl, spl_groups


def load_configuration(path_configuration):
	return utils.load_data_file(path_configuration, "pickle")


def save_hyportage(path_hyportage, pattern_repository, id_repository, mspl, spl_groups, save_modality):
	if save_modality.endswith("json"):
		logging.error("Cannot save data with json")
	else:
		data = pattern_repository, id_repository, mspl, spl_groups
		utils.store_data_file(path_hyportage, data, save_modality)


def save_configuration(path_configuration, config):
	config.mspl_config.new_masks = False
	config.mspl_config.new_use_declaration_eapi4 = False
	config.mspl_config.new_use_declaration_eapi5 = False
	config.mspl_config.new_keywords_config = False
	config.mspl_config.new_use_flag_config = False
	utils.store_data_file(path_configuration, config, "pickle")


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
	default=("config.pickle", "packages"),
	help='the configuration file in which are stored the portage configuration data, plus the folder in which the egencache portage files can be found')
@click.option(
	'--hyportage_file', '-o',
	default="hyportage.pickle",
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
	type=click.Choice(["json", "gzjson", "marshal", "pickle"]), default="pickle",
	help='Saving modality. Marshal is supposed to be faster but python version specific.')
@click.option(
	'--mode',
	type=click.Choice(["update", "emerge"]), default="update",
	help='Temporary option that states if the tool is used in translate mode or reconfigure mode.')
@click.option(
	'--explain-modality',
	is_flag=True,
	help='Execution modality that tried to explain why a request can not be satisfied.')
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
		explain_modality,
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

	if (available_cores > 1) and (os.name != 'nt'):
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

	file_configuration, file_egencache_packages = portage_files
	path_configuration = os.path.join(dir_portage, file_configuration)
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

		spl_name_list, loaded_spls = hyportage_translation.compute_portage_diff(
			concurrent_map,	last_db_hyportage_update, force, path_egencache_packages)


	##########################################################################
	# 4. LOAD THE HYPORTAGE DATABASE
	##########################################################################

	utils.phase_start("Loading the stored hyportage data.")
	pattern_repository, id_repository, mspl, spl_groups = load_hyportage(path_db_hyportage, save_modality)
	config = load_configuration(path_configuration)
	utils.phase_end("Loading completed")

	##########################################################################
	# 5. UPDATE THE HYPORTAGE DATABASE IF NECESSARY
	##########################################################################

	if todo_update_hyportage:
		logging.info("updating hyportage...")
		unchanged_spls = set(mspl.values())

		# update the hyportage spl database
		spl_db_diff = hyportage_translation.update_mspl_and_groups(mspl, spl_groups, spl_name_list, loaded_spls)
		spl_added_full, spl_removed_full, spl_groups_added, spl_groups_updated, spl_groups_removed = spl_db_diff


		unchanged_spls.difference_update(spl_removed_full)

		# update the feature list with the implicit declarations
		spl_updated_features = hyportage_translation.add_implicit_features(
			unchanged_spls, spl_added_full,
			config.mspl_config.new_use_declaration_eapi4, config.mspl_config.new_use_declaration_eapi5,
			config.mspl_config.use_declaration_eapi4, config.mspl_config.use_declaration_eapi5)

		# update the hyportage pattern repository
		pattern_added, pattern_updated, pattern_removed = hyportage_translation.update_pattern_repository_with_spl_diff(
			pattern_repository, spl_added_full, spl_removed_full)

		# update the required feature list
		spl_updated_required_features = hyportage_translation.update_required_feature_external(
			pattern_repository, pattern_added, pattern_updated, pattern_removed, unchanged_spls, spl_added_full)

		# update the id repository
		spl_updated_features.update(spl_updated_required_features)
		hyportage_translation.update_id_repository(
			id_repository, spl_updated_features, spl_removed_full, spl_groups_removed, spl_groups_added)

		# update the mask and keywords information
		spl_updated_mask = hyportage_translation.update_masks(mspl, spl_added_full, config.mspl_config)
		spl_updated_visibility = hyportage_translation.update_keywords(mspl, spl_updated_mask, config.mspl_config)

		# check if the main config of the spl must be regenerated
		hyportage_translation.reset_use_flag_config(mspl, config.mspl_config)

		# update the smt
		hyportage_translation.update_smt_constraints(
			pattern_repository, id_repository, mspl, spl_groups, simplify_mode,
			pattern_added, pattern_updated, pattern_removed,
			spl_updated_required_features, spl_updated_visibility)

		print("finished")

		# save the hypotage database
		save_hyportage(path_db_hyportage, pattern_repository, id_repository, mspl, spl_groups, save_modality)
		save_configuration(path_configuration, config)


		print("saved")

		return None

		#unchanged_spls.difference_update(spl_updated_required_features)






		# update the keywords and default feature selection


		#pattern_added_conf, pattern_removed_conf = hyportage_translation.update_pattern_repository_with_configuration_diff(
		#	pattern_repository, mspl, spl_groups, core_configuration,
		#	must_apply_profile, must_apply_user, profile_configuration, user_configuration)

		# update arch, keyword id list, and initialize iuses
		#arch_changed = hyportage_translation.update_arch(
		#	core_configuration, mspl, spl_added_full, must_apply_profile, profile_configuration)
		#if must_regenerate_keywords_ids: hyportage_translation.update_keywords_ids(id_repository, path_keywords)

		# update the hyportage database with the configurations
		#spl_modified_data, spl_modified_visibility = hyportage_translation.apply_configurations(
		#	pattern_repository, mspl, spl_added_full,
		#	profile_configuration, user_configuration, must_apply_profile, must_apply_user)

		# finalize iuse list for the packages
		#spl_iuse_reset = hyportage_translation.initialize_iuse_flags(
		#	pattern_repository, mspl, spl_groups, spl_modified_data, pattern_added, pattern_updated, pattern_removed)




		# save the hypotage database
		#save_hyportage(
		#	path_db_hyportage, pattern_repository, id_repository, mspl, spl_groups, core_configuration,
		#	installed_spls, save_modality)

		#return

	##########################################################################
	# 6. RUN RECONFIGURE IF NECESSARY
	##########################################################################

	if todo_emerge:
		logging.info("computing a new system configuration...")
		# compute what to install
		#requested_patterns, default_patterns, use_selection = reconfigure.compute_request(atoms, config)
		root_spls, request_constraint = reconfigure.process_request(
			pattern_repository, id_repository, mspl, spl_groups, config, atoms)

		# get the transitive closure of the spls
		all_spls = reconfigure.get_dependency_transitive_closure(pattern_repository, mspl, spl_groups, root_spls)

		# solve these spl, with the request constraint
		solution = reconfigure.solve_spls(
			id_repository, config, mspl, spl_groups, config.installed_packages,
			all_spls, request_constraint)

		# write the installation files
		reconfigure.generate_emerge_script_file(mspl, path_install_script, config.installed_packages, solution)
		reconfigure.generate_package_use_file(mspl, path_use_flag_configuration, solution)

		# extends the pattern repository with user-defined patterns
		reconfigure.extends_pattern_repository_with_request(pattern_repository, mspl, spl_groups, requested_patterns)

		# translate the request into corresponding smt constraint and corresponding spls
		smt_constraint, requested_spls, all_spls = reconfigure.process_request(
			pattern_repository, id_repository, mspl, spl_groups, requested_patterns, default_patterns)

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

##

if __name__ == "__main__":
	if os.name == 'nt':
		multiprocessing.freeze_support()
	main()
	print("14")

