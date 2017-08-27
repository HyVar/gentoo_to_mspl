import os
import utils
import logging

import portage_data
import hyportage_from_egencache
import hyportage_data
import hyportage_pattern
import hyportage_ids
import hyportage_configuration
import smt_encoding


__author__ = "Michael Lienhardt & Jacopo Mauro"
__copyright__ = "Copyright 2017, Michael Lienhardt & Jacopo Mauro"
__license__ = "ISC"
__version__ = "0.5"
__maintainer__ = "Michael Lienhardt & Jacopo Mauro"
__email__ = "michael.lienhardt@laposte.net & mauro.jacopo@gmail.com"
__status__ = "Prototype"


##########################################################################
# 1. COMPUTE WHAT TO DO
##########################################################################

def filter_egencache_file(path_file, last_update):
	return last_update < os.path.getmtime(path_file)


def filter_egencache_file_full(path_file, last_update, patterns):
	if last_update < os.path.getmtime(path_file):
		return True
	for pattern in patterns:
		if hyportage_pattern.match_package_path(pattern, path_file):
			return True
	return False


def compute_portage_diff(
		concurrent_map, last_update, force,
		path_profile_configuration, path_user_configuration,
		path_keywords, path_installed_packages, path_egencache_packages):
	utils.phase_start("Computing what to do.")

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

	utils.phase_end("Computation completed")

	nb_egencache_files_to_load = len(egencache_files_to_load)
	if nb_egencache_files_to_load > 0:  # load new hyportage spls  from egencache files
		utils.phase_start("Loading the " + str(nb_egencache_files_to_load) + " egencache files.")
		loaded_spls = concurrent_map(hyportage_from_egencache.create_spl_from_egencache_file, egencache_files_to_load)
		#raw_spls = map(hyportage_from_egencache.create_spl_from_egencache_file, egencache_files_to_load)
		utils.phase_end("Loading completed")
	else: loaded_spls = []

	spl_name_list = [hyportage_from_egencache.get_package_name_from_path(f)[0] for f in egencache_files]

	return (
		must_apply_profile, must_apply_user,
		must_regenerate_keywords_ids, must_regenerate_installed_packages, spl_name_list, loaded_spls)


def update_mspl_and_groups(mspl, spl_groups, spl_name_list, loaded_spls):
	utils.phase_start("Updating the core hyportage data (mspl, spl_groups).")
	spl_to_add, spl_to_update = [], []
	for spl in loaded_spls:
		if hyportage_data.spl_get_name(spl) in mspl: spl_to_update.append((mspl[hyportage_data.spl_get_name(spl)], spl))
		else: spl_to_add.append(spl)
	spl_to_remove = [mspl[spl_name] for spl_name  in  mspl.keys() if spl_name not in set(spl_name_list)]

	spl_groups_added = set()
	spl_groups_updated = set()
	spl_groups_removed = set()

	# add the added spls
	for new_spl in spl_to_add:
		hyportage_data.mspl_add_spl(mspl, new_spl)
		added_group = hyportage_data.spl_groups_add_spl(spl_groups, new_spl)
		if added_group is not None: spl_groups_added.add(added_group)

	# update the updated spls
	for old_spl, new_spl in spl_to_update:
		hyportage_data.mspl_update_spl(mspl, old_spl, new_spl)
		spl_groups_updated.add(hyportage_data.spl_get_group_name(new_spl))

	# remove the removed spls
	for old_spl in spl_to_remove:
		hyportage_data.mspl_remove_spl(mspl, old_spl)
		removed_group = hyportage_data.spl_groups_remove_spl(spl_groups, old_spl)
		if removed_group is not None: spl_groups_removed.add(removed_group)
	utils.phase_end("Updating completed")
	return spl_to_add, spl_to_update, spl_to_remove, spl_groups_added, spl_groups_updated, spl_groups_removed


def update_pattern_repository_with_spl_diff(pattern_repository, mspl, spl_groups, spl_added_full, spl_removed_full):
	pattern_added = set()
	pattern_updated = set()
	pattern_removed = set()
	utils.phase_start("Updating the pattern hyportage data (pattern_repository -- 1/2).")

	for new_spl in spl_added_full:
		pattern_added.update(hyportage_pattern.pattern_repository_add_pattern_from_spl(
			pattern_repository, mspl, spl_groups, new_spl))
	for old_spl in spl_removed_full:
		pattern_removed.update(hyportage_pattern.pattern_repository_remove_pattern_from_spl(
			pattern_repository, old_spl))

	for new_spl in spl_added_full:
		pattern_updated.update(hyportage_pattern.pattern_repository_add_spl(pattern_repository, new_spl))
	for old_spl in spl_removed_full:
		pattern_updated.update(hyportage_pattern.pattern_repository_remove_spl(pattern_repository, old_spl))
	pattern_updated.difference_update(pattern_added)

	utils.phase_end("Updating completed")
	return pattern_added, pattern_updated, pattern_removed


def update_pattern_repository_with_configuration_diff(
		pattern_repository, mspl, spl_groups, core_configuration,
		must_apply_profile, must_apply_user, profile_configuration, user_configuration):
	pattern_added = set()
	pattern_removed = set()
	utils.phase_start("Updating the pattern hyportage data (pattern_repository -- 2/2).")

	if must_apply_profile:
		core_conf_patterns = hyportage_configuration.core_configuration_get_profile_patterns(core_configuration)
		pattern_diff = hyportage_configuration.configuration_update_pattern(
			pattern_repository, mspl, spl_groups, core_conf_patterns, profile_configuration,
			hyportage_pattern.pattern_repository_element_set_in_profile_configuration)
		pattern_added.update(pattern_diff[0])
		pattern_removed.update(pattern_diff[1])
	if must_apply_user:
		core_conf_patterns = hyportage_configuration.core_configuration_get_user_patterns(core_configuration)
		pattern_diff = hyportage_configuration.configuration_update_pattern(
			pattern_repository, mspl, spl_groups, core_conf_patterns, user_configuration,
			hyportage_pattern.pattern_repository_element_set_in_user_configuration)
		pattern_added.update(pattern_diff[0])
		pattern_removed.update(pattern_diff[1])

	utils.phase_end("Updating completed")
	return pattern_added, pattern_removed


def update_arch(core_configuration, mspl, spl_added_full, must_apply_profile, profile_configuration):
	utils.phase_start("Updating the arch.")
	arch_changed = False
	if must_apply_profile:
		arch = portage_data.configuration_get_arch(profile_configuration)
		if arch != hyportage_configuration.core_configuration_get_arch(core_configuration):
			arch_changed = True
			hyportage_configuration.core_configuration_set_arch(core_configuration, arch)
			for spl in mspl.values():
				hyportage_configuration.keywords_initialize(spl, arch)
	else:
		arch = hyportage_configuration.core_configuration_get_arch(core_configuration)
		for spl in spl_added_full:
			hyportage_configuration.keywords_initialize(spl, arch)
	utils.phase_end("Updating completed")
	return arch_changed


def update_keywords_ids(id_repository, path_keywords):
	utils.phase_start("Regenerating the keyword list")
	keywords_list = portage_data.keyword_set_from_save_format(utils.load_data_file(path_keywords, "json"))
	hyportage_ids.id_repository_set_keywords(id_repository, keywords_list)
	utils.phase_end("Regeneration completed")


def initialize_iuse_flags(pattern_repository, spl_added_full, pattern_added, pattern_updated, pattern_removed):
	utils.phase_start("Resetting the spls' use flag list.")
	spl_iuse_to_update = set(spl_added_full)
	spl_iuse_to_update.update([
		spl
		for pattern in pattern_added | pattern_updated | pattern_removed
		for spl in hyportage_pattern.pattern_repository_element_get_spls(
			hyportage_pattern.pattern_repository_get(pattern_repository, pattern))])
	for spl in spl_iuse_to_update:
		hyportage_data.spl_reset_required_iuses(spl, pattern_repository)

	utils.phase_end("Resetting completed")
	return spl_iuse_to_update


def apply_configurations(
		pattern_repository, mspl, spl_iuse_reset,
		profile_configuration, user_configuration, must_apply_profile, must_apply_user):
	utils.phase_start("Applying the configuration on the hyportage database.")
	spl_modified_data, spl_modified_visibility = hyportage_configuration.apply_configurations(
			pattern_repository, mspl, spl_iuse_reset,
			profile_configuration, user_configuration, must_apply_profile, must_apply_user)

	utils.phase_end("Application completed")
	return spl_modified_data, spl_modified_visibility


def update_id_repository(pattern_repository, id_repository, spl_iuse_reset, spl_groups_removed, spl_groups_added):
	utils.phase_start("Generating the ids if necessary")
	for spl in spl_iuse_reset:
		hyportage_data.spl_reset_required_iuses(spl, pattern_repository)
		hyportage_ids.id_repository_add_spl(id_repository, spl)

	for spl_group in spl_groups_removed:
		hyportage_ids.id_repository_remove_spl_group(id_repository, spl_group)
	for spl_group in spl_groups_added:
		hyportage_ids.id_repository_add_spl_group(id_repository, spl_group)
	utils.phase_end("Generation completed")


def update_smt_constraints(
		pattern_repository, id_repository, mspl, spl_groups, arch_changed, simplify_mode,
		pattern_added, pattern_updated, pattern_removed,
		spl_iuse_reset, spl_modified_visibility):
	utils.phase_start("Updating the SMT Constraints")

	if arch_changed:
		spls_to_update = mspl.values()
		spl_groups_to_update = spl_groups.values()
	else:
		spls_to_update = set(spl_iuse_reset)
		pattern_visibility = set([
			pattern
			for spl_group_name in set([hyportage_data.spl_get_group_name(spl) for spl in spl_modified_visibility])
			for pattern in hyportage_pattern.pattern_repository_get_pattern_from_spl_group_name(spl_group_name)])
		spls_to_update.update([
			spl
			for pattern in pattern_added | pattern_updated | pattern_removed | pattern_visibility
			for spl in hyportage_pattern.pattern_repository_element_get_spls(
				hyportage_pattern.pattern_repository_get(pattern_repository, pattern))])
		spl_groups_to_update = [
			spl_groups[spl_group_name]
			for spl_group_name in set([hyportage_data.spl_get_group_name(spl) for spl in spls_to_update])]

	spl_smts = map(
		lambda spl: smt_encoding.convert_spl(pattern_repository, id_repository, spl, simplify_mode), spls_to_update)
	spl_group_smts = map(
		lambda spl_group: smt_encoding.convert_spl_group(id_repository, spl_group, simplify_mode), spl_groups_to_update)

	for spl_name, smt in spl_smts: hyportage_data.spl_set_smt_constraint(mspl[spl_name], smt)
	for spl_group_name, smt in spl_group_smts: hyportage_data.spl_group_set_smt_constraint(spl_groups[spl_group_name], smt)
	utils.phase_end("Updating completed")


