import os
import logging

import core_data

import utils

import utils_egencache
import hyportage_data
import hyportage_pattern
import hyportage_ids
import smt_encoding

"""
This file contains all the function for translating the portage data to our hyportage representation.
"""


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
		if core_data.match_package_path(pattern, path_file):
			return True
	return False


def compute_to_load(last_update, force, path_egencache_packages):
	"""
	This function collects the names of the packages in the portage repository, and lists the ones that need to be loaded
	:param last_update: the date of the last update of the hyportage repository
	:param force: the list of patterns to force to load
	:param path_egencache_packages: the path to the portage repository
	:return: a pair consisting of the list of files to load, plus the set of packages in the portage repository
		(so we know which spl must be removed from hyportage)
	"""
	utils.phase_start("Computing what to do.")
	egencache_files = utils_egencache.get_egencache_files(path_egencache_packages)
	if force:
		patterns = [ hyportage_pattern.pattern_create_from_atom(atom) for atom in force.split() ]
		def filter_function(path_file): return filter_egencache_file_full(path_file, last_update, patterns)
	else:
		def filter_function(path_file): return filter_egencache_file(path_file, last_update)
	egencache_files_to_load = filter(filter_function, egencache_files)
	logging.info("number of egencache files found: " + str(len(egencache_files)))
	logging.info("number of egencache files to load: " + str(len(egencache_files_to_load)))

	utils.phase_end("Computation completed")
	return egencache_files_to_load, {utils_egencache.get_package_name_from_path(f)[0] for f in egencache_files}


def load_spl_to_load(concurrent_map, egencache_files_to_load):
	"""
	This function loads the spl in the list in parameter
	:param concurrent_map: the map used to parallel the load
	:param egencache_files_to_load: the list of files to load
	:return: the list of loaded spls
	"""
	nb_egencache_files_to_load = len(egencache_files_to_load)
	if nb_egencache_files_to_load > 0:  # load new hyportage spls  from egencache files
		utils.phase_start("Loading the " + str(nb_egencache_files_to_load) + " egencache files.")
		loaded_spls = concurrent_map(utils_egencache.create_spl_from_egencache_file, egencache_files_to_load)
		utils.phase_end("Loading completed")
	else: loaded_spls = []
	return loaded_spls


##########################################################################
# 2. UPDATE CORE DATA: MSPL AND SPL_GROUPS
##########################################################################


def update_mspl_and_groups(mspl, spl_groups, spl_name_set, loaded_spls):
	"""
	This function updates the mspl and the spl_groups structures with the newly loaded spls,
	while removing the spl that are not in the portage repository anymore
	:param mspl: the hyportage mspl
	:param spl_groups: the hyportage spl_groups
	:param spl_name_set: the full set of spl names in the portage repository
	:param loaded_spls: the newly loaded spls
	:return: a tuple describing what changed (added spls, removed spls, added spl_groups, updated spl_groups and removed spl_groups)
	Additionally, the mspl and spl_groups in parameter have been updated
	"""
	utils.phase_start("Updating the core hyportage data (mspl, spl_groups).")
	spl_to_add, spl_to_update = [], []
	for spl in loaded_spls:
		if spl.name in mspl: spl_to_update.append((mspl[spl.name], spl))
		else: spl_to_add.append(spl)
	spl_to_remove = [mspl[spl_name] for spl_name in mspl.keys() if spl_name not in spl_name_set]

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
		spl_groups_updated.add(new_spl.group_name)

	# remove the removed spls
	for old_spl in spl_to_remove:
		hyportage_data.mspl_remove_spl(mspl, old_spl)
		removed_group = hyportage_data.spl_groups_remove_spl(spl_groups, old_spl)
		if removed_group is not None: spl_groups_removed.add(removed_group)
	utils.phase_end("Updating completed")
	spl_added_full = loaded_spls
	spl_removed_full = spl_to_remove
	spl_removed_full.extend([el[0] for el in spl_to_update])
	return spl_added_full, spl_removed_full, spl_groups_added, spl_groups_updated, spl_groups_removed


##########################################################################
# 3. UPDATE THE PATTERN REPOSITORY
##########################################################################


def __update_pattern_repository_spl_dependencies(pattern_repository, spl_added, spl_removed):
	pattern_added = set()
	pattern_updated = set()
	pattern_removed = set()

	for new_spl in spl_added:
		pattern_added_list, pattern_updated_list = pattern_repository.add_spl_dependencies(new_spl)
		pattern_added.update(pattern_added_list)
		pattern_updated.update(pattern_updated_list)
	for old_spl in spl_removed:
		pattern_removed_list, pattern_updated_list = pattern_repository.remove_spl_dependencies(old_spl)
		pattern_removed.update(pattern_removed_list)
		pattern_updated.update(pattern_updated_list)

	return pattern_added, pattern_updated, pattern_removed


def __update_pattern_repository_reset_pel(pattern_repository, spl_added, spl_removed):
	pattern_updated = set()
	for spl_group_name in {spl.group_name for spl in spl_added}:
		pattern_updated.update(pattern_repository.reset_cache(spl_group_name))
	for spl_group_name in {spl.group_name for spl in spl_removed}:  # no data changed in the spls
		pattern_repository.reset_cache(spl_group_name)
	return pattern_updated


def update_pattern_repository(pattern_repository, spl_added, spl_removed):
	utils.phase_start("Updating the pattern hyportage data (pattern_repository).")
	pattern_added, pattern_updated, pattern_removed = \
		__update_pattern_repository_spl_dependencies(pattern_repository, spl_added, spl_removed)
	pattern_updated.update(__update_pattern_repository_reset_pel(pattern_repository, spl_added, spl_removed))
	utils.phase_end("Updating completed")
	return pattern_added, pattern_updated, pattern_removed


##


def update_revert_dependencies(pattern_repository, pattern_added, pattern_updated, pattern_removed):
	utils.phase_start("Updating the set of externally required features.")

	updated_spl_list = []
	for pattern in pattern_added | pattern_updated:
		pel = pattern_repository[pattern]
		required_uses = pel.required_uses
		for spl in pel.matched_spls:
			if spl.update_revert_dependencies(pattern, required_uses):
				updated_spl_list.append(spl)

	for pattern in pattern_removed:
		pel = pattern_repository[pattern]
		for spl in pel.matched_spls:
			spl.reset_revert_dependencies(pattern)
			updated_spl_list.append(spl)

	utils.phase_end("Updating completed")
	return updated_spl_list


##########################################################################
# 4. UPDATE THE IMPLICIT IUSES
##########################################################################


def reset_implicit_features(mspl, is_eapi4_updated, is_eapi5_updated):
	utils.phase_start("Adding the implicit Features to the spls.")
	if is_eapi4_updated or is_eapi5_updated:
		for spl in mspl.itervalues():
			if (spl.eapi < 5) and is_eapi4_updated: spl.reset_iuses_full()
			elif (spl.eapi > 4) and is_eapi5_updated: spl.reset_iuses_full()
	utils.phase_end("Addition completed")


##########################################################################
# 5. UPDATE THE ID REPOSITORY
##########################################################################


def update_id_repository(id_repository, updated_spl_list, spl_removed, spl_groups_removed, spl_groups_added):
	utils.phase_start("Updating the Id Repository")
	for spl in spl_removed: id_repository.remove_spl(spl)
	for spl in updated_spl_list: id_repository.add_spl(spl)

	for spl_group in spl_groups_removed: id_repository.remove_spl_group(spl_group)
	for spl_group in spl_groups_added: id_repository.add_spl_group(spl_group)
	utils.phase_end("Generation completed")


##########################################################################
# 6. UPDATE THE SPL VISIBILITY
##########################################################################


def update_masks(mspl, spl_added_full, config):
	utils.phase_start("Updating the SPL Masks")
	if config.new_masks:
		res = []
		for k, spl in mspl.iteritems():
			unmasked = config.get_unmasked(spl.core)
			if unmasked != spl.unmasked:
				res.append(spl)
				spl.unmasked = unmasked
	else:
		for spl in spl_added_full:
			spl.unmasked = config.get_unmasked(spl.core)
		res = spl_added_full
	utils.phase_end("Generation completed")
	return res

##


def update_keywords(mspl, spl_updated_mask, config):
	utils.phase_start("Updating the SPL Keywords")
	if config.new_keywords_config: iterator = mspl.itervalues()
	else: iterator = iter(spl_updated_mask)

	res = []
	for spl in iterator:
		keyword_mask, installable, is_stable = config.get_stability_status(spl.core, spl.unmasked, spl.keywords_list)
		if (keyword_mask, is_stable) != (spl.keyword_mask, spl.is_stable):
			res.append(spl)
			spl.keyword_mask, spl.installable, spl.is_stable = keyword_mask, installable, is_stable
	utils.phase_end("Generation completed")
	return res

##



def reset_use_flag_config(mspl, config):
	utils.phase_start("Updating the Id Repository")
	if config.new_keywords_config and config.new_use_flag_config:
		for spl_name, spl in mspl.iteritems():
			spl.use_selection_full = None
	utils.phase_end("Generation completed")

##





def update_smt_constraints(
		pattern_repository, id_repository, mspl, spl_groups, simplify_mode,
		pattern_added, pattern_updated, pattern_removed,
		spl_iuse_reset, spl_modified_visibility):
	utils.phase_start("Updating the core SMT Constraints")
	spls_to_update = set(spl_iuse_reset)
	pattern_visibility = set([
		pattern
		for spl_group_name in {spl.group_name for spl in spl_modified_visibility}
		for pattern in hyportage_pattern.pattern_repository_get_pattern_from_spl_group_name(pattern_repository, spl_group_name)])
	spls_to_update.update([
		spl
		for pattern in pattern_added | pattern_updated | pattern_removed | pattern_visibility
		for spl in hyportage_pattern.pattern_repository_element_get_spls(
			hyportage_pattern.pattern_repository_get(pattern_repository, pattern), mspl, spl_groups)])
	spl_groups_to_update = [
		spl_groups[spl_group_name]
		for spl_group_name in {spl.group_name for spl in spls_to_update}]

	spl_smts = map(
		lambda spl: smt_encoding.convert_spl(
			pattern_repository, id_repository, mspl, spl_groups, spl, simplify_mode), spls_to_update)
	spl_group_smts = map(
		lambda spl_group: smt_encoding.convert_spl_group(id_repository, spl_group, simplify_mode), spl_groups_to_update)

	for spl_name, smt in spl_smts: hyportage_data.spl_set_smt_constraint(mspl[spl_name], smt)
	for spl_group_name, smt in spl_group_smts: hyportage_data.spl_group_set_smt_constraint(spl_groups[spl_group_name], smt)
	utils.phase_end("Updating completed")






