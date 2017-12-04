#!/usr/bin/python


import os
import logging

import core_data

import utils

import utils_egencache
import hyportage_data
import hyportage_pattern


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
		atom_list = force.split()
		patterns = [hyportage_pattern.pattern_create_from_atom(atom) for atom in atom_list]
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
	spl_to_remove = [spl for spl_name, spl in mspl.iteritems() if spl_name not in spl_name_set]

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
	added_spl_group_names = {spl.group_name for spl in spl_added}
	for spl_group_name in added_spl_group_names:
		pattern_updated.update(pattern_repository.reset_cache(spl_group_name))
	removed_spl_group_names = {spl.group_name for spl in spl_removed}
	for spl_group_name in removed_spl_group_names:  # no data changed in the spls
		pattern_repository.reset_cache(spl_group_name)
	return pattern_updated


def update_pattern_repository(pattern_repository, spl_added, spl_removed):
	"""
	This function updates the pattern repository in input with the newly added spls and the ones removed. In particular,
	this function updates the set of patterns in the repository to only contains those referenced in the mspl,
	and reset the cache of the patterns that are modified by the addition and removal of the spls in parameter
	:param pattern_repository: the pattern repository to update
	:param spl_added: the spls that are added to the mspl
	:param spl_removed: the spls that are removed from the mspl
	:return: the set of patterns that are added, updated and removed during the update
	"""
	utils.phase_start("Updating the pattern hyportage data (pattern_repository).")
	pattern_added, pattern_updated_containing, pattern_removed = \
		__update_pattern_repository_spl_dependencies(pattern_repository, spl_added, spl_removed)
	pattern_updated_content = __update_pattern_repository_reset_pel(pattern_repository, spl_added, spl_removed)
	utils.phase_end("Updating completed")
	return pattern_added, pattern_updated_containing, pattern_updated_content, pattern_removed


##


def update_revert_dependencies(pattern_repository, pattern_added_updated, pattern_removed):
	"""
	This function resets the cached data in the spls related to the core use flags declared in the pattern.
	Indeed, because the pattern repository changed, the set of core use flags of an spl may change as well.
	:param pattern_repository: the hyportage pattern repository
	:param pattern_added: the patterns that were added to the repository
	:param pattern_updated: the patterns that were changed in the repository
	:param pattern_removed: the patterns that were removed from the repository
	:return: the set of spls whose cache has been reset
	"""
	utils.phase_start("Updating the set of externally required features.")
	updated_spl_list = []
	for pattern in pattern_added_updated:
		pel = pattern_repository[pattern]
		required_uses = pel.required_uses
		for spl in pel.matched_spls:
			if spl.update_revert_dependencies(pattern, required_uses):
				updated_spl_list.append(spl)

	for pattern in pattern_removed:
		pel = pattern_repository[pattern]
		for spl in pel.matched_spls:
			spl.reset_revert_dependencies(pattern)

	utils.phase_end("Updating completed")
	return updated_spl_list


##########################################################################
# 4. UPDATE THE IMPLICIT IUSES
##########################################################################


def reset_implicit_features(mspl, is_eapi4_updated, is_eapi5_updated):
	"""
	This function resets the cached data of the spls if the implicit use flags changed
	:param mspl: the hyportage mspl
	:param is_eapi4_updated: if the implicit use fags for eapi4 or less changed
	:param is_eapi5_updated: if the implicit use fags for eapi5 or more changed
	:return: the list of updated spls
	"""
	utils.phase_start("Adding the implicit Features to the spls.")
	updated_spl_list = []
	if is_eapi4_updated or is_eapi5_updated:
		for spl in mspl.itervalues():
			if (spl.eapi < 5) and is_eapi4_updated:
				spl.reset_iuses_full()
				updated_spl_list.append(spl)
			elif (spl.eapi > 4) and is_eapi5_updated:
				spl.reset_iuses_full()
				updated_spl_list.append(spl)
	utils.phase_end("Addition completed")
	return updated_spl_list


##########################################################################
# 5. UPDATE THE ID REPOSITORY
##########################################################################


def update_id_repository(id_repository, changed_ids_spl_set, spl_removed):
	utils.phase_start("Updating the Id Repository")
	for spl in spl_removed: id_repository.remove_spl(spl)
	for spl in changed_ids_spl_set: id_repository.add_spl(spl)
	utils.phase_end("Generation completed")


##########################################################################
# 6. UPDATE THE SPL VISIBILITY
##########################################################################


def update_visibility(mspl, spl_added, new_masks, new_keywords, new_licenses):
	utils.phase_start("Updating the SPL Visibility")
	if new_masks:
		for spl in mspl.itervalues():
			spl.reset_unmasked()
			spl.generate_visibility_data()
	elif new_keywords or new_licenses:
		for spl in mspl.itervalues():
			spl.reset_unmasked_other()
			spl.generate_visibility_data()
	else:
		for spl in spl_added:
			spl.generate_visibility_data()
	utils.phase_end("Generation completed")


##########################################################################
# 7. UPDATE THE SPL USE FLAG SELECTION
##########################################################################


def update_use_flag_selection(mspl, spl_added, new_keywords, new_use_flag_config):
	utils.phase_start("Updating the SPL use flag Selection")
	if new_keywords or new_use_flag_config:
		for spl in mspl.itervalues():
			spl.reset_use_selection()
			_ = spl.use_selection_core
	else:
		for spl in spl_added:
			_ = spl.use_selection_core
	utils.phase_end("Generation completed")


##########################################################################
# 7. UPDATE THE SPL USE FLAG SELECTION
##########################################################################


def update_smt_constraints(
		pattern_repository, mspl, spl_groups,
		pattern_added_updated_content,
		spl_added_list, implicit_use_flag_changed):
	utils.phase_start("Updating the core SMT Constraints")
	# the spls for which we need to recompute the constraint are:
	#  - all spls if the use flag changed
	#      (it is a good enough approximation, and computing the actual set would be far to costly)
	#  - otherwise the added spls and the ones with a reference to the modified patterns
	# additionally, we need to update the SMT of the spl_group of these spls
	#
	# Note about the computation of the set of spl in case of use flag modification:
	#  - we need to update the constraint of all these spls
	#  - plus the ones that depend on these spls (because e.g. some use flags might not exist anymore)
	# too costly
	if implicit_use_flag_changed or (len(pattern_repository)/2 < len(pattern_added_updated_content)):
		iterator_spl = mspl.itervalues()
		iterator_spl_group = spl_groups.itervalues()
	else:
		spl_set = set(spl_added_list)
		for pattern in pattern_added_updated_content:
			spl_set.update(pattern_repository[pattern].containing_spl.keys())
		spl_group_set = {spl_groups[spl.group_name] for spl in spl_set}
		iterator_spl = iter(spl_set)
		iterator_spl_group = iter(spl_group_set)

	for spl in iterator_spl:
		spl.reset_smt()
		_ = spl.smt

	for spl_group in iterator_spl_group:
		spl_group.reset_smt()
		_ = spl_group.smt

	utils.phase_end("Updating completed")






