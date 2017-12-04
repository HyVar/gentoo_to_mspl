#!/usr/bin/python


import os
import logging

import core_data

import hyportage_data
import hyportage_ids
import hyportage_pattern
import utils

"""
This file contains the references to the global data of our implementation,
i.e., the hyportage data and its configuration
"""


__author__ = "Michael Lienhardt"
__copyright__ = "Copyright 2017, Michael Lienhardt"
__license__ = "GPL3"
__version__ = "0.5"
__maintainer__ = "Michael Lienhardt"
__email__ = "michael.lienhardt@laposte.net"
__status__ = "Prototype"


###############################
# PATHS

local_path = os.path.dirname(os.path.realpath(__file__))
# the path and encoding of the hyportage data
hyportage_db_path_default = os.path.abspath(os.path.join(local_path, "../data/hyportage/hyportage.pickle"))
hyportage_db_save_modality_default = "pickle"
# the path and encoding of the configuration data
config_db_path_default = os.path.abspath(os.path.join(local_path, "../data/portage/config.pickle"))
config_db_save_modality_default = "pickle"


###############################
# HYPORTAGE AND CONFIG DATA

# hyportage data
hyportage_db_loaded = False
id_repository = hyportage_ids.id_repository_create()
pattern_repository = hyportage_pattern.pattern_repository_create()
mspl = hyportage_data.mspl_create()
spl_groups = hyportage_data.spl_groups_create()

# configuration data
config_db_loaded = False
config = core_data.Config()
mspl_config = core_data.MSPLConfig()
keyword_list = []
installed_packages = core_data.dictSet()
world = set()

# annex info
simplify_mode = "individual"


###############################
# LOAD FUNCTIONS

def load_config(path=config_db_path_default, save_modality=config_db_save_modality_default):
	global config_db_loaded
	global config, mspl_config, keyword_list, installed_packages, world
	utils.phase_start("Loading the hyportage config.")
	if not config_db_loaded:
		if os.path.exists(path):
			config = utils.load_data_file(path, save_modality)
		else:
			logging.info("No config found: creating an empty one")
			config = core_data.Config()
		mspl_config = config.mspl_config
		keyword_list = config.keyword_list
		installed_packages = config.installed_packages
		world = config.world
		config_db_loaded = True
	utils.phase_end("Loading Completed")


def load_hyportage(path=hyportage_db_path_default, save_modality=hyportage_db_save_modality_default):
	utils.phase_start("Loading the hyportage database.")
	global hyportage_db_loaded
	global pattern_repository, id_repository, mspl, spl_groups
	if not hyportage_db_loaded:
		if os.path.exists(path):
			pattern_repository, id_repository, mspl, spl_groups = utils.load_data_file(path, save_modality)
		else:
			logging.info("No hyportage database found: creating an empty one")
			pattern_repository = hyportage_pattern.PatternRepository()
			id_repository = hyportage_ids.IDRepository()
			mspl = hyportage_data.mspl_create()
			spl_groups = hyportage_data.spl_groups_create()
		hyportage_db_loaded = True
	utils.phase_end("Loading Completed")


def load(
		hyportage_db_path=hyportage_db_path_default, hyportage_db_save_modality=hyportage_db_save_modality_default,
		config_db_path=config_db_path_default, config_db_save_modality=config_db_save_modality_default):
	load_config(config_db_path, config_db_save_modality)
	load_hyportage(hyportage_db_path, hyportage_db_save_modality)


###############################
# SAVE FUNCTIONS


def save_configuration(path=config_db_path_default, save_modality=config_db_save_modality_default):
	utils.phase_start("Saving the hyportage config.")
	global config, mspl_config
	mspl_config.new_masks = False
	mspl_config.new_use_declaration_eapi4 = False
	mspl_config.new_use_declaration_eapi5 = False
	mspl_config.new_keywords_config = False
	mspl_config.new_licenses_config = False
	mspl_config.new_use_flag_config = False
	utils.store_data_file(path, config, save_modality)
	utils.phase_end("Saving Completed")


def save_hyportage(path=config_db_path_default, save_modality=config_db_save_modality_default):
	utils.phase_start("Saving the hyportage database.")
	global pattern_repository, id_repository, mspl, spl_groups
	data = pattern_repository, id_repository, mspl, spl_groups
	utils.store_data_file(path, data, save_modality)
	utils.phase_end("Saving Completed")



