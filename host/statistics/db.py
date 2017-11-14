
#######################################
# This file offers a simple interface that loads the hyportage data and give direct pointers to it
#######################################


import os

import core_data

import hyportage_ids
import hyportage_pattern

import utils


__author__ = "Michael Lienhardt"
__copyright__ = "Copyright 2017, Michael Lienhardt"
__license__ = "ISC"
__version__ = "0.5"
__maintainer__ = "Michael Lienhardt"
__email__ = "michael.lienhardt@laposte.net"
__status__ = "Prototype"


# the path and encoding of the hyportage data
db_hyportage_path = os.path.abspath(os.path.join(os.path.dirname(os.path.realpath(__file__)), "../data/hyportage/hyportage.pickle"))
db_hyportage_save_modality = "pickle"


# the path and encoding of the configuration data
db_configuration_path = os.path.abspath(os.path.join(os.path.dirname(os.path.realpath(__file__)), "../data/portage/config.pickle"))
db_configuration_save_modality = "pickle"


hyportage_db_loaded = False
# hyportage data
pattern_repository = hyportage_pattern.pattern_repository_create()
flat_pattern_repository = {}
id_repository = hyportage_ids.id_repository_create()
mspl = {}
spl_groups = {}
# configuraton data
config = core_data.Config()
mspl_config = core_data.MSPLConfig()
keyword_list = None
installed_packages = None
world = None


def load_hyportage():
	utils.phase_start("Loading the hyportage database.")
	global hyportage_db_loaded
	global pattern_repository, flat_pattern_repository, id_repository, mspl, spl_groups
	global config, mspl_config, keyword_list, installed_packages, world
	if not hyportage_db_loaded:
		pattern_repository, id_repository, mspl, spl_groups = utils.load_data_file(db_hyportage_path, db_hyportage_save_modality)
		flat_pattern_repository = pattern_repository[1].copy()
		for local_map in pattern_repository[0].values():
			flat_pattern_repository.update(local_map)
		config = utils.load_data_file(db_configuration_path, db_configuration_save_modality)
		mspl_config = config.mspl_config
		keyword_list = config.keyword_list
		installed_packages = config.installed_packages
		world = config.world
		hyportage_db_loaded = True
	utils.phase_end("Loading Completed")


def filter_function_simple(x):
	return True