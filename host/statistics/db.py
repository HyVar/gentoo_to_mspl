

import os

import hyportage
import hyportage_ids
import hyportage_data
import hyportage_pattern
import hyportage_configuration

import utils


__author__ = "Michael Lienhardt"
__copyright__ = "Copyright 2017, Michael Lienhardt"
__license__ = "ISC"
__version__ = "0.5"
__maintainer__ = "Michael Lienhardt"
__email__ = "michael.lienhardt@laposte.net"
__status__ = "Prototype"


db_hyportage_path = os.path.abspath(os.path.join(os.path.dirname(os.path.realpath(__file__)), "../data/hyportage/hyportage.enc"))
db_hyportage_save_modality = "pickle"


hyportage_db_loaded = False
pattern_repository = hyportage_pattern.pattern_repository_create()
flat_pattern_repository = {}
id_repository = hyportage_ids.id_repository_create()
keywords = set()
mspl = {}
spl_groups = {}
core_configuration = hyportage_configuration.core_configuration_create()
installed_spls = {}

def load_hyportage():
	utils.phase_start("Loading the hyportage database.")
	global hyportage_db_loaded, pattern_repository, flat_pattern_repository, id_repository, keywords, mspl, spl_groups, core_configuration, installed_spls
	if not hyportage_db_loaded:
		pattern_repository, id_repository, mspl, spl_groups, core_configuration, installed_spls = hyportage.load_hyportage(
			db_hyportage_path, db_hyportage_save_modality)
		flat_pattern_repository = pattern_repository[1]
		for local_map in pattern_repository[0].values():
			flat_pattern_repository.update(local_map)
		keywords = hyportage_data.keywords_get_core_set(hyportage_ids.id_repository_get_keywords(id_repository)[0])
		hyportage_db_loaded = True
	utils.phase_end("Loading Completed")
