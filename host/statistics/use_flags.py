
import json
import logging
import os

import hyportage_data
import hyportage_pattern
import utils

from host.scripts import hyportage_db

__author__ = "Michael Lienhardt"
__copyright__ = "Copyright 2017, Michael Lienhardt"
__license__ = "ISC"
__version__ = "0.5"
__maintainer__ = "Michael Lienhardt"
__email__ = "michael.lienhardt@laposte.net"
__status__ = "Prototype"



##########################################################################
# 1. INDIVIDUAL FUNCTIONS
##########################################################################

data = {}


##########################################
# CORE

def core():
	utils.phase_start("Computing the USE Flags Core Statistics.")
	use_flags_max = 0
	use_flags_sum = 0
	use_flags_min = 100
	spl_min = []
	spl_max = []
	nb_spl = len(hyportage_db.mspl)
	for spl in hyportage_db.mspl.values():
		use_flag_size = len(hyportage_data.spl_get_iuses_default(spl))
		if use_flag_size < use_flags_min:
			use_flags_min = use_flag_size
			spl_min = [spl.name]
		elif use_flag_size == use_flags_min: spl_min.append(spl.name)
		if use_flag_size > use_flags_max:
			use_flags_max = use_flag_size
			spl_max = [spl.name]
		elif use_flag_size == use_flags_max: spl_max.append(spl.name)
		use_flags_sum = use_flags_sum + use_flag_size
	res = {
		'min': use_flags_min,
		'min_spl_list': sorted(spl_min),
		'max': use_flags_max,
		'max_spl_list': sorted(spl_max),
		'number': use_flags_sum,
		'spl_number': nb_spl,
		'average': use_flags_sum / nb_spl,
		'keywords': len(hyportage_db.keywords)
	}
	global data
	statistics['core'] = res
	utils.phase_end("Computation Completed")


def write_core(path, data):
	with open(path, "a") as f:
		f.write("## Core Statistics\n")
		f.write("\n")
		f.write("In this section, we give general statistics of USE flags:\n")
		f.write(" * minimum number of use flag per package: " + str(data['min']) + "\n")
		f.write("   * number of packages with this number of use flags: " + str(len(data['min_spl_list'])) + "\n")
		f.write(" * maximum number of use flag per package: " + str(data['max']) + "\n")
		f.write("   * number of packages with this number of use flags: " + str(len(data['max_spl_list'])) + "\n")
		f.write(" * average number of use flags: " + str(data['number']) + " / " + str(data['spl_number']) + " = " + str(data['average']) + "\n")
		f.write(" * number of additional use flags from arch: " + str(data['keywords']) + "\n")
		f.write("\n")
		f.write("\n")


##########################################
# MISSING LOCALLY

def missing_locally():
	utils.phase_start("Computing the USE Flags ``Missing Locally''  Statistics.")
	data = {}
	for spl in hyportage_db.mspl.values():
		diff = spl.required_iuses_local.difference(spl.iuses_default)
		diff.difference_update(hyportage_data.keywords_get_core_set(spl.keywords_list))
		if diff:
			data[spl.name] = sorted(diff)
	missing_use_flags = {use_flag for use_flags in data.values() for use_flag in use_flags}
	res = {
		'use_flags': sorted(missing_use_flags),
		'use_flag_number': len(missing_use_flags),
		'spl_number': len(data),
		'data': data
	}
	global data
	statistics['missing_locally'] = res
	utils.phase_end("Computation Completed")


def write_missing_locally(path, data):
	with open(path, 'a') as f:
		print("computing locally missing use flags")
		f.write("## Locally Missing USE Flags\n")
		f.write("\n")
		f.write("Here we analyze we the USE flags that are locally missing from a package,\n")
		f.write(" i.e., that are not declared in a package but used in its own constraints.\n")
		f.write("\n")
		f.write("Such USE flags must then be declared in the portage profile,\n")
		f.write(" otherwise this inconsistency means that the package cannot be installed\n")
		f.write("\n")
		f.write("\n")
		f.write("**1. Core Statistics**\n")
		f.write(" * Number of packages with missing USE flags: " + str(data['spl_number']) + "\n")
		f.write(" * Number of missing USE flags: " + str(data['use_flag_number']) + "\n")
		f.write(" * List of missing USE flags:\n")
		f.write("```\n")
		if data['use_flags']:
			f.write("\n")
			f.write(",\n".join(["    " + use_flag for use_flag in data['use_flags']]))
			f.write("\n]\n")
		else: f.write("[]\n")
		f.write("```\n")
		f.write("\n")
		f.write("\n")
		f.write("**2. Per Package Statistics**\n")
		f.write("```\n")
		for key, v in data['data'].iteritems():
			f.write(key + ": " + str(v) + "\n")
		f.write("```\n")
		f.write("\n")
		f.write("\n")


##########################################
# MISSING EXTERNALLY

def missing_externally():
	utils.phase_start("Computing the USE Flags ``Missing Externally''  Statistics.")
	data = {}
	for pattern, el in hyportage_db.flat_pattern_repository.iteritems():
		installable = False
		missing = {}
		for spl in hyportage_pattern.pattern_repository_element_get_spls(el, hyportage_db.mspl, hyportage_db.spl_groups):
			diff = set(hyportage_pattern.pattern_repository_element_get_required_use_required(el)).difference(spl.iuses_default)
			diff.difference_update(hyportage_data.keywords_get_core_set(spl.keywords_list))
			if diff:
				missing[spl.name] = sorted(diff)
			else:
				installable = True
		if missing:
			data[hyportage_pattern.pattern_to_atom(pattern)] = {
				'installable': installable,
				'missing': missing
			}
	res = {
		'pattern_number': len(filter(lambda el: not el['installable'], data.values())),
		'spl_number': len({spl_name for el in data.values() for spl_name in el['missing'].keys()}),
		'use_flag_number': len({use_flag for el in data.values() for use_flags in el['missing'].values() for use_flag in use_flags}),
		'data': data
	}
	global data
	statistics['missing_externally'] = res
	utils.phase_end("Computation Completed")


def write_missing_externally(path, data):
	with open(path, 'a') as f:
		f.write("## Externally Missing USE Flags\n")
		f.write("\n")
		f.write("Here, we analyze the USE Flags that are externally missing,\n")
		f.write(" i.e., that are used in a [USE Dependency](https://devmanual.gentoo.org/general-concepts/dependencies/) but not declared in a related package\n")
		f.write("\n")
		f.write("This analysis is a bit more complex than the previous one,\n")
		f.write(" because a USE Dependency missing from a related package is not an hard problem,\n")
		f.write(" it just means that *this* package cannot solve that dependency (but another one can).\n")
		f.write("Hence our analysis is first structured by pattern, checking which patterns cannot be satisfied,\n")
		f.write("\n")
		f.write("\n")
		f.write("**1. Core Statistics**\n")
		f.write(" * Number of missing USE flags: " + str(data['use_flag_number']) + "\n")
		f.write(" * Number of packages with missing USE flags: " + str(data['spl_number']) + "\n")
		f.write(" * Number of unsolvable pattern due to missing USE flags: " + str(data['pattern_number']) + "\n")
		f.write("\n")
		f.write("\n")
		f.write("**2. Per Pattern Statistics**\n")
		f.write("```\n")
		for pattern, el in data['data'].iteritems():
			f.write(pattern + ": " + ("installable" if el['installable'] else "NOT installable") + "\n")
			for spl_name, use_flags in el['missing'].iteritems():
				f.write("    " + spl_name + ": " + str(sorted(use_flags)) + "\n")
		f.write("```\n")
		f.write("\n")
		f.write("\n")


##########################################################################
# 1. GLOBAL DATA GENERATION
##########################################################################

def write_init(path):
	with open(path, 'w') as f:
		f.write("# USE Flag Statistics\n")
		f.write("\n")
		f.write("\n")

statistics_path_md = os.path.abspath(
	os.path.join(os.path.dirname(os.path.realpath(__file__)), "../../use_flag_statistics.md"))
statistics_path_json = os.path.abspath(
	os.path.join(os.path.dirname(os.path.realpath(__file__)), "../../use_flag_statistics.json"))


def main():
	logging.basicConfig(format="%(levelname)s: %(message)s", level=logging.DEBUG)
	hyportage_db.load()
	core()
	missing_locally()
	missing_externally()
	##
	write_init(statistics_path_md)
	write_core(statistics_path_md, data['core'])
	write_missing_locally(statistics_path_md, data['missing_locally'])
	write_missing_externally(statistics_path_md, data['missing_externally'])

	with open(statistics_path_json, 'w') as f:
		json.dump(data, f)


if __name__ == "__main__":
	main()
