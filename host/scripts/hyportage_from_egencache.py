#!/usr/bin/python

import lrparsing
import multiprocessing
import string
import os

import hyportage_data
import constraint_parser
import constraint_ast_visitor


# in portage, we only consider the egencache files (and the other ones we generate), as it is the default behavior of emerge

######################################################################
### GET EGENCACHE FILES FOM A MD5-CACHE REPOSITORY
######################################################################


def get_egencache_files(path):
	"""
	returns the set of portage files to load
	"""
	files = []
	for root, dirnames, filenames in os.walk(path):
		for filename in filenames:
			path_file = os.path.join(root, filename)
			files.append(path_file)
	return files


######################################################################
### EXTRACT DATA FROM PACKAGE FILE NAMES AND PATH
######################################################################


def structure_package_name(package_name):
	"""
	this function splits a portage package name into relevant information
	"""
	filename_split = package_name.split("-")
	version_full, version = (None, None)
	if len(filename_split) > 1:
		check1 = filename_split[-1]
		check2 = filename_split[-2]
		if check1[0] == 'r' and check2[0].isdigit():
			revision = check1
			version = check2
			del filename_split[-2:]
			version_full = version + "-" + revision
		elif check1[0].isdigit():
			version = check1
			del filename_split[-1]
			version_full = version
	package_group = "-".join(filename_split)
	return (package_group, version_full, version)


def get_package_name_from_path(package_path):
	els = package_path.split(os.sep)
	package_name = "/".join(els[:-2]) if len(els) > 1 else els[-1]
	deprecated = (len(els) > 2) and (els[-3] == "deprecated")
	return (package_name, deprecated)


######################################################################
### GENERATE BASE SPL INFORMATION
######################################################################

def is_selection_required(ctx):
	if "default" not in ctx: return True
	if "suffix" in ctx:
		if (ctx['default'] == "-") and (ctx['suffix'] == "?"): return True
		else: return False
	if "prefix" in ctx:
		return (ctx['default'] == "-")
	return (ctx['default'] == "+")


class get_dependencies(constraint_ast_visitor.ASTVisitor):
	def __init__(self, package_name):
		super(constraint_ast_visitor.ASTVisitor, self).__init__()
		self.main_package_name = package_name
		self.res = hyportage_data.raw_dependencies_create()

	def visitRequiredSIMPLE(self, ctx):
		hyprtage_data.raw_dependencies_add_use(sef.res, ctx['use'])
	def visitCondition(self, ctx):
		hyprtage_data.raw_dependencies_add_use(sef.res, ctx['use'])
	def visitAtom(self, ctx):
		self.pattern = ctx['atom']
		hyportage_data.raw_dependencies_add_pattern(self.res, self.pattern)
	def visitSelection(self,ctx):
		use = ctx['use']
		if is_selection_required(ctx): hyportage_data.raw_dependencies_add_pattern_use(self.res, self.pattern, use)
		if 'suffix' in ctx: hyprtage_data.raw_dependencies_add_use(sef.res, use)


######################################################################
### LOAD A PORTAGE MD5-CACHE REPOSITORY INTO HYPORTAGE
######################################################################



def create_spl_from_egencache_file(file_path):
	"""
	create the spl structure of a portage md5-cache file, and stores it in the mspl global variable
	"""
	# 1. base information from the file name
	package_name, deprecated = get_package_name_from_path(file_path)
	package_group, version_full, version = constraint_parser.parse_package_name(package_name)
	# 2. informations from the file content
	data_tmp = {}
	with open(file_path, 'r') as f:
		for line in f:
			array = string.split(line, "=", 1)
			data_tmp[array[0]] = array[1][:-1]  # remove the \n at the end of the line
	keywords_string = data_tmp.get('KEYWORDS')
	slots_string = data_tmp.get('SLOT')
	iuses_string = data_tmp.get('IUSE')
	fm_local = data_tmp.get('REQUIRED_USE')
	fm_external = data_tmp.get('DEPEND')
	fm_runtime = data_tmp.get('RDEPEND')
	fm_unloop = data_tmp.get('PDEPEND')
	del data_tmp
	# 3. create the base data
	keywords = keywords_string.split() if keywords_string else ["*"]

	slots = slots_string.split("/") if slots_string else ["0", "0"]
	slot = slots[0]
	subslot = slots[1] if len(slots) == 2 else "0"

	iuses, use_selection = hyportage_data.use_selection_from_iuse_list(iuses_string.split() if iuses_string else [])

	fm_local = utils.compact_list(constraint_parser.translate_require(fm_local)) if fm_local else []
	fm_external = constraint_parser.translate_depend(fm_external) if fm_external else []
	fm_runtime = constraint_parser.translate_depend(fm_runtime) if fm_runtime else []
	fm_unloop = constraint_parser.translate_depend(fm_unloop) if fm_unloop else []
	fm_combined = utils.compact_list(fm_external + fm_runtime + fm_unloop)
	# 4. extracting the more structured data
	visitor = get_dependencies()
	visitor.visitRequired(fm_local)
	visitor.visitDepend(fm_combined)
	# 5. return the raw spl
	return {
		'name': package_name, 'group': package_group, 'deprecated': deprecated,
		'versions_full': version_full, 'version': version,
		'slot': slot, 'subslot': subslot,
		'fm_local': fm_local, 'fm_combined': fm_combined, 'raw_dependencies': visitor.res,
		# data that is extended by the profile_configuration and the user_configuration
		'environment_default': keywords,
		'iuses_default': iuses, 'use_selection_default': use_selection
		}





def load_files_egencache(concurrent_map, filepaths):
	return concurrent_map(load_file_egencache, filepaths)

