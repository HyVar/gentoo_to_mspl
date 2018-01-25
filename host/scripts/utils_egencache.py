#!/usr/bin/python


import string
import os
import lrparsing

import hyportage_data
import core_data
import utils


"""
Module defining utility functions for manipulating egencache files.
In particular, it contains the function to translate an egencache file into an hyportage spl
"""


__author__ = "Michael Lienhardt & Jacopo Mauro"
__copyright__ = "Copyright 2017, Michael Lienhardt & Jacopo Mauro"
__license__ = "ISC"
__version__ = "0.5"
__maintainer__ = "Michael Lienhardt & Jacopo Mauro"
__email__ = "michael.lienhardt@laposte.net & mauro.jacopo@gmail.com"
__status__ = "Prototype"


######################################################################
# EGENCACHE FILES FUNCTIONS
######################################################################


def get_egencache_files(path):
	"""
	returns the set of portage files to load
	"""
	files = []
	for root, dirnames, filenames in os.walk(path, followlinks=True):
		for filename in filenames:
			path_file = os.path.join(root, filename)
			files.append(path_file)
	return files


def get_package_name_from_path(package_path):
	els = package_path.split(os.sep)
	package_name = "/".join(els[-2:]) if len(els) > 1 else els[-1]
	deprecated = (len(els) > 2) and (els[-3] == "deprecated")
	return package_name, deprecated


######################################################################
# TRANSLATE THE PORTAGE CONSTRAINT INTO THE HYPORTAGE AST
######################################################################


class T(lrparsing.TokenRegistry):
	ID = lrparsing.Token(re="[^\s[\]()^|?!,]+")
	# condition operators
	OR	 = lrparsing.Token('||')
	XOR	 = lrparsing.Token('^^')
	ONEMAX  = lrparsing.Token('??')
	NOT	 = lrparsing.Token('!')
	IMPLIES = lrparsing.Token('?')
	# special symbols
	LPAREN  = lrparsing.Token('(')
	RPAREN  = lrparsing.Token(')')
	LBRACKET= lrparsing.Token('[')
	RBRACKET= lrparsing.Token(']')
	# punctuation
	COMMA   = lrparsing.Token(',')


class require(lrparsing.Grammar):
	condition = lrparsing.Repeat(T.NOT, min=0, max=1) + T.ID + T.IMPLIES
	choice = T.OR | T.ONEMAX | T.XOR
	require_element = lrparsing.Choice(
		lrparsing.Repeat(T.NOT, min=0, max=1) + T.ID,
		lrparsing.Repeat(condition | choice, min=0, max=1) + T.LPAREN + lrparsing.Repeat(lrparsing.THIS) + T.RPAREN)
	require = lrparsing.Repeat(require_element)

	START = require


class depend(lrparsing.Grammar):
	condition = lrparsing.Repeat(T.NOT, min=0, max=1) + T.ID + T.IMPLIES
	choice = T.OR | T.ONEMAX | T.XOR
	selection = lrparsing.Repeat(T.NOT, min=0, max=1) + T.ID + lrparsing.Repeat(T.LPAREN + T.ID + T.RPAREN, min=0, max=1) + lrparsing.Repeat(T.IMPLIES | T.ID, min=0, max=1)
	depend_element = lrparsing.Choice(
		lrparsing.Repeat(T.NOT, min=0, max=2) + T.ID + lrparsing.Repeat(T.LBRACKET + lrparsing.List(selection, T.COMMA) + T.RBRACKET, min=0, max=1),
		lrparsing.Repeat(condition | choice, min=0, max=1) + T.LPAREN + lrparsing.Repeat(lrparsing.THIS) + T.RPAREN)
	depend = lrparsing.Repeat(depend_element)

	START = depend

lrparsing.compile_grammar(require)
lrparsing.compile_grammar(depend)


def visit_node_condition(parse_tree):
	if parse_tree[1][1] == "!": return { 'type': "condition", 'not': "!", 'use': parse_tree[2][1] }
	else: return { 'type': "condition", 'use': parse_tree[1][1] }


def visit_node_choice(parse_tree):
	return parse_tree[1][1]


def visit_node_selection(parse_tree):
	prefix = None
	suffix = None
	if parse_tree[1][1] == "!":
		prefix = "!"
		use = parse_tree[2][1]
		i = 3
	else:
		use = parse_tree[1][1]
		i = 2
	if use[0] == "-":
		prefix = "-"
		use = use[1:]
	if use[-1] == "=":
		suffix = "="
		use = use[:-1]

	res = { 'type': "selection", 'use': use }
	if prefix: res['prefix'] = prefix
	if (len(parse_tree) > i + 2) and (parse_tree[i][1] == "("):
		res['default'] = parse_tree[i+1][1]
		i = i+3
	if len(parse_tree) > i: suffix = parse_tree[i][1]
	if suffix: res['suffix'] = suffix
	return res

##


def visit_node_require_element(parse_tree):
	if parse_tree[1][0].name == "choice":
		return {
			'type': "rchoice",
			'choice': visit_node_choice(parse_tree[1]),
			'els': [ visit_node_require_element(el) for el in filter(lambda x: x[0].name == "require_element", parse_tree[3:])]
			}
	if parse_tree[1][0].name == "condition":
		return {
			'type': "rcondition",
			'condition': visit_node_condition(parse_tree[1]),
			'els': [ visit_node_require_element(el) for el in filter(lambda x: x[0].name == "require_element", parse_tree[3:])]
			}
	if parse_tree[1][1] == "(": # inner
		return {
			'type': "rinner",
			'els': [ visit_node_require_element(el) for el in filter(lambda x: x[0].name == "require_element", parse_tree[1:])]
			}
	neg = None
	if parse_tree[1][1] == "!": # not use
		neg = "!"
		use = parse_tree[2][1]
		i = 3
	else:
		use = parse_tree[1][1]
		i = 2
	res = { 'type': "rsimple", 'use': use }
	if neg: res['not'] = neg
	return res


def visit_node_require(parse_tree):
	return [ visit_node_require_element(el) for el in parse_tree[1:] ]

##


def visit_node_depend_element(parse_tree):
	if parse_tree[1][0].name == "choice":
		return {
			'type': "dchoice",
			'choice': visit_node_choice(parse_tree[1]),
			'els': [ visit_node_depend_element(el) for el in filter(lambda x: x[0].name == "depend_element", parse_tree[3:])]
			}
	if parse_tree[1][0].name == "condition":
		return {
			'type': "dcondition",
			'condition': visit_node_condition(parse_tree[1]),
			'els': [ visit_node_depend_element(el) for el in filter(lambda x: x[0].name == "depend_element", parse_tree[3:])]
			}
	if parse_tree[1][1] == "(": # inner
		return {
			'type': "dinner",
			'els': [ visit_node_depend_element(el) for el in filter(lambda x: x[0].name == "depend_element", parse_tree[1:])]
			}
	neg = None
	if parse_tree[1][1] == "!": # not atom
		if parse_tree[2][1] == "!":
			neg = "!!"
			atom = parse_tree[3][1]
			i = 4
		else:
			neg = "!"
			atom = parse_tree[2][1]
			i = 3
	else:
		atom = parse_tree[1][1]
		i = 2
	res = { 'type': "dsimple", 'atom': core_data.pattern_create_from_atom(atom) }
	if neg: res['not'] = neg
	if len(parse_tree) > i:
		res['selection'] = [ visit_node_selection(el) for el in filter(lambda x: x[0].name == "selection", parse_tree[i:])]
	return res


def visit_node_depend(parse_tree):
	return [ visit_node_depend_element(el) for el in parse_tree[1:] ]


############################
# main functions

def translate_require(require_string):
	return visit_node_require(require.parse(require_string)[1])


def translate_depend(depend_string):
	return visit_node_depend(depend.parse(depend_string)[1])


######################################################################
# TRANSLATE A EGENCACHE FILE INTO A HYPORTAGE SPL
######################################################################


def extract_iuse(iuse_list):
	use_flag_set = set()
	use_flag_manipulation = core_data.SetManipulation()
	for iuse in iuse_list:
		if iuse[0] == "+":
			iuse = iuse[1:]
			use_flag_manipulation.add(iuse)
		elif iuse[0] == "-":
			use_flag_manipulation.add(iuse)
			iuse = iuse[1:]
		use_flag_set.add(iuse)
	return use_flag_set, use_flag_manipulation


def create_spl_from_egencache_file(file_path):
	"""
	create the spl structure of a portage md5-cache file, and stores it in the mspl global variable
	"""
	# 1. base information from the file name
	package_name, deprecated = get_package_name_from_path(file_path)
	package_group, version_full, version = core_data.parse_package_name(package_name)
	# 2. information from the file content
	data_tmp = {}
	with open(file_path, 'r') as f:
		for line in f:
			array = string.split(line, "=", 1)
			data_tmp[array[0]] = array[1][:-1]  # remove the \n at the end of the line
	eapi = data_tmp.get('EAPI')
	iuses_string = data_tmp.get('IUSE')
	fm_local = data_tmp.get('REQUIRED_USE')
	fm_external = data_tmp.get('DEPEND')
	fm_runtime = data_tmp.get('RDEPEND')
	fm_unloop = data_tmp.get('PDEPEND')
	slots_string = data_tmp.get('SLOT')
	keywords_string = data_tmp.get('KEYWORDS')
	license = data_tmp.get('LICENSE')
	del data_tmp

	# 3. create the base data
	keywords = set(keywords_string.split()) if keywords_string else {"*"}

	slots = slots_string.split("/") if slots_string else ["0", "0"]
	slot = slots[0]
	subslot = slots[1] if len(slots) == 2 else slot
	# see https://devmanual.gentoo.org/general-concepts/slotting/index.html
	spl_core = core_data.spl_core_create(package_group, version_full, version, slot, subslot)

	iuses, use_manipulation = extract_iuse(iuses_string.split() if iuses_string else [])

	fm_local = utils.compact_list(translate_require(fm_local)) if fm_local else []
	fm_external = translate_depend(fm_external) if fm_external else []
	fm_runtime = translate_depend(fm_runtime) if fm_runtime else []
	fm_unloop = translate_depend(fm_unloop) if fm_unloop else []
	fm_combined = utils.compact_list(fm_external + fm_runtime + fm_unloop)
	# 5. return the raw spl
	return hyportage_data.SPL(
			eapi, package_name, spl_core, deprecated,
			iuses, use_manipulation, fm_local, fm_combined,
			keywords, license)


