#!/usr/bin/python

import lrparsing

######################################################################
### LRPARSING PARSERS
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

	START=require


class depend(lrparsing.Grammar):
	condition = lrparsing.Repeat(T.NOT, min=0, max=1) + T.ID + T.IMPLIES
	choice = T.OR | T.ONEMAX | T.XOR
	selection = lrparsing.Repeat(T.NOT, min=0, max=1) + T.ID + lrparsing.Repeat(T.LPAREN + T.ID + T.RPAREN, min=0, max=1) + lrparsing.Repeat(T.IMPLIES | T.ID, min=0, max=1)
	depend_element = lrparsing.Choice(
		lrparsing.Repeat(T.NOT, min=0, max=2) + T.ID + lrparsing.Repeat(T.LBRACKET + lrparsing.List(selection, T.COMMA) + T.RBRACKET, min=0, max=1),
		lrparsing.Repeat(condition | choice, min=0, max=1) + T.LPAREN + lrparsing.Repeat(lrparsing.THIS) + T.RPAREN)
	depend = lrparsing.Repeat(depend_element)

	START=depend

lrparsing.compile_grammar(require)
lrparsing.compile_grammar(depend)

######################################################################
### TRANSLATE ATOMS INTO HASHABLE PATTERNS
######################################################################

def parse_package_name(package_name):
	"""
	this function splits a portage package name into relevant information
	"""
	filename_split = package_name.split("-")
	version_full, version = None, None
	end = None
	if len(filename_split) > 1:
		check1 = filename_split[-1]
		check2 = filename_split[-2]
		if check1[0] == 'r' and check2[0].isdigit():
			revision = check1
			version = check2
			version_full = version + "-" + revision
			end = -2
		elif check1[0].isdigit():
			version = check1
			version_full = version
			end = -1
	package_group = "-".join(filename_split[:end])
	return (package_group, version_full, version)


def pattern_create_from_atom(atom):
	#print("parsing atom " + str(atom))
	# 1. version operator
	vop = None
	begin = 0
	if atom[0] in "=<>~":
		if atom[1] == "=":
			vop = atom[:2]
			begin = 2
		else:
			vop = atom[0]
			begin = 1
	# 2. slots
	sop = None
	slot = None
	subslot = None
	slot_position = atom.find(":")
	if slot_position != -1:
		slots = atom[slot_position+1:].split("/")
		atom = atom[begin:slot_position]
		slot = slots[0]
		if slot == "*":
			sop = "*"
			slot = None
		elif slot == "=":
			sop = "="
			slot = None
		elif slot[-1] == "=":
			sop = "="
			slot = slot[:-1]
		elif len(slots) > 1:
			subslot = slots[1]

	# 3. version
	package_group, version_full, version = parse_package_name(atom)
	has_star = False
	if (version_full is not None) and (version_full[-1] == "*"):
		has_star = True
		version_full =  version_full[:-1]
		if version[-1] == "*": version = version[:-1]
	return (vop, package_group, version_full, version, has_star, slot, subslot, sop)


############################
# matching functions

def match_only_package_group(pattern, package_group):
	pattern_package_group = pattern[1]
	if pattern_package_group == "*/*":
		return True
	elif (pattern_package_group[0] != "*") and (pattern_package_group[-1] != "*"):
		return self.package_group == group_name
	elif pattern_package_group[0] != "*":
		pattern_subgroup = pattern_package_group[2:]
		els = package_group[1].split("/")
		return pattern_subgroup == els[-1]
	else:
		pattern_category = pattern_package_group[:-2]
		els = package_group[1].split("/")
		return pattern_category == els[-2]

def match_only_package_version(pattern, version_full, version):
	pattern_vop, pattern_version_full, pattern_version, pattern_has_star = pattern[0], pattern[2], pattern[3], pattern[4]

	if (pattern_version_full is None) or (pattern_vop is None):
		return True
	compare = compare_version(version_full, pattern_version_full)
	if pattern_vop == ">=":
		if compare < 0:
			return False
	elif pattern_vop == ">":
		if compare <= 0:
			return False
	elif pattern_vop == "~":
		if pattern_version != version:
			return False
	elif pattern_vop == "=":
		if pattern_has_star:
			if not version_full.startwith(pattern_version_full):
				return False
		else:
			if compare != 0:
				return False
	elif pattern_vop == "<=":
		if compare > 0:
			return False
	elif pattern_vop == "<":
		if compare >= 0:
			return False
	return True

def match_only_slot(pattern, slot, subslot):
	pattern_slot, pattern_subslot, pattern_sop = pattern[5], pattern[6], pattern[7]
	if pattern_slot:
		if pattern_slot != slot:
			return False
	if pattern_subslot:
		if pattern_subslot != subslot:
			return False
	return True


def match_package_path(pattern, package_name):
	package_group, version_full, version = parse_package_name(package_name)
	return match_only_package_group(pattern, package_group) and match_only_package_version(pattern, version_full, version)



######################################################################
### TRANSLATOR INTO OUR INTERNAL REPRESENTATION
######################################################################

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

	res = { 'type': "selection", 'use': use }
	if prefix: res['prefix'] = prefix
	if (len(parse_tree) > i + 2) and (parse_tree[i][1] == "("):
		res['default'] = parse_tree[i+1][1]
		i = i+3
	if len(parse_tree) > i: suffix = parse_tree[i][1]
	if suffix: res['suffix'] = suffix
	return res

###

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
		use = parse_tree[1][2]
		i = 3
	else:
		use = parse_tree[1][1]
		i = 2
	res = { 'type': "rsimple", 'use': use }
	if neg: res['not'] = neg
	if len(parse_tree) > i:
		res['selection'] = [ visit_node_selection(el) for el in filter(lambda x: x[0].name == "selection", parse_tree[i:])]
	return res


def visit_node_require(parse_tree):
	return [ visit_node_require_element(el) for el in parse_tree[1:] ]

###

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
	res = { 'type': "dsimple", 'atom': pattern_create_from_atom(atom) }
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



def visit(parse_tree, indent=""):
	if not isinstance(parse_tree[0], lrparsing.TokenSymbol):
		print(indent + "1: " + parse_tree[0].name)
		for element in parse_tree[1:]:
			visit(element, indent + "  ")
	else:
		print(indent + "2: " + parse_tree[1])






constraint_list = [ "media-libs/freetype:2 virtual/opengl",
	">=kde-frameworks/kactivities-5.29.0:5 >=kde-frameworks/kauth-5.29.0:5[policykit] >=kde-frameworks/kcompletion-5.29.0:5 >=kde-frameworks/kconfig-5.29.0:5 >=kde-frameworks/kconfigwidgets-5.29.0:5 >=kde-frameworks/kcoreaddons-5.29.0:5 >=kde-frameworks/kcrash-5.29.0:5 >=kde-frameworks/kdbusaddons-5.29.0:5 >=kde-frameworks/kdelibs4support-5.29.0:5 >=kde-frameworks/kglobalaccel-5.29.0:5 >=kde-frameworks/ki18n-5.29.0:5 >=kde-frameworks/kidletime-5.29.0:5 >=kde-frameworks/kio-5.29.0:5 >=kde-frameworks/knotifications-5.29.0:5 >=kde-frameworks/knotifyconfig-5.29.0:5 >=kde-frameworks/kservice-5.29.0:5 >=kde-frameworks/kwayland-5.29.0:5 >=kde-frameworks/kwidgetsaddons-5.29.0:5 >=kde-frameworks/kxmlgui-5.29.0:5 >=kde-frameworks/solid-5.29.0:5 >=kde-plasma/libkscreen-5.8.5:5 >=kde-plasma/plasma-workspace-5.8.5:5 >=dev-qt/qtdbus-5.6.1:5 >=dev-qt/qtgui-5.6.1:5 >=dev-qt/qtwidgets-5.6.1:5 >=dev-qt/qtx11extras-5.6.1:5 virtual/libudev:= x11-libs/libxcb wireless? ( >=kde-frameworks/bluez-qt-5.29.0:5 >=kde-frameworks/networkmanager-qt-5.29.0:5 ) sys-devel/make >=dev-util/cmake-3.7.2 >=sys-apps/sed-4 dev-util/desktop-file-utils x11-misc/shared-mime-info >=kde-frameworks/extra-cmake-modules-5.29.0:5 handbook? ( >=kde-frameworks/kdoctools-5.29.0:5 ) >=dev-qt/qtcore-5.6.1:5 dev-util/desktop-file-utils app-arch/xz-utils",
	"media-libs/freetype:2= virtual/opengl",
	"virtual/pkgconfig java? ( >=virtual/jdk-1.4 ) python? ( >=dev-python/cython-0.16[python_targets_python2_7(-)?,python_targets_python3_4(-)?,python_targets_python3_5(-)?,-python_single_target_python2_7(-),-python_single_target_python3_4(-),-python_single_target_python3_5(-)] ) bluetooth? ( net-wireless/bluez ) gpm? ( >=sys-libs/gpm-1.20 ) iconv? ( virtual/libiconv ) icu? ( dev-libs/icu:= ) python? ( python_targets_python2_7? ( >=dev-lang/python-2.7.5-r2:2.7 ) python_targets_python3_4? ( dev-lang/python:3.4 ) python_targets_python3_5? ( dev-lang/python:3.5 ) >=dev-lang/python-exec-2:=[python_targets_python2_7(-)?,python_targets_python3_4(-)?,python_targets_python3_5(-)?,-python_single_target_python2_7(-),-python_single_target_python3_4(-),-python_single_target_python3_5(-)] ) ncurses? ( sys-libs/ncurses:0= ) nls? ( virtual/libintl ) tcl? ( >=dev-lang/tcl-8.4.15:0= ) usb? ( virtual/libusb:0 ) X? ( x11-libs/libXaw ) ocaml? ( >=dev-ml/findlib-1.0.4-r1 ) java? ( >=dev-java/java-config-2.2.0-r3 ) !<sys-devel/gettext-0.18.1.1-r3 || ( >=sys-devel/automake-1.15:1.15 ) >=sys-devel/autoconf-2.69 >=sys-devel/libtool-2.4 virtual/pkgconfig virtual/pkgconfig",
	">kde-frameworks/kauth-5.29.0:5[policykit(-)=, python_targets_python2_7(-)?]"
	]

def main():
	lrparsing.compile_grammar(depend)
	for constraint in constraint_list:
		print("================")
		print(constraint)
		print("--")
		print(translate_depend(constraint))

if __name__ == "__main__":
	main()


