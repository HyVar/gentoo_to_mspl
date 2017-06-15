#!/usr/bin/python

import os.path
import json
import multiprocessing
import time
import re
import timeit

import egencache_utils
import constraint_parser
import extract_id_maps
import extract_dependencies
import extract_package_groups
import atom_matching


path_to_data = os.path.realpath("../../../host/portage/gen/md5-cache")
filenames = ["sys-fs/udev-232-r2", "kde-plasma/powerdevil-5.8.5", "sys-devel/automake-1.15"]

constraint_list = [ "media-libs/freetype:2 virtual/opengl",
	">=kde-frameworks/kactivities-5.29.0:5 >=kde-frameworks/kauth-5.29.0:5[policykit] >=kde-frameworks/kcompletion-5.29.0:5 >=kde-frameworks/kconfig-5.29.0:5 >=kde-frameworks/kconfigwidgets-5.29.0:5 >=kde-frameworks/kcoreaddons-5.29.0:5 >=kde-frameworks/kcrash-5.29.0:5 >=kde-frameworks/kdbusaddons-5.29.0:5 >=kde-frameworks/kdelibs4support-5.29.0:5 >=kde-frameworks/kglobalaccel-5.29.0:5 >=kde-frameworks/ki18n-5.29.0:5 >=kde-frameworks/kidletime-5.29.0:5 >=kde-frameworks/kio-5.29.0:5 >=kde-frameworks/knotifications-5.29.0:5 >=kde-frameworks/knotifyconfig-5.29.0:5 >=kde-frameworks/kservice-5.29.0:5 >=kde-frameworks/kwayland-5.29.0:5 >=kde-frameworks/kwidgetsaddons-5.29.0:5 >=kde-frameworks/kxmlgui-5.29.0:5 >=kde-frameworks/solid-5.29.0:5 >=kde-plasma/libkscreen-5.8.5:5 >=kde-plasma/plasma-workspace-5.8.5:5 >=dev-qt/qtdbus-5.6.1:5 >=dev-qt/qtgui-5.6.1:5 >=dev-qt/qtwidgets-5.6.1:5 >=dev-qt/qtx11extras-5.6.1:5 virtual/libudev:= x11-libs/libxcb wireless? ( >=kde-frameworks/bluez-qt-5.29.0:5 >=kde-frameworks/networkmanager-qt-5.29.0:5 ) sys-devel/make >=dev-util/cmake-3.7.2 >=sys-apps/sed-4 dev-util/desktop-file-utils x11-misc/shared-mime-info >=kde-frameworks/extra-cmake-modules-5.29.0:5 handbook? ( >=kde-frameworks/kdoctools-5.29.0:5 ) >=dev-qt/qtcore-5.6.1:5 dev-util/desktop-file-utils app-arch/xz-utils",
	"media-libs/freetype:2= virtual/opengl",
	"virtual/pkgconfig java? ( >=virtual/jdk-1.4 ) python? ( >=dev-python/cython-0.16[python_targets_python2_7(-)?,python_targets_python3_4(-)?,python_targets_python3_5(-)?,-python_single_target_python2_7(-),-python_single_target_python3_4(-),-python_single_target_python3_5(-)] ) bluetooth? ( net-wireless/bluez ) gpm? ( >=sys-libs/gpm-1.20 ) iconv? ( virtual/libiconv ) icu? ( dev-libs/icu:= ) python? ( python_targets_python2_7? ( >=dev-lang/python-2.7.5-r2:2.7 ) python_targets_python3_4? ( dev-lang/python:3.4 ) python_targets_python3_5? ( dev-lang/python:3.5 ) >=dev-lang/python-exec-2:=[python_targets_python2_7(-)?,python_targets_python3_4(-)?,python_targets_python3_5(-)?,-python_single_target_python2_7(-),-python_single_target_python3_4(-),-python_single_target_python3_5(-)] ) ncurses? ( sys-libs/ncurses:0= ) nls? ( virtual/libintl ) tcl? ( >=dev-lang/tcl-8.4.15:0= ) usb? ( virtual/libusb:0 ) X? ( x11-libs/libXaw ) ocaml? ( >=dev-ml/findlib-1.0.4-r1 ) java? ( >=dev-java/java-config-2.2.0-r3 ) !<sys-devel/gettext-0.18.1.1-r3 || ( >=sys-devel/automake-1.15:1.15 ) >=sys-devel/autoconf-2.69 >=sys-devel/libtool-2.4 virtual/pkgconfig virtual/pkgconfig"
	]

# Grammar test
def constraint_test(constraint_list):
	identifier = 1
	syntax_error_listener = constraint_parser.SPLParserErrorListener()
	syntax_error_listener.stage = 'external'
	for constraint in constraint_list:
		syntax_error_listener.spl = "dependency " + str(identifier)
		syntax_error_listener.parsed_string = constraint
		antlr_ast = constraint_parser.SPLParserexternal(constraint, syntax_error_listener)
		ast = constraint_parser.ast_translator.visitDepend(antlr_ast)
		print("==========")
		print("  " + syntax_error_listener.spl)
		#print(str(ast))
		print(json.dumps(ast, sort_keys=True, indent=4, separators=(',', ': ')))


def test_list(concurrent_map, paths):
	print("Translated MSPL:")
	raw_mspl = egencache_utils.load_files_egencache(concurrent_map, paths)
	print("===============")
	print(json.dumps(raw_mspl, sort_keys=True, indent=4, separators=(',', ': ')))
	print("===============")
	print("Package Groups:")
	package_groups = extract_package_groups.from_mspl_list(concurrent_map, raw_mspl)
	print("===============")
	print(json.dumps({ k: v['implementations'] for k,v in package_groups.iteritems() }, sort_keys=True, indent=4, separators=(',', ': ')))
	print("===============")
	print("Translated AST:")
	asts = constraint_parser.parse_mspl(concurrent_map, raw_mspl)
	print("===============")
	#for spl_name, local_ast, combined_ast in asts:
	#	print(json.dumps({'name': spl_name, 'local': local_ast, 'combined': combined_ast}, sort_keys=True, indent=4, separators=(',', ': ')))
	print("===============")
	print("Atom Matching Mapping")
	atom_mapping = atom_matching.extract_atom_mapping(concurrent_map, package_groups, asts)
	print("===============")
	for k, v in atom_mapping.iteritems():
		print(str(k) + " => " + str([ spl['name'] for spl in v ]))
	return
	print("===============")
	print("Dependencies:")
	dependencies = concurrent_map(extract_dependencies.generate_dependencies_ast, asts)
	print("===============")
	print(json.dumps(dependencies, sort_keys=True, indent=4, separators=(',', ': ')))
	print("===============")
	print("Name Mapping:")
	mappings = extract_id_maps.create_empty_name_mappings()
	map_id_name, map_name_id = mappings
	mappings_list = concurrent_map(extract_id_maps.generate_name_mappings_spl, raw_mspl)
	map(lambda x: extract_id_maps.update_name_mappings(mappings, x), mappings_list)
	print("===============")
	print(json.dumps({'map_name_id': map_name_id, 'map_id_name': map_id_name}, sort_keys=True, indent=4, separators=(',', ': ')))
	print("===============")
	for spl_name,deps in dependencies:
		print(spl_name + ": " + str(deps))


def test_full():
	pool = multiprocessing.Pool(3)
	concurrent_map = pool.map
	concurrent_map = map
	#gentoo_rec.available_cores = 3
	print "loading files ... ",
	t = time.time()
	mspl = egencache_utils.get_egencache_files(path_to_data) # loads the mspl
	print(str(time.time() - t) + "s, " + ("ok" if mspl else "ERROR"))
	test_list(concurrent_map, mspl)


def test_package_groups(package_groups): # 10/06/2017: bug found by jacopo
	pool = multiprocessing.Pool(3)
	concurrent_map = pool.map # fails, I don't know why
	concurrent_map = map
	filenames = []
	for package_group in package_groups:
		array = package_group.split("/")
		path = os.path.join(path_to_data, array[0])
		filenames.extend([ os.path.join(path, filename) for filename in os.listdir(path) if array[1] in filename ])
	test_list(concurrent_map, filenames)




class C(object):
	def __init__(self, i):
		self.i = i
	def __hash__(self):
		return self.i
	def __eq__(self, other):
		if isinstance(other, C):
			return self.i == other.i
		else:
			return False

def test_class():
	o1 = C(0)
	o2 = C(1)
	o3 = C(0)
	d = {}
	d[o1] = 1
	d[o2] = 2
	d[o3] = 3
	print(str(d))
	print(str(hash(None)))
	l = map(o1.__eq__, [o3])
	print(str(l))


#			return ">"
#		elif len1 != len2:
#			return "<"
#		else:
#			return "="





# Single test
filenames = [ "sys-fs/udev-232-r2", "kde-plasma/powerdevil-5.8.5", "sys-devel/automake-1.15" ]

if __name__ == "__main__":
	#print(str(test_comparison1("sys-libs/ncurses-5.9-r3", "sys-libs/ncurses-5.9-r101")))
	#test_comparison("1", "-")
	test_package_groups([ "app-shells/bash", "sys-libs/ncurses", "virtual/libintl", "sys-libs/readline" ]) 
	#print( "\"10.toto\" < \"1.tata\": " + str("10.toto" < "1.tata"))
	#print("\"1.15_alpha\" < \"1.15_beta\": " + str("1.15_alpha" < "1.15_beta"))
	#load_test()
	#constraint_test(constraint_list)
	#test_jquery()