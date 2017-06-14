#!/usr/bin/python

import os.path
import json
import multiprocessing
import time

import egencache_utils
import constraint_parser
import extract_id_maps
import extract_dependencies
import extract_package_groups
import gentoo_rec



path_to_data = os.path.realpath("../../../host/portage/gen/md5-cache")

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

# Single test
test_filename1 = "sys-fs/udev-232-r2"
test_filename1 = "kde-plasma/powerdevil-5.8.5"
test_file1_path = os.path.join(path_to_data, test_filename1)
test_filename2 = "sys-devel/automake-1.15"
test_file2_path = os.path.join(path_to_data, test_filename2)
pool = None

def list_test(concurrent_map, paths):
	print("Translated MSPL:")
	mspl = concurrent_map(egencache_utils.load_file_egencache, paths)
	print("===============")
	print(json.dumps(mspl, sort_keys=True, indent=4, separators=(',', ': ')))
	print("===============")
	print("Translated AST:")
	asts = concurrent_map(constraint_parser.parse_spl, mspl)
	print("===============")
	for spl_name, local_ast, combined_ast in asts:
		print(json.dumps({'name': spl_name, 'local': local_ast, 'combined': combined_ast}, sort_keys=True, indent=4, separators=(',', ': ')))
	print("===============")
	print("Dependencies:")
	dependencies = concurrent_map(extract_dependencies.generate_dependencies_ast, asts)
	print("===============")
	print(json.dumps(dependencies, sort_keys=True, indent=4, separators=(',', ': ')))
	print("===============")
	print("Package Groups:")
	package_groups = extract_package_groups.create_empty_package_groups()
	package_groups_list = concurrent_map(extract_package_groups.generate_package_group_spl, mspl)
	map(lambda x: extract_package_groups.update_package_groups(package_groups, x), package_groups_list)
	print("===============")
	print(json.dumps(package_groups, sort_keys=True, indent=4, separators=(',', ': ')))
	print("===============")
	print("Name Mapping:")
	mappings = extract_id_maps.create_empty_name_mappings()
	map_id_name, map_name_id = mappings
	mappings_list = concurrent_map(extract_id_maps.generate_name_mappings_spl, mspl)
	map(lambda x: extract_id_maps.update_name_mappings(mappings, x), mappings_list)
	print("===============")
	print(json.dumps({'map_name_id': map_name_id, 'map_id_name': map_id_name}, sort_keys=True, indent=4, separators=(',', ': ')))
	print("===============")
	for spl_name,deps in dependencies:
		print(spl_name + ": " + str(deps))

def double_test():
	global pool
	gentoo_rec.mspl = pool.map(gentoo_rec.load_file_egencache, [test_file1_path, test_file2_path])
	gentoo_rec.parse_mspl()
	gentoo_rec.generate_all_information(".")
	res = { 'mspl': gentoo_rec.mspl, 'asts': gentoo_rec.asts }
	print(json.dumps(res , sort_keys=True, indent=4, separators=(',', ': ')))

def load_test():
	#gentoo_rec.available_cores = 3
	print "loading files ... ",
	t = time.time()
	mspl = egencache_utils.get_egencache_files(path_to_data) # loads the mspl
	print(str(time.time() - t) + "s, " + ("ok" if mspl else "ERROR"))
	list_test(map, mspl)


def test_jquery(): # 10/06/2017: bug found by jacopo
	path_to_data = os.path.realpath("../../../host/portage/gen/md5-cache/dev-ruby")
	paths = [ os.path.join(path_to_data, filename) for filename in os.listdir(path_to_data) if "jquery-ui-rails-" in filename ]
	list_test(map, paths)


constraint_list = [ #"media-libs/freetype:2 virtual/opengl",
	#">=kde-frameworks/kactivities-5.29.0:5 >=kde-frameworks/kauth-5.29.0:5[policykit] >=kde-frameworks/kcompletion-5.29.0:5 >=kde-frameworks/kconfig-5.29.0:5 >=kde-frameworks/kconfigwidgets-5.29.0:5 >=kde-frameworks/kcoreaddons-5.29.0:5 >=kde-frameworks/kcrash-5.29.0:5 >=kde-frameworks/kdbusaddons-5.29.0:5 >=kde-frameworks/kdelibs4support-5.29.0:5 >=kde-frameworks/kglobalaccel-5.29.0:5 >=kde-frameworks/ki18n-5.29.0:5 >=kde-frameworks/kidletime-5.29.0:5 >=kde-frameworks/kio-5.29.0:5 >=kde-frameworks/knotifications-5.29.0:5 >=kde-frameworks/knotifyconfig-5.29.0:5 >=kde-frameworks/kservice-5.29.0:5 >=kde-frameworks/kwayland-5.29.0:5 >=kde-frameworks/kwidgetsaddons-5.29.0:5 >=kde-frameworks/kxmlgui-5.29.0:5 >=kde-frameworks/solid-5.29.0:5 >=kde-plasma/libkscreen-5.8.5:5 >=kde-plasma/plasma-workspace-5.8.5:5 >=dev-qt/qtdbus-5.6.1:5 >=dev-qt/qtgui-5.6.1:5 >=dev-qt/qtwidgets-5.6.1:5 >=dev-qt/qtx11extras-5.6.1:5 virtual/libudev:= x11-libs/libxcb wireless? ( >=kde-frameworks/bluez-qt-5.29.0:5 >=kde-frameworks/networkmanager-qt-5.29.0:5 ) sys-devel/make >=dev-util/cmake-3.7.2 >=sys-apps/sed-4 dev-util/desktop-file-utils x11-misc/shared-mime-info >=kde-frameworks/extra-cmake-modules-5.29.0:5 handbook? ( >=kde-frameworks/kdoctools-5.29.0:5 ) >=dev-qt/qtcore-5.6.1:5 dev-util/desktop-file-utils app-arch/xz-utils"
	#"media-libs/freetype:2= virtual/opengl"
	"virtual/pkgconfig java? ( >=virtual/jdk-1.4 ) python? ( >=dev-python/cython-0.16[python_targets_python2_7(-)?,python_targets_python3_4(-)?,python_targets_python3_5(-)?,-python_single_target_python2_7(-),-python_single_target_python3_4(-),-python_single_target_python3_5(-)] ) bluetooth? ( net-wireless/bluez ) gpm? ( >=sys-libs/gpm-1.20 ) iconv? ( virtual/libiconv ) icu? ( dev-libs/icu:= ) python? ( python_targets_python2_7? ( >=dev-lang/python-2.7.5-r2:2.7 ) python_targets_python3_4? ( dev-lang/python:3.4 ) python_targets_python3_5? ( dev-lang/python:3.5 ) >=dev-lang/python-exec-2:=[python_targets_python2_7(-)?,python_targets_python3_4(-)?,python_targets_python3_5(-)?,-python_single_target_python2_7(-),-python_single_target_python3_4(-),-python_single_target_python3_5(-)] ) ncurses? ( sys-libs/ncurses:0= ) nls? ( virtual/libintl ) tcl? ( >=dev-lang/tcl-8.4.15:0= ) usb? ( virtual/libusb:0 ) X? ( x11-libs/libXaw ) ocaml? ( >=dev-ml/findlib-1.0.4-r1 ) java? ( >=dev-java/java-config-2.2.0-r3 ) !<sys-devel/gettext-0.18.1.1-r3 || ( >=sys-devel/automake-1.15:1.15 ) >=sys-devel/autoconf-2.69 >=sys-devel/libtool-2.4 virtual/pkgconfig virtual/pkgconfig"
	]

if __name__ == "__main__":
	#load_test()
	constraint_test(constraint_list)
	#test_jquery()