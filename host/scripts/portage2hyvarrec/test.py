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
	for constraint in constraint_list:
		antlr_ast = constraint_parser.SPLParserexternal(constraint)
		ast = constraint_parser.ast_translator.visitDepend(antlr_ast)
		print("==========")
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
	gentoo_rec.available_cores = 3
	print "loading files ... ",
	t = time.time()
	mspl = gentoo_rec.load_repository_egencache(path_to_data,cores) # loads the mspl
	print(str(time.time() - t) + "s, " + ("ok" if gentoo_rec.mspl else "ERROR"))
	print "parsing the ast ... ",
	t = time.time()
	asts = gentoo_rec.parse_mspl(mspl,cores)  # loads the asts
	print(str(time.time() - t) + "s, " + ("ok" if gentoo_rec.asts else "ERROR"))
	print "generating the information ... ",
	t = time.time()
	gentoo_rec.generate_all_information(".") # loads the information and write the mapping in files
	print(str(time.time() - t) + "s")



def test_jquery(): # 10/06/2017: bug found by jacopo
	path_to_data = os.path.realpath("../../../host/portage/gen/md5-cache/dev-ruby")
	paths = [ os.path.join(path_to_data, filename) for filename in os.listdir(path_to_data) if "jquery-ui-rails-" in filename ]
	list_test(map, paths)


constraint_list = [ "media-libs/freetype:2 virtual/opengl",
	#">=kde-frameworks/kactivities-5.29.0:5 >=kde-frameworks/kauth-5.29.0:5[policykit] >=kde-frameworks/kcompletion-5.29.0:5 >=kde-frameworks/kconfig-5.29.0:5 >=kde-frameworks/kconfigwidgets-5.29.0:5 >=kde-frameworks/kcoreaddons-5.29.0:5 >=kde-frameworks/kcrash-5.29.0:5 >=kde-frameworks/kdbusaddons-5.29.0:5 >=kde-frameworks/kdelibs4support-5.29.0:5 >=kde-frameworks/kglobalaccel-5.29.0:5 >=kde-frameworks/ki18n-5.29.0:5 >=kde-frameworks/kidletime-5.29.0:5 >=kde-frameworks/kio-5.29.0:5 >=kde-frameworks/knotifications-5.29.0:5 >=kde-frameworks/knotifyconfig-5.29.0:5 >=kde-frameworks/kservice-5.29.0:5 >=kde-frameworks/kwayland-5.29.0:5 >=kde-frameworks/kwidgetsaddons-5.29.0:5 >=kde-frameworks/kxmlgui-5.29.0:5 >=kde-frameworks/solid-5.29.0:5 >=kde-plasma/libkscreen-5.8.5:5 >=kde-plasma/plasma-workspace-5.8.5:5 >=dev-qt/qtdbus-5.6.1:5 >=dev-qt/qtgui-5.6.1:5 >=dev-qt/qtwidgets-5.6.1:5 >=dev-qt/qtx11extras-5.6.1:5 virtual/libudev:= x11-libs/libxcb wireless? ( >=kde-frameworks/bluez-qt-5.29.0:5 >=kde-frameworks/networkmanager-qt-5.29.0:5 ) sys-devel/make >=dev-util/cmake-3.7.2 >=sys-apps/sed-4 dev-util/desktop-file-utils x11-misc/shared-mime-info >=kde-frameworks/extra-cmake-modules-5.29.0:5 handbook? ( >=kde-frameworks/kdoctools-5.29.0:5 ) >=dev-qt/qtcore-5.6.1:5 dev-util/desktop-file-utils app-arch/xz-utils"
	"media-libs/freetype:2= virtual/opengl"
	]

if __name__ == "__main__":
	constraint_test(constraint_list)
	#test_jquery()