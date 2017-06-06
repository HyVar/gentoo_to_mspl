#!/usr/bin/python

import gentoo_rec
import utils
import os.path
import json
import multiprocessing
import time

path_to_data = os.path.realpath("../../../host/portage/gen/md5-cache")

# Grammar test
constraint = "media-libs/freetype:2 virtual/opengl"
def constraint_test():
	global constraint
	ast = gentoo_rec.SPLParserexternal(constraint)
	ast_local = gentoo_rec.ast_translator.visitDepend(ast)
	print(json.dumps(ast_local, sort_keys=True, indent=4, separators=(',', ': ')))

# Single test
test_filename1 = "sys-fs/udev-232-r2"
test_filename1 = "kde-plasma/powerdevil-5.8.5"
test_file1_path = os.path.join(path_to_data, test_filename1)
test_filename2 = "sys-devel/automake-1.15"
test_file2_path = os.path.join(path_to_data, test_filename2)
pool = None

def simple_test():
	global pool
	multiprocessing.freeze_support()
	pool = multiprocessing.Pool(3)

	global test_file1_path
	gentoo_rec.trust_feature_declaration = False
	print("Translated SPL:")
	spl = gentoo_rec.load_file_egencache(test_file1_path)
	print("===============")
	print(json.dumps(spl, sort_keys=True, indent=4, separators=(',', ': ')))
	print("===============")
	print("Translated AST:")
	ast = gentoo_rec.parse_spl(spl)
	spl_name, local_ast, combined_ast = ast
	print("===============")
	print(json.dumps({'name': spl_name, 'local': local_ast, 'combined': combined_ast}, sort_keys=True, indent=4, separators=(',', ': ')))
	print("===============")
	print("Name Mapping:")
	mappings_list = [ gentoo_rec.generate_name_mappings_spl(spl,mspl,asts,map_name_id,map_id_name) ]
	mappings_list_annex = [ gentoo_rec.generate_use_mappings_ast(ast) ]
	mappings_list.extend(mappings_list_annex)
	map_id_name, map_name_id = gentoo_rec.create_empty_name_mappings()
	for local_map_id_name, local_map_name_id in mappings_list:
		map_id_name.update(local_map_id_name)
		map_name_id['package'].update(local_map_name_id['package'])
		map_name_id['context'].update(local_map_name_id['context'])
		utils.inline_combine_dicts(map_name_id['flag'], local_map_name_id['flag'], gentoo_rec.__gnm_combine_util)
		utils.inline_combine_dicts(map_name_id['slot'], local_map_name_id['slot'], gentoo_rec.__gnm_combine_util)
		utils.inline_combine_dicts(map_name_id['subslot'], local_map_name_id['subslot'], gentoo_rec.__gnm_combine_util)

	print("===============")
	print(json.dumps({'map_name_id': map_name_id, 'map_id_name': map_id_name}, sort_keys=True, indent=4, separators=(',', ': ')))
	print("===============")
	print("Dependencies:")
	dependencies = gentoo_rec.generate_dependencies_ast(ast)
	print("===============")
	print(json.dumps(dependencies, sort_keys=True, indent=4, separators=(',', ': ')))
	print("Package Groups:")
	gentoo_rec.mspl = [spl]
	gentoo_rec.generate_package_groups(pool)
	print("===============")
	print(json.dumps(gentoo_rec.package_groups, sort_keys=True, indent=4, separators=(',', ': ')))
	print("===============")

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




if __name__ == "__main__":
	load_test()
