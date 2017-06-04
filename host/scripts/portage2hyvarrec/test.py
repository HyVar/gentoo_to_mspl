#!/usr/bin/python

import gentoo_rec
import os.path
import json
import multiprocessing

path_to_data = os.path.realpath("../../../host/portage/usr/portage/metadata/md5-cache")

# Grammar test
constraint = "media-libs/freetype:2 virtual/opengl"
def constraint_test():
	global constraint
	ast = gentoo_rec.SPLParserexternal(constraint)
	ast_local = gentoo_rec.ast_translator.visitDepend(ast)
	print(json.dumps(ast_local, sort_keys=True, indent=4, separators=(',', ': ')))

# Single test
test_filename1 = "dev-games/ogre-1.9.0-r1"
test_file1_path = os.path.join(path_to_data, test_filename1)
test_filename2 = "media-libs/mesa-9.0.0"
test_file2_path = os.path.join(path_to_data, test_filename2)
pool = None

def simple_test():
	global pool
	global test_file1_path
	gentoo_rec.trust_feature_declaration = False
	print("Translated SPL:")
	spl = gentoo_rec.load_file_egencache(test_file1_path)
	print("===============")
	print(json.dumps(spl, sort_keys=True, indent=4, separators=(',', ': ')))
	print("===============")
	print("Translated AST:")
	spl_name, local_ast, combined_ast = gentoo_rec.parse_spl(spl)
	print("===============")
	print(json.dumps({'name': spl_name, 'local': local_ast, 'combined': combined_ast}, sort_keys=True, indent=4, separators=(',', ': ')))
	print("===============")
	gentoo_rec.mspl = [spl]
	gentoo_rec.asts = [(spl_name, local_ast, combined_ast)]
	print("Name Mapping:")
	gentoo_rec.generate_name_mappings(pool)
	print("===============")
	print(json.dumps({'map_name_id': gentoo_rec.map_name_id, 'map_id_name': gentoo_rec.map_id_name}, sort_keys=True, indent=4, separators=(',', ': ')))
	print("===============")
	print("Dependencies:")
	gentoo_rec.generate_dependencies(pool)
	print("===============")
	print(json.dumps(gentoo_rec.dependencies, sort_keys=True, indent=4, separators=(',', ': ')))
	print("Package Groups:")
	gentoo_rec.generate_package_groups(pool)
	print("===============")
	print(json.dumps(gentoo_rec.package_groups, sort_keys=True, indent=4, separators=(',', ': ')))
	print("===============")

def double_test():
	global pool
	gentoo_rec.mspl = pool.map(gentoo_rec.load_file_egencache, [test_file1_path, test_file2_path])
	gentoo_rec.generate_all_information("tmp/")
	print(json.dumps(gentoo_rec.mspl, sort_keys=True, indent=4, separators=(',', ': ')))

lock = multiprocessing.Lock()
def find_direct_reference():
	global pool
	print("loading repository")
	gentoo_rec.load_repository_egencache(path_to_data)
	print("parsing the asts")
	gentoo_rec.parse_mspl()
	print("generating the dependencies")
	gentoo_rec.generate_dependencies(pool)
	print("analysing links")
	pool.map(__tmp, gentoo_rec.dependencies.iteritems())

def __tmp(k,v):
	global lock
	for dep in v:
		if dep in gentoo_rec.dependencies:
			with lock:
				print(k + " -> " + dep)

if __name__ == "__main__":
	multiprocessing.freeze_support()
	pool = multiprocessing.Pool(5)
	gentoo_rec.available_cores = 5
	find_direct_reference()