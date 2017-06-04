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
test_filename = "dev-games/ogre-1.9.0-r1"
test_file_path = os.path.join(path_to_data, test_filename)
pool = None

def single_test():
	global pool
	global test_file_path
	gentoo_rec.trust_feature_declaration = False
	print("Translated SPL:")
	spl = gentoo_rec.load_file_egencache(test_file_path)
	print("===============")
	print(json.dumps(spl, sort_keys=True, indent=4, separators=(',', ': ')))
	print("===============")
	print("Translated AST:")
	spl_name, local_ast, combined_ast = gentoo_rec.parse_spl(spl)
	print("===============")
	print(json.dumps({'name': spl_name, 'local': local_ast, 'combined': combined_ast}, sort_keys=True, indent=4, separators=(',', ': ')))
	print("===============")
	print("Generated Information:")
	gentoo_rec.mspl = [spl]
	gentoo_rec.asts = [(spl_name, local_ast, combined_ast)]
	print("  ...")
	gentoo_rec.generate_name_mappings(pool)
	print("  ...")
	gentoo_rec.generate_dependencies(pool)
	print("  ...")
	gentoo_rec.generate_package_groups(pool)
	print("===============")

if __name__ == "__main__":
	multiprocessing.freeze_support()
	pool = multiprocessing.Pool(2)
	single_test()