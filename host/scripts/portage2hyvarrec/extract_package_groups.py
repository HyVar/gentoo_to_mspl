#!/usr/bin/python

# extracting package groups and adding their ids into the maps

def create_empty_package_groups():
	return {}

def generate_package_group_spl(spl):
	return ( spl['group_name'], spl['versions']['full'], spl['name'])

def update_package_groups(package_groups, element):
	group_name, version, spl_name = element
	if group_name in package_groups:
		package_groups[group_name]['implementations'][version] = spl_name
		package_groups[group_name]['dependencies'].append(spl_name)
	else:
		package_groups[group_name] = {'implementations': {version: spl_name}, 'dependencies': [spl_name]}
		#new_id = utils.new_id()
		#map_name_id["package"][group_name] = new_id
		#map_id_name[new_id] = {'type': 'package', 'name': group_name}

#def generate_package_groups(concurrent_map,mspl,map_name_id,map_id_name):
#	global package_groups
#	information_list = concurrent_map(__gpg_util, mspl)
#	package_groups = {}
#	for group_name, version, spl_name in information_list:
#		if group_name in package_groups:
#			package_groups[group_name]['implementations'][version] = spl_name
#			package_groups[group_name]['dependencies'].extend(spl_name)
#		else:
#			package_groups[group_name] = {'implementations': {version: spl_name}, 'dependencies': [spl_name]}
#			new_id = utils.new_id()
#			map_name_id["package"][group_name] = new_id
#			map_id_name[new_id] = {'type': 'package', 'name': group_name}
#	return package_groups
