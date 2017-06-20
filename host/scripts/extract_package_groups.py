#!/usr/bin/python

# extracting package groups and adding their ids into the maps


def from_mspl_list(concurrent_map, raw_mspl):
	package_groups = {}
	for spl in raw_mspl:
		group_name, version, spl_name = (spl['group_name'], spl['versions']['full'], spl['name'])
		if group_name in package_groups:
			package_groups[group_name]['implementations'][version] = spl_name
			package_groups[group_name]['dependencies'].append(spl_name)
			package_groups[group_name]['reference'].append(spl)
		else:
			package_groups[group_name] = {'implementations': {version: spl_name}, 'dependencies': [spl_name], 'reference': [spl] }
	return package_groups



def clean(concurrent_map, package_groups):
	concurrent_map(clean_package_group, package_groups.values())
def clean_package_group(package_group):
	del package_group['reference']


