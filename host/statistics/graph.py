
#######################################
# This file computes several graphs from the hyportage data
#######################################

import hyportage_data
import hyportage_pattern

import db

from tulip import tlp



def label_generator_simple(el):
		return el.name


def get_graph_mspl(filter_function=db.filter_function_simple, label_generator=label_generator_simple):
	graph = tlp.newGraph()
	map = {}
	for spl in db.mspl.itervalues():
		if filter_function(spl):
			node = graph.addNode()
			map[spl] = node
			graph['viewLabel'][node] = label_generator(spl)

	spls = set(map.keys())

	for spl, node in map.iteritems():
		dependency_list = {
			dep
			for pattern in spl.dependencies.iterkeys()
			for dep in hyportage_pattern.pattern_repository_get(db.pattern_repository, pattern).get_spls(db.mspl, db.spl_groups)
		}
		for dep in dependency_list & spls:
			if spl != dep:
				graph.addEdge(map[spl], map[dep])

	return graph


def get_graph_spl_groups(filter_function=db.filter_function_simple, label_generator=label_generator_simple):
	graph = tlp.newGraph()
	map = {}
	for group in db.spl_groups.itervalues():
		if filter_function(group):
			node = graph.addNode()
			map[group] = node
			graph['viewLabel'][node] = label_generator(group)

	groups = set(map.keys())

	for group, node in map.iteritems():
		dependency_list = {
			dep
			for spl in group.references
			for pattern in spl.dependencies.iterkeys()
			for dep in hyportage_pattern.pattern_repository_get(db.pattern_repository, pattern).get_spls(db.mspl, db.spl_groups)
		}
		group_dependency_list = {db.spl_groups[hyportage_data.spl_get_group_name(spl)] for spl in dependency_list}
		for dep in group_dependency_list & groups:
			if group != dep:
				graph.addEdge(map[group], map[dep])

	return graph



