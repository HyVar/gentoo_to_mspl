
#######################################
# This file computes several characteristics of the portage graph
#######################################

import math
import sys

import core_data
import hyportage_constraint_ast
import hyportage_data
import utils

import graphs
import host.scripts.utils
from host.scripts import hyportage_db

data = {}


######################################################################
# GENERIC STATISTICS EXTRACTION FUNCTION
######################################################################


def map_base_statistics(value_number, total_size, map_size):
	average = total_size / float(value_number)
	variance = 0
	for key, value in map_size.iteritems():
		tmp = average - key
		tmp = tmp * tmp * len(value)
		variance = variance + tmp
	variance = math.sqrt(variance / value_number)
	return average, variance


def generics(input_iterator, extract_data, extract_key, filter_function=host.scripts.utils.filter_function_simple, store_data_map=False):
	value_number = 0

	map_data = {}
	map_size = {}

	total_size = 0
	max_size = 0
	min_size = sys.maxint

	for element in input_iterator:
		if filter_function(element):
			value_number = value_number + 1

			data = extract_data(element)
			key = extract_key(element)
			size = len(data)
			if store_data_map:
				if data in map_data: map_data[data].add(key)
				else: map_data[data] = {key}
			if size in map_size: map_size[size].add(key)
			else: map_size[size] = {key}

			total_size = total_size + size
			if size > max_size: max_size = size
			if size < min_size: min_size = size

	average, variance = map_base_statistics(value_number, total_size, map_size)

	return {
		'number': value_number,
		'map_data': map_data,
		'map_size': map_size,
		'total_size': total_size,
		'average': average,
		'variance': variance,
		'max_size': max_size,
		'min_size': min_size
	}


def generic_map(input_map, extraction_function, filter_function=host.scripts.utils.filter_function_simple, store_data_map=False):
	return generics(input_map.iteritems(), lambda el: extraction_function(el[1]), lambda el: el[0], filter_function, store_data_map)


def generic_list(input_list, extraction_function, filter_function=host.scripts.utils.filter_function_simple, store_data_map=False):
	return generics(input_list, extraction_function, lambda el: tuple(el), filter_function, store_data_map)


######################################################################
# FEATURES
######################################################################


def features(filter_function=host.scripts.utils.filter_function_simple):
	utils.phase_start("Computing the USE Flags Core Statistics.")

	required = sum([len(spl.required_iuses) for spl in hyportage_db.mspl.itervalues() if filter_function(spl)])
	local = sum([len(spl.iuses_default) for spl in hyportage_db.mspl.itervalues() if filter_function(spl)])

	global data
	data['features'] = generic_map(hyportage_db.mspl, hyportage_data.spl_get_iuses_full, filter_function)
	data['features']['average_required'] = required / float(data['features']['number'])
	data['features']['average_local'] = local / float(data['features']['number'])
	utils.phase_end("Computation Completed")


def features_usage(filter_function=host.scripts.utils.filter_function_simple):
	utils.phase_start("Computing the USE Flags Core Statistics.")
	map_features = {}
	for key, value in hyportage_db.mspl.iteritems():
		if filter_function(value):
			for feature in hyportage_data.spl_get_required_iuses(value):
				if feature in map_features: map_features[feature].add(key)
				else: map_features[feature] = {key}

	global data
	data['feature_usage'] = generic_map(map_features, core_data.identity, filter_function)
	data['feature_usage']['map_data'] = map_features
	utils.phase_end("Computation Completed")



"""
def statistics_features(filter_function=db.filter_function_simple):
	utils.phase_start("Computing the USE Flags Core Statistics.")

	features_number = 0
	features_max = 0
	features_min = 100
	spl_min = []
	spl_max = []
	spl_number = 0
	for spl in db.mspl.itervalues():
		if filter_function(spl):
			spl_number = spl_number + 1
			use_flag_size = len(hyportage_data.spl_get_required_iuses(spl))
			if use_flag_size < features_min:
				features_min = use_flag_size
				spl_min = [spl.name]
			elif use_flag_size == features_min: spl_min.append(spl.name)
			if use_flag_size > features_max:
				features_max = use_flag_size
				spl_max = [spl.name]
			elif use_flag_size == features_max: spl_max.append(spl.name)
			features_number = features_number + use_flag_size
	res = {
		'min': features_min,
		'min_spl_list': sorted(spl_min),
		'max': features_max,
		'max_spl_list': sorted(spl_max),
		'number': features_number,
		'spl_number': spl_number,
		'average': features_number / spl_number
	}
	global statistics
	statistics['features'] = res
	utils.phase_end("Computation Completed")
"""

######################################################################
# DEPENDENCIES
######################################################################


class GETGuardedDependenciesVisitor(hyportage_constraint_ast.ASTVisitor):
	def __init__(self):
		super(hyportage_constraint_ast.ASTVisitor, self).__init__()
		self.res = {}
		self.guards = 0

	def visitDependCONDITION(self, ctx):
		self.guards = self.guards + 1
		map(self.visitDependEL, ctx['els'])
		self.guards = self.guards - 1

	def visitDependSIMPLE(self, ctx):
		pattern = ctx['atom']
		if pattern in self.res:
			if self.guards == 0: self.res[pattern]['guarded'] = False
			if "selection" in ctx: self.res[pattern]['selects'] = True
		else: self.res[pattern] = {'guarded': self.guards > 0, 'selects': "selection" in ctx}

	def visitSPL(self, spl):
		self.visitDepend(spl.fm_combined)
		res = self.res
		self.res = {}
		self.guards = 0
		return res


def dependencies(filter_function=host.scripts.utils.filter_function_simple):
	utils.phase_start("Computing the Dependencies Statistics.")
	visitor = GETGuardedDependenciesVisitor()
	local_map = {spl.name: visitor.visitSPL(spl) for spl in hyportage_db.mspl.itervalues()}
	def extraction_function_all(data): return data.keys()
	def extraction_function_guarded(data): return {pattern for pattern in data.iterkeys() if data[pattern]['guarded']}
	def extraction_function_selects(data): return {pattern for pattern in data.iterkeys() if data[pattern]['selects']}

	global data
	data['dependencies_all'] = generic_map(local_map, extraction_function_all, filter_function)
	data['dependencies_guarded'] = generic_map(local_map, extraction_function_guarded, filter_function)
	data['dependencies_selects'] = generic_map(local_map, extraction_function_selects, filter_function)
	utils.phase_end("Computation Completed")


def lone_packages(filter_function=host.scripts.utils.filter_function_simple):
	referenced_spls = {
		spl
		for el in hyportage_db.flat_pattern_repository.itervalues()
		for spl in el.__generate_matched_spls(hyportage_db.mspl, hyportage_db.spl_groups)
	}

	spls = filter(filter_function, hyportage_db.mspl.itervalues())
	spls = filter(lambda spl: len(spl.dependencies) == 0, spls)
	spls = filter(lambda spl: spl not in referenced_spls, spls)

	global data
	data['lone_packages'] = spls



"""
def statistics_dependencies(filter_function=db.filter_function_simple):
	utils.phase_start("Computing the Dependencies Core Statistics.")
	dependencies_number = 0
	dependencies_max = 0
	dependencies_min = 100
	dependencies_guarded_number = 0
	dependencies_guarded_max = 0
	dependencies_guarded_min = 100
	spl_number = 0
	spl_max = []
	spl_min = []
	spl_guarded_number = 0
	spl_guarded_max = []
	spl_guarded_min = []

	visitor = GETDependenciesVisitor()
	for spl in db.mspl.itervalues():
		if filter_function(spl):
			spl_number = spl_number + 1
			deps = visitor.visitSPL(spl)
			#print("  " + spl.name + ": " + str(deps))
			dependencies_size = len(deps)
			if dependencies_size < dependencies_min:
				dependencies_min = dependencies_size
				spl_min = [spl.name]
			elif dependencies_size == dependencies_min:
				spl_min.append(spl.name)
			if dependencies_size > dependencies_max:
				dependencies_max = dependencies_size
				spl_max = [spl.name]
			elif dependencies_size == dependencies_max:
				spl_max.append(spl.name)
			dependencies_number = dependencies_number + dependencies_size

			deps_guarded = {k for k, v in deps.iteritems() if v}
			dependencies_guarded_size = len(deps_guarded)
			if dependencies_guarded_size < dependencies_guarded_min:
				dependencies_guarded_min = dependencies_guarded_size
				spl_guarded_min = [spl.name]
			elif dependencies_guarded_size == dependencies_guarded_min:
				spl_guarded_min.append(spl.name)
			if dependencies_guarded_size > dependencies_guarded_max:
				dependencies_max = dependencies_guarded_size
				dependencies_guarded_max = [spl.name]
			elif dependencies_guarded_size == dependencies_guarded_max:
				spl_guarded_max.append(spl.name)
			dependencies_guarded_number = dependencies_guarded_number + dependencies_guarded_size
			if dependencies_guarded_size > 0: spl_guarded_number = spl_guarded_number + 1

	res = {
		'min': dependencies_min,
		'min_spl_list': sorted(spl_min),
		'max': dependencies_max,
		'max_spl_list': sorted(spl_max),
		'number': dependencies_number,
		'spl_number': spl_number,
		'average': dependencies_number / spl_number,
		'guarded_min': dependencies_guarded_min,
		'guarded_min_spl_list': sorted(spl_guarded_min),
		'guarded_max': dependencies_guarded_max,
		'guarded_max_spl_list': sorted(spl_guarded_max),
		'guarded_number': dependencies_guarded_number,
		'guarded_spl_number': spl_guarded_number,
		'guarded_average': dependencies_guarded_number / spl_guarded_number
	}
	global statistics
	statistics['dependencies'] = res
	utils.phase_end("Computation Completed")
"""


######################################################################
# PATTERNS (ABSTRACT SPL)
######################################################################


def pattern_refinement(filter_function=host.scripts.utils.filter_function_simple):
	utils.phase_start("Computing the Pattern (refinement) Statistics.")
	def extraction_function(element): return element.matched_spls(hyportage_db.mspl, hyportage_db.spl_groups)
	global data
	data['pattern_refinement'] = generic_map(hyportage_db.flat_pattern_repository, extraction_function, filter_function)
	utils.phase_end("Computation Completed")




def statistics_pattern(filter_function=host.scripts.utils.filter_function_simple):
	utils.phase_start("Computing the Pattern Core Statistics.")
	pattern_number = 0
	pattern_usage = {}
	pattern_usage_max = 0
	for pattern_element in hyportage_db.flat_pattern_repository.itervalues():
		if filter_function(pattern_element):
			pattern_number = pattern_number + 1
			size = len(pattern_element.containing_spl)
			if pattern_usage_max < size:
				pattern_usage_max = size
			if size in pattern_usage:
				pattern_usage[size].extend(pattern_element)
			else: pattern_usage[size] = [pattern_element]
	pattern_abstraction_number = 0
	pattern_abstraction_max = [0, []]
	pattern_abstraction_min = [100, []]
	for pattern_element in hyportage_db.flat_pattern_repository.itervalues():
		if filter_function(pattern_element):
			pattern_abstraction_size = len(pattern_element.matched_spls(hyportage_db.mspl, hyportage_db.spl_groups))
			if pattern_abstraction_size < pattern_abstraction_min[0]:
				pattern_abstraction_min[0] = pattern_abstraction_size
				pattern_abstraction_min[1] = [pattern_element]
			elif pattern_abstraction_size == pattern_abstraction_min[0]:
				pattern_abstraction_min[1].append(pattern_element)
			if pattern_abstraction_size > pattern_abstraction_max[0]:
				pattern_abstraction_max[0] = pattern_abstraction_size
				pattern_abstraction_max[1] = [pattern_element]
			elif pattern_abstraction_size == pattern_abstraction_max[0]:
				pattern_abstraction_max[1].append(pattern_element)
			pattern_abstraction_number = pattern_abstraction_number + pattern_abstraction_size

	res = {
		'number': pattern_number,
		'usage': pattern_usage,
		'usage_max': pattern_usage_max,
		'usage_average': pattern_usage_max / pattern_number,
		'total_abstraction_number': pattern_abstraction_number,
		'abstraction_min': pattern_abstraction_min[0],
		'abstraction_min_list': pattern_abstraction_min[1],
		'abstraction_max': pattern_abstraction_max[0],
		'abstraction_max_list': pattern_abstraction_max[1]
	}
	global data
	data['patterns'] = res
	utils.phase_end("Computation Completed")


######################################################################
# CYCLES
######################################################################

def graph(filter_function=host.scripts.utils.filter_function_simple):
	utils.phase_start("Computing the Graph Core Statistics.")
	graph_mspl, spl_nodes = graphs.mspl(filter_function, keep_self_loop=True)
	nodes_spl = {node: spl for spl, node in spl_nodes.iteritems()}
	visited = graph_mspl.getBooleanProperty("visited")

	for n in graph_mspl.getNodes():
		visited.setNodeValue(n, False)

	shairplay_len = sys.maxint

	cycles = []
	for n in graph_mspl.getNodes():
		if not visited.getNodeValue(n):
			visited.setNodeValue(n, True)
			path = [n]
			branches = [graph_mspl.getOutNodes(n)]
			if "shairplay" in nodes_spl[n].name: shairplay_len = 1
			while path:
				if len(path) >= shairplay_len: print(str([nodes_spl[node].name for node in path]))
				if branches[-1].hasNext():
					succ = branches[-1].next()
					if len(path) >= shairplay_len: print("  found: " + nodes_spl[succ].name)
					if succ in path:
						if len(path) >= shairplay_len: print("  loop found: " + str([nodes_spl[node].name for node in path[path.index(succ):]]))
						cycles.append([nodes_spl[node].name for node in path[path.index(succ):]])
					elif not visited.getNodeValue(succ):
						visited.setNodeValue(succ, True)
						path.append(succ)
						branches.append(graph_mspl.getOutNodes(succ))
						if "shairplay" in nodes_spl[succ].name: shairplay_len = len(path)
				else:
					path.pop()
					branches.pop()
					if len(path) < shairplay_len: shairplay_len = sys.maxint

	res = generic_map({tuple(v): v for v in cycles}, core_data.identity, host.scripts.utils.filter_function_simple)
	res['cycles'] = cycles
	global data
	data['graph'] = res
	utils.phase_end("Computation Completed")

