
#######################################
# This file computes several characteristics of the portage graph
#######################################

import db
import graph

import hyportage_constraint_ast
import hyportage_data
import utils


statistics = {}


######################################################################
# FEATURES
######################################################################


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
			use_flag_size = len(hyportage_data.spl_get_iuses_default(spl))
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


######################################################################
# DEPENDENCIES
######################################################################


class GETDependenciesVisitor(hyportage_constraint_ast.ASTVisitor):
	def __init__(self):
		super(hyportage_constraint_ast.ASTVisitor, self).__init__()
		self.res = {}
		self.guarded = False

	def visitDependCONDITION(self, ctx):
		self.guarded = True
		map(self.visitCondition, ctx['els'])
		self.guarded = False

	def visitDependSIMPLE(self, ctx):
		pattern = ctx['atom']
		if self.res.get(pattern, True):
			self.res[pattern] = self.guarded

	def visitSPL(self, spl):
		self.visitDepend(spl.fm_combined)
		res = self.res
		self.res = {}
		return res




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



######################################################################
# PATTERNS (ABSTRACT SPL)
######################################################################


def statistics_pattern(filter_function=db.filter_function_simple):
	utils.phase_start("Computing the Pattern Core Statistics.")
	pattern_number = 0
	pattern_usage = {}
	pattern_usage_max = 0
	for pattern_element in db.flat_pattern_repository.itervalues():
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
	for pattern_element in db.flat_pattern_repository.itervalues():
		if filter_function(pattern_element):
			pattern_abstraction_size = len(pattern_element.get_spls(db.mspl, db.spl_groups))
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
	global statistics
	statistics['patterns'] = res
	utils.phase_end("Computation Completed")


######################################################################
# CYCLES
######################################################################

def statistics_graph(filter_function=db.filter_function_simple):
	utils.phase_start("Computing the Graph Core Statistics.")
	graph_mspl, spl_nodes = graph.get_graph_mspl(filter_function)
	visited = graph_mspl.getBooleanProperty("visited")

	for n in graph_mspl.getNodes():
		visited.setNodeValue(n, False)

	cycles = []
	for n in graph_mspl.getNodes():
		if not visited.getNodeValue(n):
			visited.setNodeValue(n, True)
			path = [n]
			branches = [graph_mspl.getOutNodes(n)]
			while path:
				try:
					succ = branches[-1].next()
					if succ in path:
						cycles.append(path[:])
					elif not visited.getNodeValue(succ):
						visited.setNodeValue(succ, True)
						path.append( (succ, graph_mspl.getOutNodes(succ)) )
				except StopIteration:
					path.pop()
	res = {
		'cycles': cycles
	}
	global statistics
	statistics['graph'] = res
	utils.phase_end("Computation Completed")

