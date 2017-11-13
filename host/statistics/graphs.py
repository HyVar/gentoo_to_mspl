
#######################################
# This file computes several graphs from the hyportage data
#######################################

import core_data
import hyportage_data
import hyportage_pattern

import db

from tulip import tlp



def label_generator_simple(el):
		return el.name


######################################################################
# GENERATORS
######################################################################


def mspl(filter_function=db.filter_function_simple, label_generator=label_generator_simple, keep_self_loop=False):
	graph = tlp.newGraph()
	spl_nodes = {}
	for spl in db.mspl.itervalues():
		if filter_function(spl):
			node = graph.addNode()
			spl_nodes[spl] = node
			graph['viewLabel'][node] = label_generator(spl)

	spls = set(spl_nodes.keys())

	for spl, node in spl_nodes.iteritems():
		dependency_list = {
			dep
			for pattern in spl.dependencies.iterkeys()
			for dep in hyportage_pattern.pattern_repository_get(db.pattern_repository, pattern).get_spls(db.mspl, db.spl_groups)
		}
		for dep in dependency_list & spls:
			if keep_self_loop or (spl != dep):
				graph.addEdge(spl_nodes[spl], spl_nodes[dep])

	return graph, spl_nodes



def mspl_full(
		filter_spl=db.filter_function_simple, filter_pattern=db.filter_function_simple,
		label_spl=label_generator_simple, label_pattern=core_data.pattern_to_atom):
	graph = tlp.newGraph()
	spl_nodes = {}
	pattern_nodes = {}

	for spl in db.mspl.itervalues():
		if filter_spl(spl):
			node = graph.addNode()
			spl_nodes[spl] = node
			graph['viewLabel'][node] = label_spl(spl)

	for pattern in db.flat_pattern_repository.iterkeys():
		if filter_pattern(pattern):
			node = graph.addNode()
			pattern_nodes[pattern] = node
			graph['viewLabel'][node] = label_pattern(pattern)

	spls = set(spl_nodes.keys())
	patterns = set(pattern_nodes.keys())

	for spl, node in spl_nodes.iteritems():
		for pattern in spl.dependencies.iterkeys():
			if pattern in patterns:
				graph.addEdge(node, pattern_nodes[pattern])

	for pattern, node in pattern_nodes.iteritems():
		for spl in db.flat_pattern_repository[pattern].get_spls(db.mspl, db.spl_groups):
			if spl in spls:
				graph.addEdge(node, spl_nodes[spl])

	return graph, spl_nodes, pattern_nodes




def spl_groups(filter_function=db.filter_function_simple, label_generator=label_generator_simple, keep_self_loop=False):
	graph = tlp.newGraph()
	group_nodes = {}
	for group in db.spl_groups.itervalues():
		if filter_function(group):
			node = graph.addNode()
			group_nodes[group] = node
			graph['viewLabel'][node] = label_generator(group)

	groups = set(group_nodes.keys())

	for group, node in group_nodes.iteritems():
		dependency_list = {
			dep
			for spl in group.references
			for pattern in spl.dependencies.iterkeys()
			for dep in hyportage_pattern.pattern_repository_get(db.pattern_repository, pattern).get_spls(db.mspl, db.spl_groups)
		}
		group_dependency_list = {db.spl_groups[hyportage_data.spl_get_group_name(spl)] for spl in dependency_list}
		for dep in group_dependency_list & groups:
			if keep_self_loop or (group != dep):
				graph.addEdge(group_nodes[group], group_nodes[dep])

	return graph, group_nodes


######################################################################
# ANALYSIS
######################################################################


def density(graph):
	number_nodes = len(graph.nodes())
	number_edges = len(graph.edges())
	return number_edges / float(number_nodes * (number_nodes - 1))


class SSCComputation(object):  # Tarjan Algorithm
	def __init__(self):
		self.graph = None
		self.sccs = None
		self.stack = None
		self.index = None
		self.current_node = None
		self.path = None
		self.branches = None

	def register_node(self, n):
		self.graph['index'][n] = self.index
		self.graph['lowlink'][n] = self.index
		self.graph['onstack'][n] = True
		self.index = self.index + 1
		self.stack.append(n)

		self.current_node = n
		self.path.append(n)
		self.branches.append(self.graph.getOutNodes(n))

	def strongly_connected_components_rec(self, graph, n):
		graph['index'][n] = self.index
		graph['lowlink'][n] = self.index
		graph['onstack'][n] = True
		self.index = self.index + 1
		self.stack.append(n)
		for succ in graph.getOutNodes(n):
			if graph['index'][succ] < 0:
				self.strongly_connected_components_rec(graph, succ)
				graph['lowlink'][n] = min(graph['lowlink'][n], graph['lowlink'][succ])
			elif graph['onstack'][succ]:
				graph['lowlink'][n] = min(graph['lowlink'][n], graph['index'][succ])
		if graph['index'][n] == graph['lowlink'][n]:
			scc = []
			while True:
				node = self.stack.pop()
				scc.append(node)
				graph['onstack'][node] = False
				if node == n: break
			self.sccs.append(scc)

	def strongly_connected_components_it(self):
		while self.branches:
			if self.branches[-1].hasNext():
				succ = self.branches[-1].next()
				if self.graph['index'][succ] < 0:
					self.register_node(succ)
				elif self.graph['onstack'][succ]:
					self.graph['lowlink'][self.current_node] = min(self.graph['lowlink'][self.current_node], self.graph['index'][succ])

			else:
				if self.graph['index'][self.current_node] == self.graph['lowlink'][self.current_node]:
					scc = []
					while True:
						node = self.stack.pop()
						scc.append(node)
						self.graph['onstack'][node] = False
						if node == self.current_node: break
					self.sccs.append(scc)
				self.branches.pop()
				self.path.pop()
				self.current_node = self.path[-1] if self.path else None


	def computation(self, graph):
		self.graph = graph
		self.sccs = []
		self.stack = []
		self.index = 0
		for n in graph.getNodes(): graph['index'][n] = -1
		for n in graph.getNodes():
			if graph['index'][n] < 0:
				self.path = []
				self.branches = []
				self.register_node(n)
				self.strongly_connected_components_it()
		self.graph.delLocalProperty("index")
		self.graph.delLocalProperty("onstack")
		self.graph.delLocalProperty("lowlink")
		return self.sccs


def strongly_connected_components(graph):
	return SSCComputation().computation(graph)


def loops(graph):
	graph_loops = []
	for n in graph.getNodes(): graph['visited'][n] = False
	for n in graph.getNodes():
		if not graph['visited'][n]:
			graph['visited'][n] = True
			path = [n]
			branches = [graph.getOutNodes(n)]
			while branches:
				if branches[-1].hasNext():
					succ = branches[-1].next()
					if succ in path:
						graph_loops.append(path[path.index(succ):])
					elif not graph['visited'][succ]:
						graph['visited'][succ] = True
						path.append(succ)
						branches.append(graph.getOutNodes(succ))
				else:
					path.pop()
					branches.pop()
	return graph_loops


def forest(graph, roots=()):
	res = tlp.newGraph()
	equiv = {}
	for node in graph.getNodes():
		new_node = res.addNode()
		equiv[node] = new_node

	for n in graph.getNodes(): graph['visited'][n] = False

	def visit(graph, n):
		if not graph['visited'][n]:
			graph['visited'][n] = True
			path = [n]
			branches = [graph.getOutNodes(n)]
			while branches:
				if branches[-1].hasNext():
					succ = branches[-1].next()
					if not graph['visited'][succ]:
						res.addEdge(equiv[path[-1]], equiv[succ])
						graph['visited'][succ] = True
						path.append(succ)
						branches.append(graph.getOutNodes(succ))
				else:
					path.pop()
					branches.pop()

	for n in roots: visit(graph, n)
	for n in graph.getNodes(): visit(graph, n)
	return res, equiv


def tree(graph, root):
	res = tlp.newGraph()
	equiv = {}

	for n in graph.getNodes(): graph['visited'][n] = False

	new_node = res.addNode()
	equiv[root] = new_node
	graph['visited'][root] = True
	path = [new_node]
	branches = [graph.getOutNodes(root)]
	while branches:
		if branches[-1].hasNext():
			succ = branches[-1].next()
			if not graph['visited'][succ]:
				new_node = res.addNode()
				equiv[succ] = new_node
				res.addEdge(path[-1], new_node)
				graph['visited'][succ] = True
				path.append(new_node)
				branches.append(graph.getOutNodes(succ))
		else:
			path.pop()
			branches.pop()
	return res, equiv


def topological_order(forest):
	res = []

	for n in forest.getNodes(): forest['visited'][n] = False

	for n in forest.getNodes():
		if not forest['visited'][n]:
			forest['visited'][n] = True
			path = [n]
			branches = [forest.getOutNodes(n)]
			while branches:
				if branches[-1].hasNext():
					succ = branches[-1].next()
					if not forest['visited'][succ]:
						forest['visited'][succ] = True
						path.append(succ)
						branches.append(forest.getOutNodes(succ))
				else:
					res.append(path.pop())
					branches.pop()
	return res



def set_node_size(graph, scale=1):
	sccs = strongly_connected_components(graph)
	graph_forest, equiv = forest(graph)
	inv_equiv = {v: k for k, v in equiv.iteritems()}

	order = topological_order(graph_forest)

	# base values
	for scc in sccs:
		size = len(scc)
		for node in scc: graph['size'][node] = size

	# cummulative values
	for n in graph_forest.getNodes(): graph_forest['size'][n] = 1
	for node in order:
		size = sum([graph_forest['size'][n] for n in graph_forest.getOutNodes(node)], 0)
		graph_forest['size'][node] = graph_forest['size'][node] + size

	# combine the values
	for n in graph.getNodes(): graph['size'][n] = (graph['size'][n] + graph_forest['size'][equiv[n]] - 1) * scale


######################################################################
# TEST
######################################################################

def set_layout(graph, root):
	t, equiv = tree(graph, root)
	#inv_equiv = {v: k for k, v in equiv.iteritems()}

	# 1. clean the graph
	t_nodes = t.nodes()
	to_delete = { n for n in graph.getNodes() if n not in equiv}
	for n in to_delete: graph.delNode(n)

	# 2. compute the layout
	layout = "Tree Radial"
	params = tlp.getDefaultPluginParameters(layout, t)
	t.applyLayoutAlgorithm(layout, params)
	for n in graph.getNodes(): graph['viewLayout'][n] = t['viewLayout'][n]

	# 3. compute the size
	set_node_size(graph, scale=4)








