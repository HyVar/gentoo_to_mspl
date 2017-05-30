#!/usr/bin/python


"""
utils.py: this file contains utility functions and classes for translating the gentoo's ebuild in well-formed Dependent SPL and processing them
"""

__author__     = "Michael Lienhardt"
__copyright__  = "Copyright 2017, Michael Lienhardt"
__licence__    = "GPLv3"
__version__    = "0.1"
__maintainer__ = "Michael Lienhardt"
__email__      = "michael.lienhardt@laposte.net"
__status__     = "Prototype"

import os
import subprocess
import re
import json
import string
import networkx

from antlr4 import *
from antlr4.error.ErrorListener import ErrorListener
from grammar.DepGrammarLexer import DepGrammarLexer
from grammar.DepGrammarParser import DepGrammarParser
from grammar.DepGrammarVisitor import DepGrammarVisitor

import networkx


#####################################################################################
### GLOBAL VARIABLE
#####################################################################################

__main_feature__ = "__main__"   # constant name of the root feature of every SPL

#data_raw = {}                   # dictionary loaded from a repository. Shape = { package => { 'implementations': { version => implementation } , 'versions': list_of_versions, 'slots': list_of_slots, 'subslots': list_of_subslots } }
#data_spl = {}                   # dictionary of cleaned data. Shape = { spl => {} }
#data_catalog = { 'names': set(), 'names_used': set(), 'versions': set(), 'features': set(), 'slots': set(), 'subslots': set() }               # dictionary of name and number replacement
#data_graph = networkx.DiGraph() # graph of the SPLs

######################################################################
### FUNCTIONS TO LOAD A GENTOO FILE
######################################################################

# configuraton variables
path_portage_implementation = os.path.abspath("../resources/src-portage")
path_ebuild_loader = "source " + os.path.join(path_portage_implementation, "bin", "ebuild.sh")
path_log_file = os.path.abspath("../resources/log.txt")
path_log_file_id = "4"

build_dir="/var/tmp/portage"
eprefix=""

__my_env__ = os.environ.copy()

def structure_filename(filename):
	filename_split = filename.split("-")
	tmp = filename_split[-1]
	if tmp.startswith("r"):
		revision = tmp
		version = filename_split[-2]
		del filename_split[-2:]
		version_all = version + "-" + revision
	else:
		revision = "r0"
		version = filename_split[-1]
		del filename_split[-1]
		version_all = version
	package = "-".join(filename_split)
	return (package, version_all, version, revision)

def construct_data(names, versions, environment, slots, features, fm_local, fm_external, fm_runtime):
	name, name_base, category, package = names
	version_all, version, revision = versions
	environment = environment.split() if environment else ["*"]
	slots = slots.split("/") if slots else [0, 0]
	slot = str(slots[0])
	has_subslot = (len(slots) == 2)
	subslot = (str(slots[1]) if has_subslot else "0")
	features = features.split() if features else []
	features = { (feature[1:] if (feature[0] in ['+', '-']) else feature): {} for feature in features }
	features[__main_feature__] = { 'versions': [str(version_all)], 'version_base': str(version), 'revision': str(revision), 'slots': [slot], 'subslots': [subslot] } 
	fm_local = fm_local if fm_local else "" 	
	fm_external = fm_external if fm_external else "" 	
	fm_runtime = fm_runtime if fm_runtime else ""
	data = { 'name': name, 'name_base': name_base, 'name_package': package, 'name_category': category, 'features': features, 'environment': environment, 'fm': { 'local': fm_local, 'external': fm_external, 'runtime': fm_runtime } }
	return data

###############################

def set_static_ebuild_environ():
	__my_env__['WORKDIR']  = build_dir + "/work"             # Path to the ebuild's root build directory. For example: "${PORTAGE_BUILDDIR}/work".
	__my_env__['T']        = build_dir + "/temp"             # Path to a temporary directory which may be used by the ebuild. For example: "${PORTAGE_BUILDDIR}/temp".
	__my_env__['D']        = build_dir + "/image"            # Path to the temporary install directory. For example: "${PORTAGE_BUILDDIR}/image".
	__my_env__['HOME']     = build_dir + "/homedir"          # Path to a temporary directory for use by any programs invoked by an ebuild that may read or modify the home directory. For example: "${PORTAGE_BUILDDIR}/homedir".
	#os.environ['A']        = # All the source files for the package (excluding those which are not available because of USE flags).
	#os.environ['ROOT']     = # The absolute path to the root directory into which the package is to be merged. Only allowed in pkg_* phases. See ROOT
	#os.environ['DISTDIR']  = # Contains the path to the directory where all the files fetched for the package are stored.
	__my_env__['EPREFIX']  = eprefix                         # The normalised offset-prefix path of an offset installation.
	__my_env__['ED']       = build_dir + "/image/" + eprefix # Shorthand for ${D%/}${EPREFIX}/.
	#os.environ['EROOT']    = # Shorthand for ${ROOT%/}${EPREFIX}/. 
	#
	__my_env__['EAPI']              = "6" 
	__my_env__['EBUILD_PHASE']      = "depend"
	__my_env__['PORTAGE_REPO_NAME'] = "portage"
	#
	__my_env__['IMPLEMENTATION_DIR']       = path_portage_implementation
	__my_env__['PORTAGE_BIN_PATH']         = os.path.join(path_portage_implementation, "bin")   # where all the .sh files are defined
	__my_env__['PORTAGE_PYM_PATH']         = os.path.join(path_portage_implementation, "pym")   # where all the .py files are defined
	__my_env__['PORTAGE_ECLASS_LOCATIONS'] = os.path.abspath("../resources/gentoo-master")
	__my_env__['PORTAGE_BUILDDIR']         = build_dir
	__my_env__['PORTAGE_TMPDIR']           = build_dir
	__my_env__['BUILD_PREFIX']             = os.path.join(build_dir, "portage")
	__my_env__['PKG_TMPDIR']               = os.path.join(build_dir, "portage", "._unmerge_")
	__my_env__['PORTAGE_PIPE_FILENAME']    = path_log_file
	__my_env__['PORTAGE_PIPE_FD']          = path_log_file_id


def load_features_equery(catpackage):
	equery_output = subprocess.check_output(["bash", "-c", "equery u \"" + catpackage + "\" | cut -c 2-"])
	return equery_output[:-1] # remove last line


def load_file_ebuild(filepath):
	# 1. base information about the ebuild
	path_to_file, filename=os.path.split(filepath)
	path_to_package, package = os.path.split(path_to_file)
	path_to_category, category = os.path.split(path_to_package)
	filename_core = filename[:-7]
	package, version_all, version, revision = structure_filename(filename_core)
	name = category + "/" + filename_core
	name_base = category + "/" + package
	# 2. set the environment variables
	__my_env__['P']        = package + "-" + version     # Package name and version (excluding revision, if any), for example vim-6.3.
	__my_env__['PN']       = package                     # Package name, for example vim.
	__my_env__['PV']       = version                     # Package version (excluding revision, if any), for example 6.3. It should reflect the upstream versioning scheme.
	__my_env__['PR']       = revision                    # Package revision, or r0 if no revision exists.
	__my_env__['PVR']      = version_all                 # Package version and revision (if any), for example 6.3, 6.3-r1.
	__my_env__['PF']       = package + "-" + version_all # Full package name, ${PN}-${PVR}, for example vim-6.3-r1.
	__my_env__['CATEGORY'] = category                    # Package's category, for example app-editors.
	__my_env__['FILESDIR'] = path_to_package + "/files"  # Path to the ebuild's files/ directory, commonly used for small patches and files. For example: "${PORTDIR}/${CATEGORY}/${PN}/files".
	# 3. load the package
	__my_env__['EBUILD'] = filepath
	output = subprocess.check_output(["bash", "-himBH", "load_ebuild.sh"], env=__my_env__) # not possible to put the option -c, because the set of options is used in ebuild.sh for something else...
	#output = subprocess.check_output(["bash", "-c", "exec " + path_log_file_id + "<>" + path_log_file + " && " + path_ebuild_loader + " ; echo \"KEYWORDS=${KEYWORDS}\" ; echo \"SLOT=${SLOT}\" ; echo \"REQUIRED_USE=${REQUIRED_USE//$'\n'/}\" | tr '\t' ' ' ; echo \"DEPEND=${DEPEND//$'\n'/}\" | tr '\t' ' ' ; echo \"RDEPEND=${RDEPEND//$'\n'/}\" | tr '\t' ' ' "], env=__my_env__)
	output = output.split("\n")
	output.pop()
	data_tmp = {}
	for line in output:
		array = string.split(line, "=", 1)
		data_tmp[array[0]] = array[1]
	# 4. return the data
	names = (name, name_base, category, package)
	versions = (version_all, version, revision)
        data = construct_data(
			names,
			versions,
			data_tmp.get('KEYWORDS'),
			data_tmp.get('SLOT'),
			data_tmp.get('IUSE'),
			data_tmp.get('REQUIRED_USE'),
			data_tmp.get('DEPEND'),
			data_tmp.get('RDEPEND'))
	return data


def load_file_egencache(filepath):
	# 1. base information from the file name
	path_to_file, filename=os.path.split(filepath)
	path_to_category, category = os.path.split(path_to_file)
	package, version_all, version, revision = structure_filename(filename)
	name = category + "/" + filename
	name_base = category + "/" + package
	# 2. informations from the file content
	data_tmp = {}
	f = open(filepath, 'r')
	for line in f:
		array = string.split(line, "=", 1)
		data_tmp[array[0]] = array[1][:-1] # remove the \n at the end of the line
	f.close()
	# 3. return the data
	names = (name, name_base, category, package)
	versions = (version_all, version, revision)
        data = construct_data(
			names,
			versions,
			data_tmp.get('KEYWORDS'),
			data_tmp.get('SLOT'),
			data_tmp.get('IUSE'),
			data_tmp.get('REQUIRED_USE'),
			data_tmp.get('DEPEND'),
			data_tmp.get('RDEPEND'))
	return data


#####################################################################################
### FUNCTIONS TO LOAD AN MSPL without explicit dependencies FROM A REPOSITORY 
#####################################################################################

# load a repository
def load_repository(file_filter, file_loader, path):
	# 1. fill up data_raw
	data = {}
	for root, dirs, filenames in os.walk(path):
		for filename in filenames:
			filename = os.path.join(root, filename)
			if file_filter(filename):
				#print("loading file \"" + filename + "\"")
				implementation = file_loader(filename)
				data[implementation['name']] = implementation
	return data

def load_from_ebuild(path):
	set_static_ebuild_environ()
	return load_repository(lambda filename: (filename.endswith(".ebuild") and filename != os.path.join(path, "skel.ebuild")), load_file_ebuild, path)

def load_from_egencache(path):
	return load_repository(os.path.isfile, load_file_egencache, path)

# complete the repository with the entries about packages
def generate_packages(data_implementation):
	data_package = {}
	# 1. create the basic structure for the package
	for implementation in data_implementation.values():
		name = implementation['name_base']
		implementation_name = implementation['name']
		package = data_package.get(name)
		if package == None:
			package = { 'name': name, 'name_package': implementation['name_package'], 'name_category': implementation['name_category'],
					'features': {}, 'environment': set(), 'implementations': {}, 'slots': {} }
			data_package[name] = package
		package['features'].update({ f: {} for f in implementation['features'].keys() })
		package['environment'].update(implementation['environment'])
		package['implementations'][implementation['features'][__main_feature__]['versions'][0]] = implementation_name
		implementation_slot = implementation['features'][__main_feature__]['slots'][0]
		slot = package['slots'].get(implementation_slot)
		if slot == None:
			slot = {}
			package['slots'][implementation_slot] = slot
		implementation_subslot = implementation['features'][__main_feature__]['subslots'][0]
		subslot = slot.get(implementation_subslot)
		if subslot == None:
			subslot = set()
			slot[implementation_subslot] = subslot
		subslot.add(implementation_name)
	# 2. complete the structure with a feature model, and translates all set in list (for json)
	for package in data_package.values():
		package['features'][__main_feature__] = { 'versions': package['implementations'].keys(), 
			'slots': package['slots'].keys(), 'subslots': list(set([subslot for mapping in package['slots'].values() for subslot in mapping.keys()])) }
		package['environment']     = list(package['environment'])
		constraint_impl, constraint_conflict = generate_constraint_slots(package['slots'])
		constraint_version = generate_constraint_version(package['implementations'])
		package['fm'] = { 'local': "", 'external': " ".join([constraint_impl, constraint_conflict, constraint_version]), 'runtime': "" }
		#package['dependencies'] = package['implementations'].values() # is computed during the dependencies extraction
		del package['slots']
	# 3. return the computed value
	return data_package

def generate_constraint_slots(slots):
	impl = {}
	conflict = ""
	for slot, subslots in slots.iteritems():
		tmp = {}
		for subslot, elements in subslots.iteritems():
			tmp[slot] = " ".join([ "=" + element for element in elements ])
		impl[slot] = " ".join([__main_feature__ + "{ subslot=" + subslot + " }? ( ||(" + elements_str + "))" for subslot, elements_str in tmp.iteritems()])
		conflict =  conflict + " " + " ".join("?? (" + elements_str + ")" for elements_str in tmp.values())
	return (" ".join([__main_feature__ + "{ slot=" + slot + " }? ( ||(" + elements_str + "))" for slot, elements_str in impl.iteritems()]) , conflict)

def generate_constraint_version(implementations):
	return " ".join([__main_feature__ + "{ versions=" + version + " }? (=" + implementation_name + ")" for version, implementation_name in implementations.iteritems()])	


######################################################################
### FUNCTIONS TO COMPLETE and extract a catalog from AN MSPL
######################################################################

"""
creates a dictionary package -> { 'implementations': list_of_data_from_file, 'versions': list_of_versions, 'slots': list_of_slots, 'subslots': list_of_subslots }
Loading several repositories will combine them :) Useful for loading installed packages
"""

class SPLParser(DepGrammarVisitor, ErrorListener):
	def __init__(self):
		super(DepGrammarVisitor, self).__init__()
		super(ErrorListener, self).__init__()
		# 1. global data
		self.spl = {}                                        # all the spl names declared in the data we parsed
		self.spl_used = set()                                # all the spl names used in the data we parsed
		self.versions = set()                                    # all the versions in the data we parsed
		self.features = set()                                    # all the features in the data we parsed
		self.slots = set()                                       # all the slots in the data we parsed
		self.subslots = set()                                    # all the subslots in the data we parsed
		self.environment = set()
	
	def parser(self, parsed_string):
		self.parsed_string = parsed_string
		lexer = DepGrammarLexer(InputStream(parsed_string))
		lexer._listeners = [ self ]
		parser = DepGrammarParser(CommonTokenStream(lexer))
		parser._listeners = [ self ]
		return parser

	def load_spl(self, spl):
		self.processing = spl['name']
		is_implementation = True if spl.get('name_base') else False
		# 1. update data from local data
		if is_implementation:
			self.versions.update(spl['features'][__main_feature__]['versions'])
			self.features.update(spl['features'].keys())
			self.slots.update(spl['features'][__main_feature__]['slots'])
			self.subslots.update(spl['features'][__main_feature__]['subslots'])
			self.environment.update([ keyword[1:] if keyword.startswith("~") or keyword.startswith("*") else keyword for keyword in spl['environment'] ])
			# 2. update data from constraint
			self.used_features = { 'local': set(), 'external': {} }   # features used in the local constraint
			self.dependencies = set()                                 # set of tuple (version_operator, name, version, has_star, slot, subslot, configured) used in the local constraint
			self.init_dependencies(spl)
			self.current_package = None
			self.stage = 'required_use'
			required = self.parser(spl['fm']['local'])
			required = required.required()
			self.stage = 'depend'
			depend = self.parser(spl['fm']['external'])
			depend = depend.depend()
			self.stage = 'rdepend'
			rdepend = self.parser(spl['fm']['runtime'])
			rdepend = rdepend.depend()
			self.visitRequired(required)
			self.visitDepend(depend)
			self.visitDepend(rdepend)
		else:
			self.used_features = { 'local': set(), 'external': {} }   # features used in the local constraint
			self.dependencies = set()                                 # set of tuple (version_operator, name, version, has_star, slot, subslot, configured) used in the local constraint
			for version, name in spl['implementations'].iteritems():
				self.dependencies.add( ( "=", name, version, False, None, None, True ) )
		# 3. finish up
		self.format_data()
		spl['dependencies'] = list(set([ dep['name'] for dep in self.dependencies ]))
		spl['configures'] = list(set([ dep['name'] for dep in self.dependencies if dep['configured'] ]))

	def load_repository(self, data):
		for spl in data.values():
			self.load_spl(spl)

	def get_catalog(self):
		catalog = {}
		catalog['spl'] = self.spl
		catalog['spl_used'] = list(self.spl_used)
		catalog['versions'] = list(self.versions)
		catalog['features'] = list(self.features)
		catalog['slots'] = list(self.slots)
		catalog['subslots'] = list(self.subslots)
		catalog['environment'] = list(self.environment)
		return catalog

	# PRIVATE METHODS

	def init_dependencies(self, spl): # add a dependency to the main package, so all the implementation of a package will be solve together, to deal with slotting
		name_base = spl.get('name_base')
		operator = "="
		name = spl['name_base']
		version = spl['features'][__main_feature__]['versions'][0]
		star = False
		slot = spl['features'][__main_feature__]['slots'][0]
		subslot = spl['features'][__main_feature__]['subslots'][0]
		self.dependencies.add(( operator, name, version, star, slot, subslot, True ))

	def format_data(self):
		features_used = { 'local': list(self.used_features['local']), 'external': { pn: list(s) for pn, s in self.used_features['external'].iteritems() } }
		dependencies = [ { 'operator': operator, 'name': name, 'version': version, 'star': star, 'slot': slot, 'subslot': subslot, 'configured': configured } for operator, name, version, star, slot, subslot, configured in self.dependencies ]
		self.spl[self.processing] = { 'features_used': features_used, 'dependencies': dependencies}
		self.dependencies = dependencies

	# REDEFINITION OF VISITOR METHODS
	def visitAtom(self, ctx):
		catpackage = ctx.catpackage().getText()
		# 1. version
		version = ctx.version()
		has_star = False
		if version:
			has_star = True if version.TIMES() else False
			version = version.getText()
			if has_star:
				version = version[:-1]
			else:
				self.versions.add(version)
		versionOP = ctx.versionOP()
		if versionOP:
			versionOP = versionOP.getText()
		# 2. slot
		slotspec = ctx.slotSPEC()
		if slotspec:
			if isinstance(slotspec, DepGrammarParser.SlotSIMPLEContext):
				slot = slotspec.slot
				subslot = None
			elif isinstance(slotspec, DepGrammarParser.SlotFULLContext):
				slot = slotspec.slot
				subslot = slotspec.subslot
			elif isinstance(slotspec, DepGrammarParser.SlotEQContext):
				slot = None
				subslot = None
			elif isinstance(slotspec, DepGrammarParser.SlotSTARContext):
				slot = None
				subslot = None
			elif isinstance(slotspec, DepGrammarParser.SlotSIMPLEEQContext):
				slot = slotspec.slot
				subslot = None
			if slot:
				slot = slot.getText()
				self.slots.add(slot)
			if subslot:
				subslot = subslot.getText()
				self.slots.add(subslot)
		else:
			slot = None
			subslot = None
		# 3. fill the registry
		self.spl_used.add(catpackage)
		self.dependencies.add( ( versionOP, catpackage, version, has_star, slot, subslot, True if ctx.selection() else False ) )
		# call original version
		self.current_package = catpackage
		DepGrammarVisitor.visitAtom(self, ctx)
		self.current_package = None

	def visitUse(self, ctx):
		use = ctx.getText()
		self.features.add(use)
		if self.current_package:
			data = self.used_features['external'].get(self.current_package)
			if not data:
				data = set()
				self.used_features['external'][self.current_package] = data
			data.add(use)
		else:
			self.used_features['local'].add(use)
		# call original version
		DepGrammarVisitor.visitUse(self, ctx)

	# REDEFINITION OF ERROR STRATEGY METHODS
	def syntaxError(self, recognizer, offendingSymbol, line, column, msg, e):
		msg = "Parsing error in \"" + self.processing + "\" (stage " + self.stage + "): column " + str(column) + " " + msg + "\nSentence: " + self.parsed_string
		raise Exception(msg)




######################################################################
### FUNCTIONS FOR PRE-PROCESSING
######################################################################


def preprocess(mspl):
	# process data
	graph = create_graph(mspl)
	preprocess_graph(graph)
	# transfert information to the mspl
	for node in graph.nodes():
		node.spl['reachable'] = [ obj.name for obj in node.reachable ]
		node.spl['shared'] = [ obj.name for obj in node.shared ]
		node.spl['included'] = [ obj.name for obj in node.included ]
		node.spl['loop'] = [ obj.name for obj in node.loop[1] ] if node.loop else None



class Node:
	def __init__(self, spl):
		self.spl = spl
		self.name = spl['name']

def create_graph(mspl):
	graph = networkx.DiGraph()
	dictionary = {}
	# 1. add the nodes
	for spl in mspl.values():
		node = Node(spl)
		dictionary[node.name] = node
		graph.add_node(node)
	# 2. add the edges
	for name, node in dictionary.iteritems():
		for dependency in node.spl['configures']:			
			next = dictionary.get(dependency)
			if next:
				graph.add_edge(node, next)
			else:
				print("Warning: SPL \"" + node.name + "\" has a dependency towards the inexistant SPL \"" + dependency + "\" => skipping")
	return graph


ID = 0
def preprocess_graph(graph):
	# 1. init the walking data in the nodes
	global ID
	ID = 0
	for node in graph.nodes():
		node.state = ID
		node.reachable = {}
		node.shared = set()
		node.included = set()
		node.loop = None
		node.visited = False
	for node in graph.nodes():
		if not node.visited:
			preprocess_rec(graph, node)

def preprocess_rec(graph, node):
	#print("LOG: visiting \"" + node.name() + "\" ->(ID=" + str(node.state) + ", " + str(node.visited) + ")")
	global ID
	if (not node.visited) and (node.state > 0): # we have a loop whose identified root is node
		#print("LOG: loop started at \"" +node.name() + "\": " + str((node.state, set([node]))))
		return (node.state, set([node]))
	elif node.state == 0: # node wasn't visited yet
		ID = ID + 1
		node.state = ID
		loop_root = ID
		loop_elements = set()
		for next in graph.successors_iter(node):
			#print("LOG: \"" + node.name() + "\" going in \"" + next.name() + "\"")
			loop_local = preprocess_rec(graph, next)
			has_loop = loop_local != None
			if has_loop: # update the loop information
				loop_local_root, loop_local_elements = loop_local
				#print("LOG: \"" + node.name() + "\" loop from \"" + next.name() + "\" => " + str(loop_local))
				loop_root = min(loop_local_root, loop_root)
				loop_elements.update(loop_local_elements)
			else: # update the reachable information
				for el, path in next.reachable.iteritems():
					if node.reachable.has_key(el): # shared element
						node.shared.add(el)
						node.included.update([next, el])
						node.included.update(path)
						node.included.update(node.reachable[el])
					else:
						node.reachable[el] = [next] + path
				for el in next.included:
					if node.reachable.has_key(el): # shared element
						node.shared.add(el)
						node.included.update([next, el])
						node.included.update(node.reachable[el])
					else:
						node.reachable[el] = [next]
				node.reachable[next] = []
		res = None
		if loop_elements:
			if loop_root == node.state: # we found all the elements of the loop
				#print("LOG: Loop Detected: " + str(loop_elements))
				# create the loop structure
				loop = (loop_root, loop_elements)
				# create the unified information of all the elements of the loop
				node.included.update(loop_elements)
				for nodeq in loop_elements - set([node]):
					node.shared.update(nodeq.shared)
					node.included.update(nodeq.included)
					for el, path in nodeq.reachable.iteritems():
						if node.reachable.has_key(el): # shared element
							node.shared.add(el)
							node.included.add(el)
							node.included.update(path)
							node.included.update(node.reachable[el])
						else:
							node.reachable[el] = path
				node.reachable = { key: [el for el in val if el not in node.included ] for key, val in node.reachable.iteritems() if key not in node.included }
				# unify the elements of the loop
				for nodeq in loop_elements - set([node]):
					nodeq.loop = loop
					nodeq.shared = node.shared
					nodeq.included = set(node.included)
					nodeq.reachable = node.reachable
				for nodeq in loop_elements:
					nodeq.included.discard(nodeq)
			else:
				loop_elements.add(node)
				res = (loop_root, loop_elements)
		else: # no loop => we can clean the reachable mapping
			node.reachable = { key: [el for el in val if el not in node.included ] for key, val in node.reachable.iteritems() if key not in node.included }
		node.visited = True
		return res


######################################################################
### FUNCTIONS FOR LOADING EXISTING CONFIGURATION
######################################################################


def load_configuration_features_equery(catpackage):
	equery_output = subprocess.check_output(["bash", "-c", "equery u " + catpackage + " | cut -c 1-"])
	return equery_output[:-1] # remove last line

# path=/var/db/pkg
def load_configuration(path):
	data = {}
	#output = subprocess.check_output(["bash", "-himBH", "list-gentoo-packages.sh"], env=__my_env__)
	f = open(path)
	output = f.read()
	f.close()
	#
	packages=output.split("\n")
	packages = packages[:-1] # remove last line
	for line in packages:
		items = line.split()
		package = items[0]
		features = items[1:]
		data[package] = features
	return data








