#!/usr/bin/python

# for version matching
import re

import egencache_utils
import constraint_ast_visitor

######################################################################
### SIMPLE HASH-AWARE CLASS TO MATCH AN SPL
######################################################################

# TODO: pattern constructor from an actual name?

def compare_version(s1, s2):
	i, len1, len2 = 0, len(s1), len(s2)
	maximum = min(len1, len2)
	while (i < maximum) and (s1[i] == s2[i]):
		i = i + 1
	if i == maximum:
		return len1 - len2
	else:
		if s1[i].isdigit() and s2[i].isdigit():
			n1 = int(re.search("\d+", s1[i:]).group(0))
			n2 = int(re.search("\d+", s2[i:]).group(0))
			return n1 - n2
		else:
			return ord(s1[i]) - ord(s2[i])


class pattern_all(object):
	def match(self, whatever):
		return True

class pattern_complete(object):
	def match_full_spl(self, spl):
		return self.match_full(spl['group_name'], spl['versions']['full'], spl['versions']['base'], spl['slot'], spl['subslot'])

	def match_simple_spl(self, spl):
		return self.match_only_package_version(spl['versions']['full'], spl['versions']['base']) and self.match_only_slot(spl['slot'], spl['subslot'])
		
	def match_simple_spl_name(self, spl_name):
		package_group, version_full, version, revision = egencache_utils.structure_package_name(atom['package'])
		return self.match_only_package_group(package_group) and self.match_only_package_version(version_full, version)

	def match_only_package_group(self, group_name):
		return self.package_group != group_name

	def match_only_package_version(self, version_full, version_base):
		if self.version_op:
			compare = compare_version(version_full, self.version_full)
			if self.version_op == ">=":
				if compare < 0:
					return False
			elif self.version_op == ">":
				if compare <= 0:
					return False
			elif self.version_op == "~":
				if res.version != version_base:
					return False
			elif self.version_op == "=":
				if self.time:
					if not version_full.startwith(self.version_all):
						return False
				else:
					if compare != 0:
						return False
			elif self.version_op == "<=":
				if compare > 0:
					return False
			elif self.version_op == "<":
				if compare >= 0:
					return False
		return True

	def match_only_slot(self, slot, subslot):
		if self.slot:
			if self.slot != slot:
				return False
		if self.subslot:
			if self.subslot != subslot:
				return False

		return True


	def match_spl_name(self, group_name, version_full, version_base):


	def match_full(self, group_name, version_full, version_base, slot, subslot):
		return self.match_only_package_group(group_name) and self.match_only_package_version(version_full, version_base) and self.match_only_slot(slot, subslot)


	def __match_old(self, spl):
		# 1. check the name
		if self.package_group != spl['group_name']:
			return False
		# 2. check the version
		if self.version_op:
			compare = compare_version(spl['versions']['full'], self.version_all)
			if self.version_op == ">=":
				if compare < 0:
					return False
			elif self.version_op == ">":
				if compare <= 0:
					return False
			elif self.version_op == "~":
				if res.version != spl['versions']['base']:
					return False
			elif self.version_op == "=":
				if self.time:
					if not spl['versions']['full'].startwith(self.version_all):
						return False
				else:
					if compare != 0:
						return False
			elif self.version_op == "<=":
				if compare > 0:
					return False
			elif self.version_op == "<":
				if compare >= 0:
					return False
		# 3. check slots
		if self.slot:
			if self.slot != spl['slot']:
				return False
		if self.subslot:
			if self.subslot != spl['subslot']:
				return False
		# everything was checked
		return True

	def match_package_groups(self, package_groups):
		return filter(self.match_simple_spl, package_groups[self.package_group])


	def __hash__(self):
		return hash(self.package_group) + hash(self.version_all)
		+ hash(self.version_op) + hash(self.time) + hash(self.slots) + hash(self.subslot)
	def __eq__(self, other):
		if isinstance(other, PackagePattern):
			return (self.package_group == other.package_group) and (self.version_all == other.version_all) and (self.version_op == other.version_op) and (self.time == other.time) and (self.slot == other.slot) and (self.subslot == other.subslot)
		else:
			return False
	def __str__(self):
		if self.version_op:
			res = self.version_op
		else:
			res = ""
		res = res + self.package_group
		if self.version_full:
			res = res + "-" + self.version_full
		if self.slot:
			res = res + ":" + self.slot
			if self.subslot:
				res = res + "/" + res.subslot
		return res


def pattern_from_atom(atom):
	res = pattern_complete()
	res.package_group, res.version_full, res.version = egencache_utils.structure_package_name(atom['package'])
	if 'version_op' in atom:
		res.version_op = atom['version_op']
	else:
		res.version_op = None
	if 'times' in atom:
		res.time = True
	else:
		res.time = False
	if 'slots' in atom:
		slots = atom['slots']
		if 'slot' in slots:
			res.slot = slots['slot']
			if 'subslot' in slots:
				res.subslot = slots['subslot']
			else:
				res.subslot = None
		else:
			res.slot = None
			res.subslot = None
	else:
		res.slot = None
		res.subslot = None
	return res

def pattern_

######################################################################
### FUNCTION TO CREATE A MAPPING ATOM -> MATCHING PACKAGES
######################################################################

class ExtractAtoms(constraint_ast_visitor.ASTVisitor):
    def __init__(self):
        super(constraint_ast_visitor.ASTVisitor, self).__init__()
    def DefaultValue(self):
        #return set([])
        return []
    def CombineValue(self, value1, value2):
    	#value1.update(value2)
        #return value1
        value1.extend(value2)
        return value1

    def visitAtom(self, ctx):
        #return set([ PackagePattern(ctx) ])
        return [ PackagePattern(ctx) ]

    def visit_ast(self, ast):
    	spl, local_ast, combined_ast = ast
    	return self.visitDepend(combined_ast)

def pattern_match_pattern(pattern, package_groups):
	if pattern.package_group in package_groups:
		spls = package_groups[pattern.package_group]['reference']
	else:
		spls = []
	return (pattern, filter(pattern.match, spls))


def extract_atom_mapping(concurrent_map, package_groups, asts):
	# 1. get the atoms from the constraints
	visitor = ExtractAtoms()
	atoms_list = concurrent_map(visitor.visit_ast, asts)
	atoms = set([ atom for atom_set in atoms_list for atom in atom_set])
	# 2. create the mapping
	result_list = concurrent_map(lambda x: pattern_match_pattern(x, package_groups), atoms)
	return { pattern: l  for pattern, l in result_list }

