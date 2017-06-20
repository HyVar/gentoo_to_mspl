#!/usr/bin/python




######################################################################
### EXTRACTING USE MAPPING FROM THE AST
######################################################################

class SPLWrapper(object)
	def __init__(self, spl):
		self.spl = spl
	def __eq__(self, other):
		if isinstance(other, SPLWrapper):
			return self.spl['name'] == other.spl['name']
		else:
			return False
	def __hash__(self):
		return hash(self.spl['name'])

class ExtractUseFromAST(constraint_ast_visitor.ASTVisitor):
    def __init__(self):
        super(constraint_ast_visitor.ASTVisitor, self).__init__()
    def DefaultValue(self):
        return {}
    def CombineValue(self, value1, value2):
        utils.inline_combine_dicts(value1, value2, utils.inline_combine_lists)
        return value1

    def visitRequiredSIMPLE(self, ctx):
        return { self.spl: [ ctx['use'] ] }
    def visitCondition(self, ctx):
        return { self.spl: [ ctx['use'] ] }
    def visitAtom(self, ctx):
        self.local_package_name = atom_matching.PackagePattern(ctx) # stores the pattern
        return constraint_ast_visitor.ASTVisitor.visitAtom(self, ctx)
    def visitSelection(self,ctx):
    	if not 'default' in ctx: # if there is a default of the right sign, then this iuse is not a requirement
        	res = { self.local_package_name: [ ctx['use'] ] }
        	if 'suffix' in ctx: res[self.spl] = [ ctx['use'] ]
        	return  res
        else:
        	return {}

def extract_use_from_ast(ast_el):
    spl, local_ast, combined_ast = ast_el
    visitor = ExtractUseFromAST()
    visitor.spl_name = SPLWrapper(spl)
    uses = visitor.visitRequired(local_ast)
    utils.inline_combine_dicts(uses, visitor.visitDepend(combined_ast), utils.inline_combine_lists)
    return uses


######################################################################
### COMPLETING AND CHECKING IUSE DECLARATION IN PACKAGES
######################################################################

def check_profile_spl(parameter):
	package, used_iuses, implicit_iuse = parameter
	tmp = set(used_iuses)
	tmp.difference_update(package['features'])
	tmp.difference_update(implicit_iuse)
	res = set(used_iuses)
	if len(s) > 0:
		return ('error', package, (s, res))
	else:
		return ('ok', package, res)
 
def apply_profile_spl(parameter):
	code, package, res = parameter
	if code == 'error':
		missing, res = res
		logging.warning("Package \"" + package['name'] + "\" is missing the following iuses: " + str(missing))
	new_iuses = [ f for f in package['features'] if f not in res ] + list(res)
	package['features'] = new_iuses


def apply_profile(concurrent_map, atom_mapping, raw_asts, profile_iuse):
	# 1. get the necessary use flags for every components
	use_mapping_list = concurrent_map(extract_use_from_ast, raw_asts)
	use_mapping = {}
	map(lambda x: utils.inline_combine_dicts(use_mapping, x, utils.inline_combine_lists), use_mapping_list)
    use_mapping = { k: set(l) for k,l in use_mapping.iteritems() } # replace every list with sets
	# 2. check for all spl that they have no missing iuse
	implicit_iuse = set(profile_iuse)
	my_list = [ (package, used_iuses, implicit_iuse)
		for (pattern, used_iuses) in use_mapping.iteritems()
		for package in (atom_mapping[pattern] if isinstance(pattern, atom_matching.PackagePattern) else [ pattern.spl ])
		]
	result_list = concurrent_map(check_profile_spl, my_list)
	map(apply_profile_spl, result_list)


        # TODO: must remove the following lines when we start loading the profile
        mappings_list = concurrent_thread_map(extract_id_maps.generate_use_mappings_ast, asts)


# need to match all the atoms in all the constraints to the packages, to know if the requested features do exist


######################################################################
### CREATING THE CONFIGURATION CONSTRAINT
######################################################################



we need to apply the profile to the mspl
in the profile, we have
- necessary and conflicting packages
- base configuration of all packages
- iuse for all packages
How to save these information as part of the mspl?
Apart from the iuse, there is no places right now where to put these information.
I thus need to discuss to jacopo about it.


so, the application is done in two parts: adding the iuse to the mspl, and translating the configuration to the mspl structure.
first part is easy. we need a check to see if I don't forget anything.
If we want to do things intelligently, we can add only the iuse that are actually required.
We can extract these information by parsing the ast once.
That way, we can also check if all the features that are required are indeed declared
The only issue is that feature usage is also hidden inside installation scripts...
Well, it does not matter, as if the feature is not set by hyvarrec, then gentoo will use the default configuration.
So not considering features that are not relevant for us IS correct.

Second part is a bit more subtle.
We need a general operation that translate and constraints.
That way, I can generate everything (preferences, request constraint and current configuration) and use the translator.
 - current configuration is fine for now (I would rather go for pisitive and negative use flags)
 - preferences: how to deal with that? Well, actually, in gentoo, this is not a preference, but a hard constraint (it actually asks you to change things).
    the problem is, we don't have the syntax for this kind of constraint, which is "if the package is present, then these features must be set like this"
    I have to see that with Jacopo
 - request: this is the list of packages that are requested, and packages that forbidden. For the encoding of the use flags, I need to ask jacopo what I can do.

