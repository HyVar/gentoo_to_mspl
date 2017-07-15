'''
Module defining the AST visitor created by parsing the gentoo dependencies
'''

__author__ = "Michael Lienhardt & Jacopo Mauro"
__copyright__ = "Copyright 2017, Michael Lienhardt & Jacopo Mauro"
__license__ = "ISC"
__version__ = "0.5"
__maintainer__ = "Michael Lienhardt & Jacopo Mauro"
__email__ = "michael.lienhardt@laposte.net & mauro.jacopo@gmail.com"
__status__ = "Prototype"

import core_data


######################################################################
# AST CORE VISITOR
######################################################################


class ASTVisitor(object):
	"""
	this is the base Visitor class for our AST
	"""
	def DefaultValue(self): return None

	def CombineValue(self, value1, value2): return value1

	def visitRequired(self, ctx):
		return reduce(self.__mapvisitRequiredEL, ctx, self.DefaultValue())

	def visitRequiredEL(self, ctx):
		if ctx['type'] == "rsimple":
			return self.visitRequiredSIMPLE(ctx)
		elif ctx['type'] == "rcondition":
			return self.visitRequiredCONDITION(ctx)
		elif ctx['type'] == "rchoice":
			return self.visitRequiredCHOICE(ctx)
		elif ctx['type'] == "rinner":
			return self.visitRequiredINNER(ctx)

	def visitRequiredSIMPLE(self, ctx): return self.DefaultValue()

	def visitRequiredCONDITION(self, ctx):
		return reduce(self.__mapvisitRequiredEL, ctx['els'], self.visitCondition(ctx['condition']))

	def visitRequiredCHOICE(self, ctx):
		return reduce(self.__mapvisitRequiredEL, ctx['els'], self.DefaultValue())

	def visitRequiredINNER(self, ctx):
		return reduce(self.__mapvisitRequiredEL, ctx['els'], self.DefaultValue())

	def visitDepend(self, ctx):
		return reduce(self.__mapvisitDependEL, ctx, self.DefaultValue())

	def visitDependEL(self, ctx):
		if ctx['type'] == "dsimple":
			return self.visitDependSIMPLE(ctx)
		elif ctx['type'] == "dcondition":
			return self.visitDependCONDITION(ctx)
		elif ctx['type'] == "dchoice":
			return self.visitDependCHOICE(ctx)
		elif ctx['type'] == "dinner":
			return self.visitDependINNER(ctx)

	def visitDependSIMPLE(self, ctx):
		res = self.visitAtom(ctx['atom'])
		if "selection" in ctx:
			return reduce(self.__mapvisitSelection, ctx['selection'], res)
		else: return res


	def visitDependCONDITION(self, ctx):
		return reduce(self.__mapvisitDependEL, ctx['els'], self.visitCondition(ctx['condition']))

	def visitDependCHOICE(self, ctx):
		return reduce(self.__mapvisitDependEL, ctx['els'], self.DefaultValue())

	def visitDependINNER(self, ctx):
		return reduce(self.__mapvisitDependEL, ctx['els'], self.DefaultValue())

	def visitChoice(self, ctx):
		return self.DefaultValue()

	def visitCondition(self, ctx):
		return self.DefaultValue()

	def visitAtom(self, ctx):
		return self.DefaultValue()

	def visitSelection(self, ctx):
		res = self.DefaultValue()
		if 'prefix' in ctx:
			res = self.CombineValue(res, self.visitPrefix(ctx['prefix']))
		if 'default' in ctx:
			res = self.CombineValue(res, self.visitDefault(ctx['default']))
		if 'suffix' in ctx:
			res = self.CombineValue(res, self.visitSuffix(ctx['suffix']))
		return res

	def visitPrefix(self, ctx): return self.DefaultValue()

	def visitDefault(self, ctx): return self.DefaultValue()

	def visitSuffix(self, ctx): return self.DefaultValue()

	def __mapvisitRequiredEL(self,x,y): return self.CombineValue(x, self.visitRequiredEL(y))

	def __mapvisitDependEL(self,x,y): return self.CombineValue(x, self.visitDependEL(y))

	def __mapvisitSelection(self,x,y): return self.CombineValue(x, self.visitSelection(y))


######################################################################
# AST TRANSLATION TO AND FROM SAVE FORMAT
######################################################################

class ASTToSaveFormatVisitor(ASTVisitor):
	def visitRequired(self, ctx): return ctx
	def visitRequiredEL(self, ctx): return ctx
	def visitRequiredSIMPLE(self, ctx): return ctx
	def visitRequiredCONDITION(self, ctx): return ctx
	def visitRequiredCHOICE(self, ctx): return ctx
	def visitRequiredINNER(self, ctx): return ctx

##

	def visitDepend(self, ctx):
		return [ self.visitDependEL(el) for el in ctx ]

	def visitDependEL(self, ctx):
		if ctx['type'] == "dsimple":
			return self.visitDependSIMPLE(ctx)
		elif ctx['type'] == "dcondition":
			return self.visitDependCONDITION(ctx)
		elif ctx['type'] == "dchoice":
			return self.visitDependCHOICE(ctx)
		elif ctx['type'] == "dinner":
			return self.visitDependINNER(ctx)

	def visitDependSIMPLE(self, ctx):
		res = dict(ctx)
		res['atom'] = self.visitAtom(res['atom'])
		return res

	def visitDependCONDITION(self, ctx):#idem
		res = dict(ctx)
		res['els'] = [ self.visitDependEL(el) for el in res['els'] ]
		return res

	def visitDependCHOICE(self, ctx):
		res = dict(ctx)
		res['els'] = [ self.visitDependEL(el) for el in res['els'] ]
		return res

	def visitDependINNER(self, ctx):
		res = dict(ctx)
		res['els'] = [ self.visitDependEL(el) for el in res['els'] ]
		return res

	def visitChoice(self, ctx): return ctx

	def visitCondition(self, ctx): return ctx

	def visitAtom(self, ctx):
		return core_data.pattern_to_save_format(ctx)

	def visitSelection(self, ctx): return ctx

	def visitPrefix(self, ctx): return ctx

	def visitDefault(self, ctx): return ctx

	def visitSuffix(self, ctx): return ctx


class ASTFromSaveFormatVisitor(ASTVisitor):
	def visitRequired(self, ctx): return ctx
	def visitRequiredEL(self, ctx): return ctx
	def visitRequiredSIMPLE(self, ctx): return ctx
	def visitRequiredCONDITION(self, ctx): return ctx
	def visitRequiredCHOICE(self, ctx): return ctx
	def visitRequiredINNER(self, ctx): return ctx

##

	def visitDepend(self, ctx):
		return [ self.visitDependEL(el) for el in ctx ]

	def visitDependEL(self, ctx):
		if ctx['type'] == "dsimple":
			return self.visitDependSIMPLE(ctx)
		elif ctx['type'] == "dcondition":
			return self.visitDependCONDITION(ctx)
		elif ctx['type'] == "dchoice":
			return self.visitDependCHOICE(ctx)
		elif ctx['type'] == "dinner":
			return self.visitDependINNER(ctx)

	def visitDependSIMPLE(self, ctx):
		res = dict(ctx)
		res['atom'] = self.visitAtom(res['atom'])
		return res

	def visitDependCONDITION(self, ctx):
		res = dict(ctx)
		res['els'] = [ self.visitDependEL(el) for el in res['els'] ]
		return res

	def visitDependCHOICE(self, ctx):
		res = dict(ctx)
		res['els'] = [ self.visitDependEL(el) for el in res['els'] ]
		return res

	def visitDependINNER(self, ctx):
		res = dict(ctx)
		res['els'] = [ self.visitDependEL(el) for el in res['els'] ]
		return res

	def visitChoice(self, ctx): return ctx

	def visitCondition(self, ctx): return ctx

	def visitAtom(self, ctx):
		return core_data.pattern_from_save_format(ctx)

	def visitSelection(self, ctx): return ctx

	def visitPrefix(self, ctx): return ctx

	def visitDefault(self, ctx): return ctx

	def visitSuffix(self, ctx): return ctx

##


def ast_require_to_save_format(ast):
	return ASTToSaveFormatVisitor().visitRequired(ast)


def ast_depend_to_save_format(ast):
	return ASTToSaveFormatVisitor().visitDepend(ast)


def ast_require_from_save_format(save_format):
	return ASTFromSaveFormatVisitor().visitRequired(save_format)


def ast_depend_from_save_format(save_format):
	return ASTFromSaveFormatVisitor().visitDepend(save_format)

