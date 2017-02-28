"""
Module that translate the gentoo dependencies into hyvarrec like input constraints
"""
__author__ = "Jacopo Mauro"
__copyright__ = "Copyright 2017, Jacopo Mauro"
__license__ = "ISC"
__version__ = "0.1"
__maintainer__ = "Jacopo Mauro"
__email__ = "mauro.jacopo@gmail.com"
__status__ = "Prototype"

from antlr4 import *
from antlr4.error.ErrorListener import ErrorListener
from dependencies_grammar.DepGrammarLexer import DepGrammarLexer
from dependencies_grammar.DepGrammarParser import DepGrammarParser
from dependencies_grammar.DepGrammarVisitor import DepGrammarVisitor

import re
import settings
import logging




def match_package_version(template, operator, s):
    """
    Check if a version package matches a template
    """
    if operator == "~":
        return match_package_version(template + "-r*", "=", s)
    if operator == "=":
        template = re.sub('\.','\\\.',template)
        template = re.sub('\*', '.*', template)
        if re.match(template,s):
            return True
        else:
            return False

    # operators different from = and ~
    p = re.compile("(?P<nums>[0-9]+(?:\.[0-9]+)*)(?:_|-)?.*")
    t_match = p.search(template)
    t_nums = map(lambda x: int(x), t_match.group("nums").split("."))
    s_match = p.search(s)
    s_nums = map(lambda x: int(x), s_match.group("nums").split("."))

    if operator == '<=':
        return s_nums <= t_nums
    elif operator == '>=':
        return s_nums >= t_nums
    elif operator == '<':
        return s_nums < t_nums
    elif operator == '>':
        return s_nums > t_nums
    else:
        raise Exception("Operator " + operator + " not supported for package version comparison")



class DepVisitor(DepGrammarVisitor, ErrorListener):
    def __init__(self, mspl, map_name_id,package):
        """
        The flag mode is used to parse the local constraints only that can contain only use flags
        :param mspl:
        :param map_name_id:
        :param package:
        :param flag_mode: True in case the dependencies to parse are local
        """
        super(DepGrammarVisitor, self).__init__()
        super(ErrorListener, self).__init__()
        self.mspl = mspl
        self.map_name_id = map_name_id
        self.package = package
        self.constraints = []

    def parser(self, parsed_string):
        self.parsed_string = parsed_string
        lexer = DepGrammarLexer(InputStream(parsed_string))
        lexer._listeners = [self]
        parser = DepGrammarParser(CommonTokenStream(lexer))
        parser._listeners = [self]
        return parser

    def visitSlotSPEC(self,ctx):
        slot = None
        subslot = None
        if ctx.slotID(): # if it is not a terminal
            slot = ctx.getChild(0).getText()
            if ctx.getChildCount() == 3:
                subslot = ctx.getChild(2).getText()
        return (slot,subslot)

    def visitSelection(self, ctx):
        sym = "" # merge of prefix and suffix
        if ctx.prefix():
            sym += ctx.prefix().getText()
        use = ctx.use().getText()
        dep_def = ""
        if ctx.preference():
            dep_def = ctx.preference().getText()[1]
        if ctx.suffix():
            sym += ctx.suffix().getText()

        return sym,use,dep_def

    def visitSelection_comma_list(self, ctx):

        def is_compact(s):
            return "!" in pre or "?" in pre or "=" in pre

        ls_normal = []
        ls_compact = []
        for i in range(0, ctx.getChildCount(),2):
            pre,use,dep_def = ctx.getChild(i).accept(self)
            if is_compact(pre):
                ls_compact.append((pre,use,dep_def))
            else:
                ls_normal.append((pre,use,dep_def))
        return ls_normal,ls_compact

    def visitUse_flag(self, ctx):
        return ctx.use().getText()

    def visitLocalDEPcondition(self, ctx):
        use_flag = ctx.use_flag().accept(self)
        if use_flag not in self.map_name_id["flag"][self.package]:
            logging.error("Flag " + use_flag + " not declared for package " + self.package + ". Ignoring the constraint")
            return "true"
        feature = settings.get_hyvar_flag(self.map_name_id["flag"][self.package][use_flag])
        ls = []
        c = feature + " = "
        if ctx.NOT():
            c += "0 impl ("
            for i in range(3, ctx.getChildCount() - 1):
                ls.append(ctx.getChild(i).accept(self))
        else:
            c += "1 impl ("
            for i in range(2, ctx.getChildCount() - 1):
                ls.append(ctx.getChild(i).accept(self))
        c += settings.get_hyvar_and(ls) + ")"
        return c

    def visitLocalDEPatom(self, ctx):
        flag_name = ctx.use().getText().strip()
        if flag_name not in self.map_name_id["flag"][self.package]:
            logging.error("The use flag " + flag_name + " is not a valid one for package " + self.package +
                          ". Return a false constraint.")
            return "false"
        c = settings.get_hyvar_flag(self.map_name_id["flag"][self.package][flag_name])
        if ctx.getChildCount() > 1:
            # its a conflict and not a dependency
            # we treat ! and !! in a similar way
            return "not (" + c + ")"
        else:
            return c

    def visitLocalDEPchoice(self, ctx):
        choice = ctx.choice().getText()
        ls = []
        for i in range(2,ctx.getChildCount()-1):
            ls.append(ctx.getChild(i).accept(self))
        if choice == "??":
            if len(ls) == 1:
                return ls[0]
            elif len(ls) == 2:
                return "( " + ls[0] + " xor " + ls[1] + ")"
            else:
                # dev-qt/qtwebkit-5.7.1
                # todo fix onemax
                logging.error("?? onemax operator in local dependency not supported with more than two arguments. ")
                return "false"
        elif choice == "^^":
            if len(ls) == 2:
                return "( " + ls[0] + " xor " + ls[1] + ")"
            else:
                logging.error("^^ xor operator in local dependency not supported with more than two arguments. Return false")
                return "false"
        else: # choice == "||"
            return settings.get_hyvar_or(ls)

    def visitLocalDEPparen(self, ctx):
        ls = []
        for i in range(1,ctx.getChildCount()-1):
            ls.append(ctx.getChild(i).accept(self))
        return settings.get_hyvar_and(ls)

    def visitLocalDEP(self, ctx):
        for i in range(ctx.getChildCount()):
            self.constraints.append(
                settings.get_hyvar_package(self.map_name_id["package"][self.package]) + " = 1 impl (" +
                ctx.getChild(i).accept(self)  + ")")

    def visitAtom(self, ctx):

        def get_expression(package,slot,subslot,flags):
            """
            Used to print the constraint string when the flags are simple (i.e., only + e -).
            """
            id = self.map_name_id["package"][package]
            c = settings.get_hyvar_package(id) + " = 1"
            if slot:
                if slot not in self.map_name_id["slot"][package]:
                    # return false because the slot is not allowed
                    #logging.warning("Slot " + slot + " not found for package " + package + ". Return false constraint")
                    return "false"
                c += " and " + settings.get_hyvar_slot(id) + " = " + unicode(self.map_name_id["slot"][package][slot])
            if subslot:
                if subslot not in  self.map_name_id["subslot"][package]:
                    # return false because the subslot is not allowed
                    #logging.warning("Subslot " + subslot + " not found for package " + package + ". Return false constraint")
                    return "false"
                c += " and " + settings.get_hyvar_subslot(id) + " = " +\
                     unicode(self.map_name_id["subslot"][package][subslot])
            for pre,flag,def_dep in flags:
                if package in self.map_name_id["flag"] and flag in self.map_name_id["flag"][package]:
                    # flag is actually set by the package
                    if "-" in pre:
                        c += " and " + settings.get_hyvar_flag(self.map_name_id["flag"][package][flag]) + " = 0"
                    else:
                        c += " and " + settings.get_hyvar_flag(self.map_name_id["flag"][package][flag]) + " = 1"
                else: # use the def_dep setting
                    if not def_dep: # in this case the default is not set and the flag is not set
                        if "-" not in pre: # non selectable flag is required to be selected
                            return "false"
                        # flag that can not be set is required to be deselected
                        # we allow that -> no need to add an additional constraint
                    elif "-" in pre and "+" in def_dep:
                        return "false"
                    elif "-" not in pre and "-" in def_dep:
                        return "false"
                    # remaining cases (-,-) and (+,+) are true and no constraint need to be added
            return c

        def get_cond_expression(package_targets, slot, subslot, flag_name, flags, flag_set):
            """
            Used to print the constraint string in the compact form.
            Flags is a list of pairs (pre,use) with at most one element
            """

            if flag_name not in self.map_name_id["flag"][self.package]:
                logging.error("Flag " + flag_name + " not declared for package " + self.package + ". Ignoring the constraint")
                return "true"
            flag_representation = settings.get_hyvar_flag(self.map_name_id["flag"][self.package][flag_name])
            ls = []
            for i in package_targets:
                ls.append(get_expression(i,slot,subslot,flags))
            c = settings.get_hyvar_or(ls)
            if c == "false":
                logging.warning("Subslot " + unicode(subslot) + " or slot " + unicode(slot) +
                                " not found in packages " + unicode(package_targets) +
                                ". Return false constraint while processing " + self.package)
            if flag_set:
                return flag_representation + " = 1 impl " + c
            else:
                return flag_representation + " = 0 impl " + c

        package = ctx.catpackage().getText().strip()
        version_op = ctx.versionOP()
        if version_op:
            m = re.search("-[0-9]+(\.[0-9]+)*[a-zA-Z]?((_alpha|_beta|_pre|_rc|_p)[0-9]*)*(-r[0-9]+)?$", package)
            if m:
                version = m.group()[1:]
                package = package.replace("-" + version, "")
            else:
                logging.error("Impossible to find version in package " + package)
                exit(1)
            if ctx.TIMES():
                version += "*"

        if package not in self.mspl:
            logging.warning("Package " + package + " in dependency of package " + self.package + " does not exits.")
            return "false"
        packages = []

        # if version is specified
        if version_op:
            version_op = ctx.versionOP().getText()
            for i in self.mspl[package]["implementations"].keys():
                if match_package_version(version,version_op,i):
                    packages.append(self.mspl[package]["implementations"][i])
        else:
            if "implementations" in self.mspl[package]:
                packages = self.mspl[package]["implementations"].values()
            else:
                packages.append(package)

        # slots
        # := and :* are ignored since they do not restrict the use of slots
        # :SLOT= and :SLOT are treated in a similar way
        # :SLOT/SUBSLOT is captured setting both slot and subslot
        slot = ctx.slotSPEC()
        if slot:
            slot,subslot = slot.accept(self)
        else:
            slot,subslot = (None, None)

        ls = []
        if ctx.selection_comma_list():
            simple_list,compact_list = ctx.selection_comma_list().accept(self)
            # handle simple use flags
            if simple_list:
                ls.append(settings.get_hyvar_or([get_expression(x, slot, subslot, simple_list) for x in packages ]))
            # handle the compact representations
            for (pre,flag_name,dep_def) in compact_list:
                if "?" in pre and "!" in pre: # app-misc/foo[!bar?]    bar? (app-misc/foo) !bar? (app-misc/foo[-bar])
                    ls.append( settings.get_hyvar_and( [
                        get_cond_expression(packages, slot, subslot, flag_name, [],True),
                        get_cond_expression(packages, slot, subslot, flag_name, [("-", flag_name,dep_def)], False)
                    ]))
                elif "?" in pre: # app-misc/foo[bar?] -> bar? (app-misc/foo[bar]) !bar? (app-misc/foo)
                    ls.append(settings.get_hyvar_and([
                        get_cond_expression(packages, slot, subslot, flag_name, [("", flag_name,dep_def)], True),
                        get_cond_expression(packages, slot, subslot, flag_name, [], False)
                    ]))
                elif "=" in pre and "!" in pre:  # app-misc/foo[!bar=]    bar? (app-misc/foo[-bar]) !bar? (app-misc/foo[bar])
                    ls.append(settings.get_hyvar_and([
                        get_cond_expression(packages, slot, subslot, flag_name, [("-", flag_name,dep_def)], True),
                        get_cond_expression(packages, slot, subslot, flag_name, [("", flag_name,dep_def)], False)
                    ]))
                elif "=" in pre:  # app-misc/foo[bar=]    bar? (app-misc/foo[bar]) !bar? (app-misc/foo[-bar])
                    ls.append(settings.get_hyvar_and([
                        get_cond_expression(packages, slot, subslot, flag_name, [("", flag_name,dep_def)], True),
                        get_cond_expression(packages, slot, subslot, flag_name, [("-", flag_name,dep_def)], False)
                    ]))
                else:
                    logging.error("Prefix " + pre + " of compact form not recognized. Exiting")
                    exit(1)
        else:
            c = settings.get_hyvar_or([get_expression(x, slot, subslot, []) for x in packages])
            if c == "false":
                logging.warning("Subslot " + unicode(subslot) + " or slot " + unicode(slot) +
                                " not found in packages " + unicode(packages) +
                                ". Return false constraint while processing " + self.package)
            ls.append(c)
        return settings.get_hyvar_and(ls)


    def visitDependELatom(self, ctx):
        c = ctx.atom().accept(self)
        if ctx.getChildCount() > 1:
            # its a conflict and not a dependency
            # we treat ! and !! in a similar way
            return "not (" + c + ")"
        else:
            return c

    def visitDependELor(self, ctx):
        ls = []
        for i in range(2,ctx.getChildCount()-1):
            ls.append(ctx.getChild(i).accept(self))
        return settings.get_hyvar_or(ls)

    def visitDependELparen(self, ctx):
        ls = []
        for i in range(1,ctx.getChildCount()-1):
            ls.append(ctx.getChild(i).accept(self))
        return settings.get_hyvar_and(ls)

    def visitDependELcondition(self, ctx):
        use_flag = ctx.use_flag().accept(self).strip()
        if use_flag not in self.map_name_id["flag"][self.package]:
            logging.error("Flag " + use_flag + " not declared for package " + self.package + ". Ignoring the constraint")
            return "true"
        feature = settings.get_hyvar_flag(self.map_name_id["flag"][self.package][use_flag])
        ls = []
        c = feature + " = "
        if ctx.NOT():
            c += "0 impl ("
            for i in range(3, ctx.getChildCount() - 1):
                ls.append(ctx.getChild(i).accept(self))
        else:
            c += "1 impl ("
            for i in range(2, ctx.getChildCount() - 1):
                ls.append(ctx.getChild(i).accept(self))
        c += settings.get_hyvar_and(ls) + ")"
        return c

    def visitDepend(self, ctx):
        for i in range(ctx.getChildCount()):
            c = ctx.getChild(i).accept(self)
            self.constraints.append(
                settings.get_hyvar_package(self.map_name_id["package"][self.package]) + " = 1 impl (" + c + ")")

    # REDEFINITION OF ERROR STRATEGY METHODS
    def visitErrorNode(self, node):
        token = node.getSymbol()
        raise Exception("Erroneous Node at line " +
                        str(token.line) + ", column " + str(token.column) + ": '" +
                        str(token.text) + "'")

    def syntaxError(self, recognizer, offendingSymbol, line, column, msg, e):
        msg = "Parsing error, column " + str(column) + ", " + msg + "\nSentence: " + self.parsed_string
        raise Exception(msg)

