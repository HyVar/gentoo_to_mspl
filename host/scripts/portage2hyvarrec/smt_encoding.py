######################################################################
### FUNCTIONS FOR MSPL TRANSLATION
### Assumes that the compact form have been already decompacted
######################################################################


import pysmt
import re
import constraint_ast_visitor
import utils
import pysmt.shortcuts as smt

def match_version(template, operator, p_name):
    """
    Check if a version package s (a string) matches a template
    Note that s and template need to have the same base package
    """
    if operator == "~":
        return match_version(template + "-r*", "=", p_name) or match_version(template, "=", p_name)
    if operator == "=":
        # update re special chars in the template
        template = re.sub('\.', '\\\.', template)
        template = re.sub('\*', '.*', template) + "$"
        if re.match(template,p_name):
            return True
        else:
            return False

    # operators different from = and ~
    p = re.compile("(?P<nums>[0-9]+(?:\.[0-9]+)*)(?:_|-)?.*")
    t_match = p.search(template)
    t_nums = map(lambda x: int(x), t_match.group("nums").split("."))
    s_match = p.search(p_name)
    s_nums = map(lambda x: int(x), s_match.group("nums").split("."))

    if operator == '<=':
        return s_nums <= t_nums
    elif operator == '>=':
        return s_nums >= t_nums
    elif operator == '>':
        return s_nums < t_nums
    elif operator == '<':
        return s_nums > t_nums
    else:
        raise Exception("Operator " + operator + " not supported for package version comparison")


def match_slot(data,slot,p_name):
    """
    Checks if the package p_name has slot slot
    """
    return "slot" in data[p_name] and data[p_name]["slot"] == slot


def match_subslot(data,subslot,p_name):
    """
    Checks if the package p_name has subslot subslot
    """
    return "subslot" in data[p_name] and data[p_name]["subslot"] == subslot


def get_packages(data,template,operator,slot="",subslot=""):
    """
    :param data: the mspl data file
    :param template: string representing the template to match
    :param operator: comparison operator
    :param slot: if required which slot
    :param subslot: if required which subslot
    :return: list of versioned packages that match with the given paramters
    """

    base_pkg = utils.get_base_package(template)
    if base_pkg:
        ls = [x for x in data[base_pkg]["implementations"] if match_version(template,operator,x)]
        if slot:
            ls = [x for x in ls if match_slot(data,slot,x)]
        if subslot:
            ls = [x for x in ls if match_subslot(data,subslot,x)]
        return ls
    return []

##############################################
# auxiliary functions
##############################################

def get_smt_package(map_name_id,p_name):
    return smt.Symbol("p" + map_name_id["package"][p_name])

def get_smt_use(map_name_id,p_name,u_name):
    return smt.Symbol("u" + map_name_id["flag"]["package"][u_name])

def get_smt_context(map_name_id,c_name):
    return smt.Symbol("u" + map_name_id["context"][c_name])

def get_no_two_true_expressions(fs):
    return smt.And([smt.Not(smt.And(fs[i], fs[j])) for i in range(fs) for j in range(fs) if i < j])


def process_simple_atom(mspl,ctx)

def decompact_atom(ctx):

    def get_use(ctx):
        use = {"use": ctx["use"]}
        if "preference" in ctx:
            use["preference"] = ctx["preference"]
        return use

    # decompact the comapct atoms
    assert "selection" in ctx
    condELs = []
    normal_sels = []
    for i in ctx["selection"]:
        if "prefix" in i and i["prefix"] == "!":
            if "suffix" in i:
                if i["suffix"] == "?":
                    # app - misc / foo[!bar?]    bar? (app - misc / foo) !bar? (app - misc / foo[-bar])
                    first = {
                        "condition": {'use': i["use"]},
                        "els" : [ { x:y for x,y in ctx if x != "selection" and x != "type" }]}
                    second = first.deepcopy()
                    second["condition"]["not"] = ""
                    second["els"][0]["selection"] = [get_use(i) + {"prefix": "-" }]
                    condELs.extend([first,second])
                elif i["suffix"] == "=":
                    # app - misc / foo[!bar =]    bar? (app - misc / foo[-bar]) !bar? (app - misc / foo[bar])
                    first = {
                        "condition": {'use': i["use"]},
                        "els" : [ { x:y for x,y in ctx if x != "selection" and x != "type" }]}
                    second = first.deepcopy()
                    first["els"][0]["selection"] = [get_use(i) + {"prefix": "-"}]
                    second["els"][0]["selection"] = [get_use(i)]
                    second["condition"]["not"] = ""
                    condELs.extend([first,second])
            else:
                raise Exception("Find prefix ! but not suffix ? or = for use " + i["use"])
        elif "suffix" in i:
            if i["suffix"] == "?":
                # app - misc / foo[bar?]    bar? (app - misc / foo[bar]) !bar? (app - misc / foo)
                first = {
                    "condition": {'use': i["use"]},
                    "els": [{x: y for x, y in ctx if x != "selection" and x != "type"}]}
                second = first.deepcopy()
                first["els"][0]["selection"] = [get_use(i)]
                second["condition"]["not"] = ""
                condELs.extend([first, second])
            elif i["suffix"] == "=":
                # app - misc / foo[bar =]    bar? (app - misc / foo[bar]) !bar? (app - misc / foo[-bar])
                first = {
                    "condition": {'use': i["use"]},
                    "els": [{x: y for x, y in ctx if x != "selection" and x != "type"}]}
                second = first.deepcopy()
                first["els"][0]["selection"] = [get_use(i)]
                second["els"][0]["selection"] = [get_use(i) + {"prefix": "-"}]
                second["condition"]["not"] = ""
                condELs.extend([first, second])
        else:
            normal_sels.append(i)
    return condELs,normal_sels


##############################################
# visitor to convert the AST into SMT formulas
##############################################
class visitorASTtoSMT(constraint_ast_visitor.ASTVisitor):

    def __init__(self,mspl,map_name_id,package):
        super(constraint_ast_visitor.ASTVisitor, self).__init__()
        self.map_name_id = map_name_id
        self.package = package
        self.mspl = mspl

    # def CombineValue(self, value1, value2):
    #     return value1

    def visitRequired(self, ctx):
        return smt.And(map(self.mapvisitRequiredEL, ctx))

    def visitRequiredSIMPLE(self, ctx):
        assert(self.map_name_id[self.package][ctx["use"]]) # flag must exists
        if "not" in ctx:
            return smt.Not(get_smt_use(self.map_name_id,self.package,ctx["use"]))
        else:
            return get_smt_use(self.map_name_id, self.package, ctx["use"])

    def visitRequiredCONDITION(self, ctx):
        formulas = map(self.visitRequiredEL, ctx['els'])
        assert (self.map_name_id[self.package][ctx['condition']['use']])  # flag must exists
        use = get_smt_use(self.map_name_id, self.package, ctx['condition']['use'])
        if 'not' in ctx['condition']:
            return smt.If(smt.Not(use),smt.And(formulas))
        return smt.If(use,smt.And(formulas))

    def visitRequiredCHOICE(self, ctx):
        formulas = map(self.visitRequiredEL, ctx['els'])
        if ctx["choice"]["type"] == "or":
            return smt.Or(formulas)
        elif ctx["choice"]["type"] == "one-max":
            if len(formulas) > 2:
                return get_no_two_true_expressions(formulas)
            else:
                return smt.TRUE()
        elif ctx["choice"]["type"] == "xor":
            if len(formulas) > 1:
                return smt.And(smt.Or(formulas),get_no_two_true_expressions(formulas))
            elif len(formulas) == 1:
                return formulas[0]
            return smt.FALSE() # no formula to be satisified

    def visitRequiredINNER(self, ctx):
        return smt.And([map(self.mapvisitRequiredEL, ctx['els'])])

    def visitDepend(self, ctx):
        return smt.And(map(self.visitDependEL, ctx))

    def visitDependSIMPLE(self, ctx):
        formula = self.visitAtom(ctx['atom'])
        if "not" in ctx:
            return smt.Not(formula)
        return formula

    def visitDependCONDITION(self, ctx):
        formulas = map(self.visitDependEL, ctx['els'])
        assert (self.map_name_id[self.package][ctx['condition']['use']])  # flag must exists
        use = get_smt_use(self.map_name_id, self.package, ctx['condition']['use'])
        if 'not' in ctx['condition']:
            return smt.If(smt.Not(use),smt.And(formulas))
        return smt.If(use,smt.And(formulas))

    def visitDependCHOICE(self, ctx):
        formulas = map(self.visitDependEL, ctx['els'])
        if ctx["choice"]["type"] == "or":
            return smt.Or(formulas)
        elif ctx["choice"]["type"] == "one-max":
            if len(formulas) > 2:
                return get_no_two_true_expressions(formulas)
            else:
                return smt.TRUE()
        elif ctx["choice"]["type"] == "xor":
            if len(formulas) > 1:
                return smt.And(smt.Or(formulas),get_no_two_true_expressions(formulas))
            elif len(formulas) == 1:
                return formulas[0]
            return smt.FALSE() # no formula to be satisified

    def visitDependINNER(self, ctx):
        return smt.And([map(self.mapvisitDependEL, ctx['els'])])

    def visitAtom(self, ctx):

        def aux_visit_select(pkgs,sel):
            if sel["use"] in self.mspl[self.package]["declared_uses"]:
                # the package declared the use
                if "prefix" in sel and sel["prefix"]  == "-":
                    if "preference" in sel:
                        if sel["preference"] == "+":
                            return smt.False()
                    else: # preference - or absent
                        return smt.Or(map(lambda x: get_smt_package(self.mspl,x),pkgs))
                else: # prefix + or absent
                    if "preference" in sel:
                        if sel["preference"] == "+":
                            return smt.Or(map(lambda x: get_smt_package(self.mspl,x),pkgs))
                    else: # preference - or absent
                        return smt.False()
            else: # package declared the use
                if "prefix" in sel and sel["prefix"] == "-":
                    return smt.Or(map(lambda x: smt.And(
                        get_smt_package(self.mspl, x),
                        smt.Not(get_smt_use(self.mspl,x,sel["use"]))),pkgs))
                else: # prefix + or absent
                    return smt.Or(map(lambda x: smt.And(
                        get_smt_package(self.mspl, x),
                        get_smt_use(self.mspl, x, sel["use"])), pkgs))

        # todo this function can be made more efficient avoiding to redo previous work for compact atoms
        operator = "="
        if 'version_op' in ctx:
            operator = ctx['version_op']
        slot = ""
        subslot = ""
        if "slots" in ctx:
            if "slot" in ctx["slots"]:
                slot = ctx["slots"]["slot"]
            if "subslot" in ctx["slots"]:
                subslot = ctx["slots"]["subslot"]

        pkgs = get_packages(self.mspl,ctx["package"], operator, slot, subslot)

        # decompact compact forms
        if "selection" in ctx:
            if "type" in ctx: # decompact procedure has not been run yet
                condELs, normal_sels = decompact_atom(ctx)
            else:
                normal_sels = ctx["selection"]
                condELs = []
            formulas = map(self.visitDependCONDITION,condELs)
            formulas.extend(map(lambda x: aux_visit_select(pkgs,x), normal_sels))
            return smt.And(formulas)
        else:
            return smt.Or(map(lambda x: get_smt_package(self.mspl, x), pkgs))

    def visitSlotSTAR(self, ctx):
        return self.DefaultValue()

    def visitSelection(self, ctx):
        res = self.DefaultValue()
        if 'prefix' in ctx:
            res = self.CombineValue(res, self.visitPrefix(ctx['prefix']))
        if 'preference' in ctx:
            res = self.CombineValue(res, self.visitPreference(ctx['preference']))
        if 'suffix' in ctx:
            res = self.CombineValue(res, self.visitSuffix(ctx['suffix']))
        return res
    def visitPrefix(self, ctx):
        return self.DefaultValue()
    def visitPreference(self, ctx):
        return self.DefaultValue()
    def visitSuffix(self, ctx):
        return self.DefaultValue()
    def __mapvisitRequiredEL(self,x,y):
        return self.CombineValue(x, self.visitRequiredEL(y))
    def __mapvisitDependEL(self,x,y):
        return self.CombineValue(x, self.visitDependEL(y))
    def __mapvisitSelection(self,x,y):
        return self.CombineValue(x, self.visitSelection(y))


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
        c = settings.get_hyvar_flag(self.map_name_id["flag"][self.package][flag_name]) + " = 1"
        if ctx.getChildCount() > 1:
            # its a conflict and not a dependency
            # we treat ! and !! in a similar way
            return "not (" + c + ")"
        else:
            return c

    def visitLocalDEPchoice(self, ctx):
        # https://wiki.gentoo.org/wiki/Handbook:Parts/Working/USE#Declaring_temporary_USE_flags
        # for the semantics of the operators

        def get_no_two_true_expressions(xs):
            ys = ["not( " + x + " and " + y + ")" for x in ls for y in ls if x < y]
            return settings.get_hyvar_and(ys)

        choice = ctx.choice().getText()
        ls = []
        for i in range(2,ctx.getChildCount()-1):
            ls.append(ctx.getChild(i).accept(self))
        if choice == "??":
            # with ls(ls) < 2 the constraint is always satisfied -> skipping
            if len(ls) >= 2:
                return get_no_two_true_expressions(ls)
            return "true"
        elif choice == "^^":
            if len(ls) == 1:
                return ls[0]
            elif len(ls) == 2:
                return "( " + ls[0] + " xor " + ls[1] + ")"
            elif len(ls) > 2:
                return settings.get_hyvar_and([get_no_two_true_expressions(ls),settings.get_hyvar_or(ls)])
            return "false" # if ls is empty nothing can be set to true
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
                                " with flags " + unicode(flags) +
                                ". Return false constraint while processing " + self.package)
            if flag_set:
                return flag_representation + " = 1 impl " + c
            else:
                return flag_representation + " = 0 impl " + c

        package = ctx.catpackage().getText().strip()
        version_op = ctx.versionOP()
        if version_op:
            m = re.search(settings.VERSION_RE, package)
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
                                " not found in packages " + package + unicode(packages) +
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




"""
def toSMT2(f, status="unknown", name="benchmark", logic=""):
  v = (z3.Ast * 0)()
  return z3.Z3_benchmark_to_smtlib_string(f.ctx_ref(), name, logic, status, "", 0, v, f.as_ast()).replace(
      "\n"," ").replace("(check-sat)","").replace("; benchmark (set-info :status unknown)","").strip()

def convert(package,target_dir):

    logging.debug("Processing package " + package)
    assert mspl
    if not package in mspl:
        raise Exception("Package " + package + " not found in the MSPL JSON files")

    data = {"attributes": [], "constraints": [], "configures": [],
            "dependencies": []}

    # add "dependencies" and "configures"
    for i in mspl[package]["configures"]:
        if i in mspl:
            data["configures"].append(i)
        else:
            logging.warning("The package " + i + " find in configures is not found. It will be ignored")

    for i in mspl[package]["dependencies"]:
        if i in mspl:
            data["dependencies"].append(i)
        else:
            logging.warning("The package " + i + " find in dependencies is not found. It will be ignored")

    if is_base_package(package):
        data["implementations"] = mspl[package]["implementations"]
        versions = mspl[package]["implementations"].values()
        # if installed then one of its version should be installed as well
        data["constraints"].append(
            settings.get_hyvar_package(map_name_id["package"][package]) +
            " = 1 impl (" +
            settings.get_hyvar_or([settings.get_hyvar_package(map_name_id["package"][i]) + " = 1" for i in versions]) + ")")
        # two versions should have different slots or subslots
        possible_slot_matches = [(i,j,unicode(map_name_id["slot"][i][s]),unicode(map_name_id["slot"][j][s]))
                                 for i in versions for j in versions for s in map_name_id["slot"][i] if
                                 i<j and s in map_name_id["slot"][j]]
        possible_subslot_matches = [(i, j, unicode(map_name_id["subslot"][i][s]),unicode(map_name_id["subslot"][j][s]))
                                    for i in versions for j in versions for s in map_name_id["subslot"][i] if
                                    i < j and s in map_name_id["subslot"][j]]
        for i in versions:
            for j in versions:
                if i < j:
                    slots = [(x[2],x[3]) for x in possible_slot_matches if x[0] == i and x[1] == j]
                    subslots = [(x[2], x[3]) for x in possible_subslot_matches if x[0] == i and x[1] == j]
                    c = settings.get_hyvar_impl(
                            settings.get_hyvar_and(
                                [settings.get_hyvar_package(map_name_id["package"][i]) + "= 1",
                                 settings.get_hyvar_package(map_name_id["package"][j]) + " = 1"]),
                            settings.get_hyvar_impl(
                                settings.get_hyvar_or(
                                    [settings.get_hyvar_slot(map_name_id["package"][i]) + " = " + x[0] + " and " +
                                    settings.get_hyvar_slot(map_name_id["package"][j]) + " = " + x[1] for x in slots]),
                                settings.get_hyvar_or(
                                    [settings.get_hyvar_subslot(map_name_id["package"][i]) + " = " + x[0] + " xor " +
                                    settings.get_hyvar_subslot(map_name_id["package"][j]) + " = " + x[1] for x in subslots])))
                    if c != "true":
                        data["constraints"].append(c)
    else:

        # add slot and subslot as attributes
        assert len(map_name_id["slot"][package]) > 0
        assert len(map_name_id["subslot"][package]) > 0

        data["attributes"].append( {
            "id": settings.get_hyvar_slot(map_name_id["package"][package]),
            "min": 0,
            "max": len(map_name_id["slot"][package]) -1,
            "featureId": settings.get_hyvar_package(map_name_id["package"][package])})

        data["attributes"].append({
            "id": settings.get_hyvar_subslot(map_name_id["package"][package]),
            "min": 0,
            "max": len(map_name_id["subslot"][package]) - 1,
            "featureId": settings.get_hyvar_package(map_name_id["package"][package])})

        # add constraints
        assert "fm" in mspl[package]
        assert "external" in mspl[package]["fm"]
        assert "local" in mspl[package]["fm"]
        visitor = dep_translator.DepVisitor(mspl, map_name_id, package)
        if mspl[package]["fm"]["external"]:
            parser = visitor.parser(mspl[package]["fm"]["external"])
            tree = parser.depend()
            visitor.visit(tree)
        if mspl[package]["fm"]["runtime"] and mspl[package]["fm"]["runtime"] != mspl[package]["fm"]["external"]:
            parser = visitor.parser(mspl[package]["fm"]["runtime"])
            tree = parser.depend()
            visitor.visit(tree)
        if mspl[package]["fm"]["local"]:
            parser = visitor.parser(mspl[package]["fm"]["local"])
            tree = parser.localDEP()
            visitor.visit(tree)
        data["constraints"].extend(visitor.constraints)

        # package with version needs its base package to be selected
        data["constraints"].append(settings.get_hyvar_package(map_name_id["package"][package]) + " = 1 impl 1 = " +
                                settings.get_hyvar_package(map_name_id["package"][re.sub(settings.VERSION_RE,"",package)]))

        # if package is not selected its flags are not selected either
        data["constraints"].append(settings.get_hyvar_impl(
            settings.get_hyvar_package(map_name_id["package"][package]) + " = 0",
            settings.get_hyvar_and([settings.get_hyvar_flag(x) + " = 0" for x in map_name_id["flag"][package].values()])))

        # if flag is selected then its package is selected too
        for i in map_name_id["flag"][package].values():
            data["constraints"].append(settings.get_hyvar_impl(
                settings.get_hyvar_flag(i) + " = 1",
                settings.get_hyvar_package(map_name_id["package"][package]) + " = 1"))

    # add validity formulas. Context must be one of the possible env
    envs = [settings.process_envirnoment_name(x) for x in mspl[package]["environment"]]
    envs = [x for x in envs if not x.startswith("-")]
    if envs:
        if "*" not in envs:
            data["constraints"].append(
                settings.get_hyvar_package(map_name_id["package"][package]) + " = 1 impl (" +
                settings.get_hyvar_or(
                    [settings.get_hyvar_context() + " = " + unicode(map_name_id["context"][x]) for x in envs]) + ")")
    else:
        logging.warning("Environment empty for package " + package + ". This package will be treated as not installable.")
        data["constraints"] = ["false"]

    # if activated, for performance reasons do the encoding directly into z3 smt formulas
    if to_smt:
        features = set()
        ls = []
        for i in data["constraints"]:
            try:
                # logging.debug("Processing " + i)
                d = SpecTranslator.translate_constraint(i, {})
                # other.update(d["contexts"])
                # other.update(d["attributes"])
                features.update(d["features"])
                ls.append(d["formula"])
            except Exception as e:
                logging.error("Parsing failed while converting into SMT " + i + ": " + unicode(e))
                logging.error("Exiting")
                sys.exit(1)
        formula = z3.simplify(z3.And(ls))
        s = toSMT2(formula)
        data["smt_constraints"] = {}
        data["smt_constraints"]["formulas"] = [s]
        data["smt_constraints"]["features"] = list(features)
        # data["smt_constraints"]["other_int_symbols"] = list(other)
        data["constraints"] = []

    logging.debug("Writing file " + os.path.join(target_dir, package + ".json"))
    d = package.split(settings.PACKAGE_NAME_SEPARATOR)[0]
    try:
        if not os.path.exists(os.path.join(target_dir, d)):
            os.makedirs(os.path.join(target_dir, d))
    except OSError, e:
        if e.errno != 17:
            raise
        # if e.errno == 17 another thread already created the directory (race condition)
    with open(os.path.join(target_dir, package + ".json"), 'w') as f:
        json.dump(data, f, indent=1)
    return True

# worker for a thread
def worker(pair):
    pkg,target_dir = pair
    convert(pkg,target_dir)
    return True


    logging.info("Load the MSPL. This may take a while")
    load_mspl(os.path.join(input_dir,'mspl'))
    logging.info("Load the SPL. This may take a while")
    load_spl(os.path.join(input_dir,os.path.join('catalog','spl')))

    if os.path.isfile(os.path.join(target_dir,settings.NAME_MAP_FILE)):
        logging.info("Use the exising " + settings.NAME_MAP_FILE + " file. No computation of new ids")
        data = read_json(os.path.join(target_dir,settings.NAME_MAP_FILE))
        map_name_id = data["name_to_id"]
        map_id_name = data["id_to_name"]
    else:
        logging.info("Generate the name maps for packages and stores in a file")
        generate_name_mapping_file(target_dir)

    logging.info("Start converting files of the MSPL. Skipping existing ones")

    if translate_only:
        convert(translate_only, target_dir)
    else:
        to_convert = [x for x in spl.keys() if not os.path.isfile(os.path.join(target_dir,x+".json"))]
        # if more than one thread is used python goes into segmentation fault
        logging.info("Starting to convert packages using " + unicode(available_cores) + " processes.")
        logging.info("Number of packages to convert: " + unicode(len(to_convert)))

        pool = multiprocessing.Pool(available_cores)
        pool.map(worker,[(x,target_dir) for x in to_convert])
    logging.info("Execution terminated.")
"""