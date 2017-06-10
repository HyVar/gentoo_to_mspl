######################################################################
### FUNCTIONS FOR MSPL TRANSLATION
### Assumes that the compact form have been already decompacted
######################################################################

import re
import constraint_ast_visitor
import utils
import pysmt.shortcuts as smt
import logging
import pysmt.smtlib.printers

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

def get_smt_packages(map_name_id,pkgs):
    return map(lambda x: get_smt_package(map_name_id,x),pkgs)


def get_smt_use(map_name_id,p_name,u_name):
    return smt.Symbol("u" + map_name_id["flag"]["package"][u_name])

def get_smt_context(map_name_id,c_name):
    return smt.Symbol("u" + map_name_id["context"][c_name])

def get_no_two_true_expressions(fs):
    return smt.And([smt.Not(smt.And(fs[i], fs[j])) for i in range(fs) for j in range(fs) if i < j])


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
        if ctx["choice"] == "or":
            return smt.Or(formulas)
        elif ctx["choice"] == "one-max":
            if len(formulas) > 2:
                return get_no_two_true_expressions(formulas)
            else:
                return smt.TRUE()
        elif ctx["choice"] == "xor":
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
        if ctx["choice"] == "or":
            return smt.Or(formulas)
        elif ctx["choice"] == "one-max":
            if len(formulas) > 2:
                return get_no_two_true_expressions(formulas)
            else:
                return smt.TRUE()
        elif ctx["choice"] == "xor":
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
                        return smt.Or(get_smt_packages(self.map_name_id,pkgs))
                else: # prefix + or absent
                    if "preference" in sel:
                        if sel["preference"] == "+":
                            return smt.Or(get_smt_packages(self.map_name_id,pkgs))
                    else: # preference - or absent
                        return smt.False()
            else: # package declared the use
                if "prefix" in sel and sel["prefix"] == "-":
                    return smt.Or(map(lambda x: smt.And(
                        get_smt_package(self.map_name_id, x),
                        smt.Not(get_smt_use(self.map_name_id,x,sel["use"]))),pkgs))
                else: # prefix + or absent
                    return smt.Or(map(lambda x: smt.And(
                        get_smt_package(self.map_name_id, x),
                        get_smt_use(self.map_name_id, x, sel["use"])), pkgs))

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
            return smt.Or(get_smt_packages(self.map_name_id,pkgs))


def convert(mspl,map_name_id,simplify_mode,package):

    logging.debug("Processing package " + package)

    constraints = []

    if utils.is_base_package(mspl,package):
        versions = mspl[package]["implementations"].values()
        # if installed then one of its version should be installed as well
        constraints.append(smt.Implies(
            get_smt_package(map_name_id,package),
            smt.Or(get_smt_packages(map_name_id,versions))))
        # two versions should have different slots or subslots
        possible_slot_matches = [(i,j) for i in versions for j in versions if i < j
                                 and mspl[i]["slot"] == mspl[i]["slot"]
                                 and mspl[i]["subslot"] == mspl[i]["subslot"]]

        for i,j in possible_slot_matches:
            constraints.append(smt.Not(smt.And(get_smt_package(map_name_id,i),get_smt_package(map_name_id,j))))
    else:
        # add local and combined constraints
        visitor = visitorASTtoSMT(mspl,map_name_id,package)
        for i in map(visitor.visitRequiredEL,mspl["fm"]["local"]):
            constraints.append(smt.Implies(get_smt_package(map_name_id, package),i))
        for i in map(visitor.visitDependEL, mspl["fm"]["combined"]):
            constraints.append(smt.Implies(get_smt_package(map_name_id, package),i))

        # package with version needs its base package to be selected
        constraints.append(smt.Implies(
            get_smt_package(map_name_id, package),
            get_smt_package(map_name_id,mspl[package]['group_name'])))

        # if package is not selected its flags are not selected either
        constraints.append(smt.Implies(
            smt.Not(get_smt_package(map_name_id, package)),
            smt.And(smt.Not(smt.get_smt_packages(map_name_id,map_name_id["flag"][package].keys())))))

        # if flag is selected then its package is selected too
        constraints.append(smt.Implies(
            smt.Or(smt.get_smt_packages(map_name_id, map_name_id["flag"][package].keys())),
            get_smt_package(map_name_id, package)))



    # add validity formulas. Context must be one of the possible env

    envs = [utils.process_keyword(x) for x in mspl[package]["environment"]]
    envs = [x for x in envs if not x.startswith("-")]
    if envs:
        if "*" not in envs:
            validity_formula = smt.Implies(
                get_smt_package(map_name_id, package),
                smt.Or(map(lambda x:get_smt_context(map_name_id,x),envs)))
        else:
            validity_formula = smt.TRUE()
    else:
        logging.warning("Environment empty for package " + package +
                        ". This package will be treated as not installable.")
        validity_formula = smt.FALSE()

    # validity formula added at the end of constraints
    constraints.append(validity_formula)

    if simplify_mode == "default":
        return (package,[pysmt.smtlib.printers.to_smtlib(smt.simplify(smt.And(constraints)))])
    elif simplify_mode == "individual":
        return (package,map(lambda x: pysmt.smtlib.printers.to_smtlib(smt.simplify(x)),constraints))


def generate_formulas(concurrent_map,mspl,map_name_id,simplify_mode):
    return concurrent_map(lambda x: convert(mspl,map_name_id,simplify_mode,x),mspl.keys())