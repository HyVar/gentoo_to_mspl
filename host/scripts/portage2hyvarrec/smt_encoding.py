######################################################################
### FUNCTIONS FOR MSPL TRANSLATION
### Assumes that the compact form have been already decompacted
######################################################################

import re
import constraint_ast_visitor
import utils
import logging
import z3


# function to encode SMT expression into SMTLIB
def toSMT2(f, status="unknown", name="benchmark", logic=""):
  v = (z3.Ast * 0)()
  return z3.Z3_benchmark_to_smtlib_string(f.ctx_ref(), name, logic, status, "", 0, v, f.as_ast()).replace(
      "\n"," ").replace("(check-sat)","").replace("; benchmark (set-info :status unknown)","").strip()


def match_version(template, operator, p_name):
    """
    Check if a version package s (a string) matches a template
    Note that s and template need to have the same base package
    """
    if operator == "~":
        return match_version(template + "-r*", "=", p_name) or match_version(template, "=", p_name)
    if operator == "=":
        # update re special chars in the template
        template = re.sub('\+', '\\\+', template)
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
        raise Exception("Operator " + unicode(operator) + " not supported for package version comparison")


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

    no_star_template = re.sub('\*','',template) # star messes up with get_base_package regular expression
    base_pkg = utils.get_base_package(data,no_star_template)
    if base_pkg and base_pkg in data:
        ls = [x for x in data[base_pkg]["implementations"].values() if match_version(template,operator,x)]
        if slot:
            ls = [x for x in ls if match_slot(data,slot,x)]
        if subslot:
            ls = [x for x in ls if match_subslot(data,subslot,x)]
        return ls
    else:
        logging.warning("A dependency is looking for " + operator + template + " but no package " +
                        base_pkg + " has been found.")
    return []

##############################################
# auxiliary functions
##############################################

def get_smt_package(map_name_id,p_name):
    return z3.Bool("p" + map_name_id["package"][p_name])

def get_hyvar_pakcage(map_name_id,p_name):
    return "feature[p" + map_name_id["package"][p_name] + "]"

def get_smt_packages(map_name_id,pkgs):
    return map(lambda x: get_smt_package(map_name_id,x),pkgs)

def get_smt_use(map_name_id,p_name,u_name):
    return z3.Bool("u" + map_name_id["flag"][p_name][u_name])

def get_hyvar_use(map_name_id,p_name,u_name):
    return "feature[u" + map_name_id["flag"][p_name][u_name]+ "]"

def get_smt_context():
    return z3.Int(utils.CONTEXT_VAR_NAME)

def get_no_two_true_expressions(fs):
    return z3.And([z3.Not(z3.And(fs[i], fs[j])) for i in range(len(fs)) for j in range(len(fs)) if i < j])


def decompact_atom(ctx):

    def get_use(ctx,prefix=""):
        use = {"use": ctx["use"]}
        if prefix:
            use['prefix'] = prefix
        if "preference" in ctx:
            use["preference"] = ctx["preference"]
        return use

    def get_dcondition(ctx,use):
        new_ctx = {
            'type': "dcondition",
            'condition': get_use(use),
            'els': [{'type': "dsimple", 'atom': {x: ctx[x] for x in ctx if x != "selection"}}]}
        new_ctx['els'][0]['atom']['decompacted'] = ""
        return new_ctx

    # decompact the comapct atoms
    assert "selection" in ctx
    condELs = []
    normal_sels = []
    for i in ctx["selection"]:
        if "prefix" in i and i["prefix"] == "!":
            if "suffix" in i:
                if i["suffix"] == "?":
                    # app - misc / foo[!bar?]    bar? (app - misc / foo) !bar? (app - misc / foo[-bar])
                    first = get_dcondition(ctx,i)
                    second = get_dcondition(ctx,i)
                    second["condition"]["not"] = ""
                    second["els"][0]["atom"]["selection"] = [get_use(i,"-")]
                    condELs.extend([first,second])
                elif i["suffix"] == "=":
                    # app - misc / foo[!bar =]    bar? (app - misc / foo[-bar]) !bar? (app - misc / foo[bar])
                    first = get_dcondition(ctx,i)
                    second = get_dcondition(ctx,i)
                    first["els"][0]["atom"]["selection"] = [get_use(i,"-")]
                    second["els"][0]["atom"]["selection"] = [get_use(i)]
                    second["condition"]["not"] = ""
                    condELs.extend([first,second])
            else:
                raise Exception("Find prefix ! but not suffix ? or = for use " + i["use"])
        elif "suffix" in i:
            if i["suffix"] == "?":
                # app - misc / foo[bar?]    bar? (app - misc / foo[bar]) !bar? (app - misc / foo)
                first = get_dcondition(ctx,i)
                second = get_dcondition(ctx,i)
                first["els"][0]["atom"]["selection"] = [get_use(i)]
                second["condition"]["not"] = ""
                condELs.extend([first, second])
            elif i["suffix"] == "=":
                # app - misc / foo[bar =]    bar? (app - misc / foo[bar]) !bar? (app - misc / foo[-bar])
                first = get_dcondition(ctx,i)
                second = get_dcondition(ctx,i)
                first["els"][0]["atom"]["selection"] = [get_use(i)]
                second["els"][0]["atom"]["selection"] = [get_use(i,"-")]
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
        return z3.And(map(self.visitRequiredEL, ctx))

    def visitRequiredSIMPLE(self, ctx):
        assert ctx["use"] in self.map_name_id["flag"][self.package]
        if "not" in ctx:
            return z3.Not(get_smt_use(self.map_name_id,self.package,ctx["use"]))
        else:
            return get_smt_use(self.map_name_id, self.package, ctx["use"])

    def visitRequiredCONDITION(self, ctx):
        formulas = self.visitRequired(ctx['els'])
        assert (self.map_name_id["flag"][self.package][ctx['condition']['use']])  # flag must exists
        use = get_smt_use(self.map_name_id, self.package, ctx['condition']['use'])
        if 'not' in ctx['condition']:
            return z3.Implies(z3.Not(use),z3.And(formulas))
        return z3.Implies(use,z3.And(formulas))

    def visitRequiredCHOICE(self, ctx):
        formulas = map(self.visitRequiredEL, ctx['els'])
        if ctx["choice"] == "or":
            return z3.Or(formulas)
        elif ctx["choice"] == "one-max":
            if len(formulas) > 2:
                return get_no_two_true_expressions(formulas)
            else:
                return z3.BoolVal(True)
        elif ctx["choice"] == "xor":
            if len(formulas) > 1:
                return z3.And(z3.Or(formulas),get_no_two_true_expressions(formulas))
            elif len(formulas) == 1:
                return formulas[0]
            return z3.BoolVal(False) # no formula to be satisified

    def visitRequiredINNER(self, ctx):
        return z3.And(self.visitRequired(ctx['els']))

    def visitDepend(self, ctx):
        return z3.And(map(self.visitDependEL, ctx))

    def visitDependSIMPLE(self, ctx):
        formula = self.visitAtom(ctx['atom'])
        if "not" in ctx:
            return z3.Not(formula)
        return formula

    def visitDependCONDITION(self, ctx):
        formulas = self.visitDepend(ctx['els'])
        assert self.map_name_id["flag"][self.package][ctx['condition']['use']]  # flag must exists
        use = get_smt_use(self.map_name_id, self.package, ctx['condition']['use'])
        if 'not' in ctx['condition']:
            return z3.Implies(z3.Not(use),z3.And(formulas))
        return z3.Implies(use,z3.And(formulas))

    def visitDependCHOICE(self, ctx):
        formulas = map(self.visitDependEL, ctx['els'])
        if ctx["choice"] == "or":
            return z3.Or(formulas)
        elif ctx["choice"] == "one-max":
            if len(formulas) > 2:
                return get_no_two_true_expressions(formulas)
            else:
                return z3.BoolVal(True)
        elif ctx["choice"] == "xor":
            if len(formulas) > 1:
                return z3.And(z3.Or(formulas),get_no_two_true_expressions(formulas))
            elif len(formulas) == 1:
                return formulas[0]
            return z3.BoolVal(False) # no formula to be satisified

    def visitDependINNER(self, ctx):
        return z3.And(self.visitDepend(ctx['els']))

    def visitAtom(self, ctx):

        def aux_visit_single_pkg_single_select(pkg,sel):
            if sel["use"] not in self.map_name_id["flag"][pkg]:
                # the package considered did not declared the use
                if "prefix" in sel and sel["prefix"] == "-":
                    if "preference" in sel:
                        if sel["preference"] == "+":
                            return z3.BoolVal(False)
                    # preference - or absent
                    return get_smt_package(self.map_name_id,pkg)
                else: # prefix + or absent
                    if "preference" in sel:
                        if sel["preference"] == "+":
                            return get_smt_package(self.map_name_id,pkg)
                    # preference - or absent
                    return z3.BoolVal(False)
            else: # package declared the use
                if "prefix" in sel and sel["prefix"] == "-":
                    return z3.And(
                        get_smt_package(self.map_name_id, pkg),
                        z3.Not(get_smt_use(self.map_name_id,pkg,sel["use"])))
                else: # prefix + or absent
                    return z3.And(
                        get_smt_package(self.map_name_id, pkg),
                        get_smt_use(self.map_name_id, pkg, sel["use"]))

        def aux_visit_select(pkgs,sel):
            return z3.Or([aux_visit_single_pkg_single_select(x,sel) for x in pkgs])

        template = ctx["package"]
        if 'version_op' in ctx:
            operator = ctx['version_op']
            if "times"in ctx:
                template += "*"
        else:
            operator = "="
            template += "*"

        slot = ""
        subslot = ""
        if "slots" in ctx:
            if "slot" in ctx["slots"]:
                slot = ctx["slots"]["slot"]
            if "subslot" in ctx["slots"]:
                subslot = ctx["slots"]["subslot"]

        pkgs = get_packages(self.mspl,template, operator, slot, subslot)

        if pkgs:
            # decompact compact forms
            if "selection" in ctx:
                if not "decompacted" in ctx: # decompact procedure has not been run yet
                    condELs, normal_sels = decompact_atom(ctx)
                else:
                    normal_sels = ctx["selection"]
                    condELs = []
                formulas = [aux_visit_select(pkgs, x) for x in normal_sels]
                formulas.append(self.visitDepend(condELs))
                return z3.And(formulas)
            else:
                return z3.Or(get_smt_packages(self.map_name_id,pkgs))
        else:
            return z3.BoolVal(False)


def convert(input_tuple):
    mspl, map_name_id, simplify_mode, package = input_tuple

    logging.debug("Processing package " + package)

    constraints = []

    if utils.is_base_package(mspl,package):
        versions = mspl[package]["implementations"].values()
        # if installed then one of its version should be installed as well
        constraints.append(z3.Implies(
            get_smt_package(map_name_id,package),
            z3.Or(get_smt_packages(map_name_id,versions))))
        # two versions should have different slots or subslots
        possible_slot_matches = [(i,j) for i in versions for j in versions if i < j
                                 and mspl[i]["slot"] == mspl[i]["slot"]
                                 and mspl[i]["subslot"] == mspl[i]["subslot"]]

        for i,j in possible_slot_matches:
            constraints.append(z3.Not(z3.And(get_smt_package(map_name_id,i),get_smt_package(map_name_id,j))))
    else:
        # add local and combined constraints
        visitor = visitorASTtoSMT(mspl,map_name_id,package)
        for i in map(visitor.visitRequiredEL,mspl[package]["fm"]["local"]):
            constraints.append(z3.Implies(get_smt_package(map_name_id, package),i))
        for i in map(visitor.visitDependEL, mspl[package]["fm"]["combined"]):
            constraints.append(z3.Implies(get_smt_package(map_name_id, package),i))

        # package with version needs its base package to be selected
        constraints.append(z3.Implies(
            get_smt_package(map_name_id, package),
            get_smt_package(map_name_id,mspl[package]['group_name'])))

        # if package is not selected its flags are neither
        constraints.append(z3.Implies(
            z3.Not(get_smt_package(map_name_id, package)),
            z3.And(map(lambda x: z3.Not(get_smt_use(map_name_id,package,x)),map_name_id["flag"][package]))))

        # if flag is selected then its package is selected too
        constraints.append(z3.Implies(
            z3.Or(map(lambda x: get_smt_use(map_name_id,package,x),map_name_id["flag"][package])),
            get_smt_package(map_name_id, package)))


        # add validity formulas. Context must be one of the possible env
        envs = [utils.process_keyword(x) for x in mspl[package]["environment"]]
        envs = [x for x in envs if not x.startswith("-")]
        if envs:
            if "*" not in envs:
                validity_formula = z3.Implies(
                    get_smt_package(map_name_id, package),
                    z3.Or([get_smt_context().__eq__(z3.IntVal(map_name_id["context_int"][x])) for x in envs]))
            else:
                validity_formula = z3.BoolVal(True)
        else:
            logging.warning("Environment empty for package " + package +
                            ". This package will be treated as not installable.")
            validity_formula = z3.BoolVal(False)

        # validity formula added at the end of constraints
        constraints.append(validity_formula)

    if simplify_mode == "default":
        formula = z3.simplify(z3.And(constraints))
        if z3.BoolVal(False) == formula:
            logging.warning("Dependencies in package " + package + " make it uninstallable.")
        return (package,[toSMT2(formula)])
    elif simplify_mode == "individual":
        formulas = []
        for i in constraints:
            formula = z3.simplify(z3.And(i))
            if z3.BoolVal(False) == formula:
                logging.warning("Dependency " + unicode(i) + " in package " + package + " is false." +
                                "Package can not be installed")
            formulas.append(formula)
        return (package,[toSMT2(x) for x in formulas])


def generate_formulas(concurrent_map,mspl,map_name_id,simplify_mode):
    ls = [(mspl, map_name_id, simplify_mode, package) for package in mspl]
    return concurrent_map(convert,ls)