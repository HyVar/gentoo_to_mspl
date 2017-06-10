######################################################################
### FUNCTIONS FOR MSPL TRANSLATION
### Assumes that the compact form have been already decompacted
######################################################################

import re
import constraint_ast_visitor
import utils
import pysmt.shortcuts as smt
import logging

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


def convert(mspl,map_name_id,package):

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
        visitor = visitorASTtoSMT(mspl,map_name_id,package)
        

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