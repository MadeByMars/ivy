import sys
#sys.path.insert(0, "/home/rock/ws/version/github/aman_goel/latest/ivy/ivy")

import ivy_logic
import ivy_utils as iu
import ivy_actions as ia
import logic as lg
import ivy_printer as ip

from ivy_logic import UninterpretedSort, UnionSort
import ivy_logic_utils as lut
import ivy_art
import ivy_interp as itp
import logic as lg
import logic_util as lgu
import ivy_init
import ivy_module as im
import ivy_utils as utl
import ivy_compiler
import ivy_isolate
import ivy_ast

outFile = "out.vmt"
outF = None
def fprint(s):
    global outF
    outF.write(s + "\n")

for cls in [lg.Eq, lg.Not, lg.And, lg.Or, lg.Implies, lg.Iff, lg.Ite, lg.ForAll, lg.Exists,
            lg.Apply, lg.Var, lg.Const, lg.Lambda, lg.NamedBinder, lg.EnumeratedSort, lg.Const]:
    if hasattr(cls,'__vmt__'):
        cls.__str__ = cls.__vmt__

class print_module_vmt():
    def __init__(self, mod):
        self.mod = mod
        self.sorts = {}
        self.pre = set()
        self.nex = set()
        self.updated = set()
        self.glo = set()
        self.vars = set()
        self.allvars = set()
        self.nex2pre = {}
        self.pre2nex = {}
        self.actions = set()
        self.helpers = {}
        self.definitions = set()
        self.defn_labels = []
        self.str = {}
        self.vmt = {}
        self.distincts = []
        self.prefix = "__"
        self.execute()

    def execute(self):
        if len(self.mod.labeled_props) != 0:
            print("labeled_props: %s" % str(self.mod.labeled_props))
            assert(0)
        if len(self.mod.labeled_inits) != 0:
            print("labeled_inits: %s" % str(self.mod.labeled_inits))
            assert(0)
        if len(self.mod.native_definitions) != 0:
            print("native_definitions: %s" % str(self.mod.native_definitions))
            assert(0)
        if len(self.mod.sig.interp) != 0:
            print("sig.interp: %s" % str(self.mod.sig.interp))
#            assert(0)

        if len(self.mod.definitions) != 0:
#             print("definitions: %s" % str(self.mod.definitions))
            for defn in self.mod.definitions:
                self.definitions.add(defn)
            self.mod.definitions = []
            
        with self.mod.theory_context():
            self.process_sig()
            self.process_defs()
            self.process_conj()
            self.process_axiom()
            self.process_init()
            self.process_actions()
            self.process_global()
    
            self.print_vmt()
            
    def print_vmt(self):
        global outF, outFile
        outF = open(outFile, 'w')

        for s in self.sorts.keys():
            fprint(self.str[str(s)])
        fprint("")
        for s, v in self.sorts.iteritems():
            self.print_sort_size(str(s), v)
        fprint("")
        for pre in self.pre:
            fprint(self.str[str(pre)])
        fprint("")
        for pre in self.pre:
            nex = self.pre2nex[pre]
            fprint(self.str[str(nex)])
        fprint("")
        for pre in self.pre:
            nex = self.pre2nex[pre]
            fprint(self.str[str(pre) + str(nex)])
        fprint("")
        if len(self.glo) != 0:
            for g in self.glo:
                fprint(self.str[str(g)])
            fprint("")
            for g in self.glo:
                pre = self.nex2pre[g]
#TODO: fix global
                fprint(self.str[str(pre)+str(g)])
            fprint("")
        if len(self.vars) != 0:
            for v in self.vars:
                fprint(self.str[str(v)])
            fprint("")
        for h in self.defn_labels:
#            fprint(self.get_vmt_string_def(h))
            fprint(self.get_vmt_string(h))
            fprint("")
        fprint(self.get_vmt_string("$prop"))
        fprint("")
        if len(self.mod.labeled_axioms) != 0:
            f, name, suffix, value = self.vmt["$axiom"]
            self.vmt["$axiom"] = ("(and %s %s)"%(f, ' '.join(self.distincts)), name, suffix, value)
            fprint(self.get_vmt_string("$axiom"))
            fprint("")
        fprint(self.get_vmt_string("$init"))
        fprint("")
        for actname in self.actions:
            fprint(self.get_vmt_string(actname))
            fprint("")
        for h in sorted(self.helpers.keys()):
            fprint(self.get_vmt_string(h))
            fprint("")
        
    def process_sig(self):
        for name,sort in ivy_logic.sig.sorts.iteritems():
            if name == 'bool':
                continue
            if isinstance(sort, lg.EnumeratedSort):
                print 'enumerated sort', str(sort), type(sort)
                n = len(sort.extension)
                print type(sort.extension[0])
                for i in range(1, n):
                    for j in range(i):
                        print str(sort.extension[i]), type(sort.extension[j])
                        self.distincts.append('(not (= %s_%s %s_%s))'% (sort.name, sort.extension[i], sort.name, sort.extension[j]))
            elif not isinstance(sort,UninterpretedSort):
                print 'not uninterpreted sort', str(sort), type(sort), isinstance(sort, lg.EnumeratedSort)
                assert("todo")
            res = ''
            res += '(declare-sort {} 0)'.format(name)
            self.sorts[sort] = 0
            self.str[str(sort)] = res
        for name,sym in ivy_logic.sig.symbols.iteritems():
            if isinstance(sym.sort,UnionSort):
                print 'Union sort!', name, sym.sort
                continue
                assert("todo")
            psym = sym.prefix('__')
            nsym = sym
            self.pre.add(psym)
            self.nex.add(nsym)
            self.pre2nex[psym] = nsym
            self.nex2pre[nsym] = psym
            self.allvars.add(psym)
            self.allvars.add(nsym)
            
            self.add_constant(sym, True)
    
    def process_defs_v0(self):
        for lf in self.definitions:
            f = lf.formula.to_constraint()
            self.add_new_constants(f)
            label = str(lf.label)
            res = (f, label, "axiom", "true")
            self.vmt[label] = res
            self.defn_labels.append(label)
            
            pref = lgu.substitute(f, self.nex2pre)
            self.add_new_constants(pref)
            label = "__" + str(lf.label)
            res = (pref, label, "axiom", "true")
            self.vmt[label] = res
            self.defn_labels.append(label)
            
    def process_defs(self):
        for lf in self.definitions:
#             print(type(lf.formula))
#             print(lf.formula)
            sym = lf.formula.defines()
            label = "def_" + str(sym)
            lhs = lf.formula.lhs()
            rhs = lf.formula.rhs()
            self.add_new_constants(rhs)
#             args = []
#             if isinstance(lhs, lg.Apply):
#                 for arg in lhs.terms:
#                     args.append(arg)
#             self.add_definition(label, sym, args, rhs)
#             sym = lgu.substitute(sym, self.nex2pre)
#             label = "def_" + str(sym)
#             lhs = lgu.substitute(lf.formula.lhs(), self.nex2pre)
#             rhs = lgu.substitute(lf.formula.rhs(), self.nex2pre)
#             self.add_new_constants(rhs)
#             args = []
#             if isinstance(lhs, lg.Apply):
#                 for arg in lhs.terms:
#                     args.append(arg)
#             self.add_definition(label, sym, args, rhs)
#             self.pre.remove(sym)

            args = {}
            vargs = []
            if isinstance(lhs, lg.Apply):
                for arg in lhs.terms:
                    name = "V" + str(len(vargs))
                    varg = lg.Var(name, arg.sort)
                    args[arg] = varg
                    vargs.append(varg)
                lhs = lgu.substitute(lhs, args)
                rhs = lgu.substitute(rhs, args)
            f = lg.Eq(lhs, rhs)
            if len(vargs) != 0:
                f = lg.ForAll(vargs, f)
            res = (f, label, "definition", str(sym))
            self.vmt[label] = res
            self.defn_labels.append(label)
        
            sym = lgu.substitute(sym, self.nex2pre)
            label = "def_" + str(sym)
            pref = lgu.substitute(f, self.nex2pre)
            res = (pref, label, "definition", str(sym))
            self.vmt[label] = res
            self.defn_labels.append(label)
            
    def process_conj(self):
        fmlas = []
        helpers = []
        for lf in self.mod.labeled_conjs:
            label = str(lf.label)
            if label.startswith("help_"):
                helpers.append(lf)
            else:
                fmlas.append(lf.formula)
        cl = lut.Clauses(fmlas)
        f = self.get_formula(cl)
        pref = lgu.substitute(f, self.nex2pre)
        self.add_new_constants(pref)
        res = (pref, "prop", "invar-property", "0")
        self.vmt["$prop"] = res
        
        for lf in helpers:
            label = str(lf.label)
            self.helpers[label] = lf.formula
            cl = lut.Clauses([lf.formula])
            f = self.get_formula(cl)
            pref = lgu.substitute(f, self.nex2pre)
            self.add_new_constants(pref)
            res = (pref, label, "help", label)
            self.vmt[label] = res
        
    def process_axiom(self):
        fmlas = [lf.formula for lf in self.mod.labeled_axioms]
        cl = lut.Clauses(fmlas)
        f = self.get_formula(cl)
        self.add_new_constants(f)
        res = (f, "axiom", "axiom", "true")
        self.vmt["$axiom"] = res

    def process_init(self):
        init_cl = []
        for name,action in self.mod.initializers:
#             print ("init: ", str(action))
            ag = ivy_art.AnalysisGraph(initializer=lambda x:None)
            history = ag.get_history(ag.states[0])
            post = lut.and_clauses(history.post)
            init_cl.append(post)
        clauses = lut.and_clauses(*init_cl)
        f = self.get_formula(clauses)
        pref = lgu.substitute(f, self.nex2pre)
        self.add_new_constants(pref)
        res = (pref, "init", "init", "true")
        self.vmt["$init"] = res
        
    def process_actions(self):
#        print self.mod.public_actions
        for name in self.mod.public_actions:
            action = ia.env_action(name)
#            print (type(action))
#            print ("action2: ", ia.action_def_to_str(name, action))
            ag = ivy_art.AnalysisGraph()
            pre = itp.State()
            pre.clauses = lut.true_clauses()
#            print(pre.to_formula())
            post = ag.execute(action, pre)
            history = ag.get_history(post)
            clauses = lut.and_clauses(history.post)
            f = self.get_formula(clauses)
            conjuncts = clauses.fmlas
            defn = lut.close_epr(lg.And(*conjuncts))
#             print(defn)
#             assert(0)
            
            update = action.update(pre.domain,pre.in_scope)
            sf = self.standardize_action(f, update[0], name)
            self.add_new_constants(sf)
            
            actname = "action_" + name
            self.actions.add(actname)
            res = (sf, actname, "action", name)
#            print 'result: ', res
            self.vmt[actname] = res

    def process_global(self):
        for n in self.nex:
            if n not in self.updated:
                self.glo.add(n)
        subs = {}
        for n in self.glo:
            p = self.nex2pre[n]
            subs[p] = n
            self.pre.remove(p)
            self.str.pop(str(p))
            self.set_global(n, str(p)+str(n))
#             print("\treplacing %s -> %s globally" % (p, n))
        if len(subs) != 0:
            for k, v in self.vmt.iteritems():
                f, name, suffix, value = v
                newF = lgu.substitute(f, subs)
                self.vmt[k] = (newF, name, suffix, value)
        
    def standardize_action(self, f, nexvars, name):
        nexSet = set()
        for n in nexvars:
            nexSet.add(n)
            self.updated.add(n)

        cons = lgu.used_constants(f)
        subs = dict()
        for c in cons:
            if c in self.nex:
                if c not in nexSet:
                    subs[c] = self.nex2pre[c]
        
        if len(subs) == 0:
            return f
        else:
#             for k, v in subs.iteritems():
#                 print("\treplacing %s -> %s in %s" % (k, v, name))
            return lgu.substitute(f, subs)
  
    def add_new_constants(self, f):
        cons = lgu.used_constants(f)
        for c in cons:
            if c not in self.allvars and c.name != '>' and c.name != '>=' and c.name != '<=':
                self.add_constant(c, False)
                self.vars.add(c)
                self.allvars.add(c)
                
    def add_constant(self, sym, addPre):   
        sort = sym.sort
        name = str(sym)
        prefix = ''
        prefix +=  '(declare-fun '
            
        suffix = ''
        suffix += " ("
        if sort.dom:
            suffix += ' '.join('{}'.format(s) for idx,s in enumerate(sort.dom))
        suffix += ")"
        if not sort.is_relational():
            suffix += ' {}'.format(sort.rng)
        else:
            suffix += ' Bool'
        suffix += ')'
        self.str[name] = prefix + name + suffix
#       print name, self.str[name]
        
        if addPre:
            psym = self.nex2pre[sym]
            prename = str(psym)
            prenex = ''
            prenex +=  '(define-fun '
            prenex +=  '.' + name
            prenex += " ("
            if sort.dom:
                prenex += ' '.join('(V{} {})'.format(idx, s) for idx,s in enumerate(sort.dom))
            prenex += ")"
            if not sort.is_relational():
                prenex += ' {}'.format(sort.rng)
            else:
                prenex += ' Bool'
            prenex += ' (! '
            if sort.dom:
                prenex += '(' + prename + ' '
                prenex += ' '.join('V{}'.format(idx) for idx,s in enumerate(sort.dom))
                prenex += ')'
            else:
                prenex += prename
            prenex += ' :next ' + name + '))'
            self.str[prename] = prefix + prename + suffix
            self.str[prename+name] = prenex
#            print prename, self.str[prename]
#            print prename+name, self.str[prename+name]
            
    def add_definition(self, label, sym, args, rhs):   
        sort = sym.sort
        name = str(sym)

        prenex = ''
        prenex +=  '(define-fun '
        prenex +=  name
        prenex += " ("
        if sort.dom:
            prenex += ' '.join('({} {})'.format(args[idx], s) for idx,s in enumerate(sort.dom))
        prenex += ")"
        if not sort.is_relational():
            prenex += ' {}'.format(sort.rng)
        else:
            prenex += ' Bool'
        prenex += '\n'
        
        res = (rhs, label, prenex, "")
        self.vmt[label] = res
        self.defn_labels.append(label)
            
    def set_global(self, sym, k):
        sort = sym.sort
        name = str(sym)
        
        prenex = ''
        prenex +=  '(define-fun '
        prenex +=  '.' + name
        prenex += " ("
        if sort.dom:
            prenex += ' '.join('(V{} {})'.format(idx, s) for idx,s in enumerate(sort.dom))
        prenex += ")"
        if not sort.is_relational():
            prenex += ' {}'.format(sort.rng)
        else:
            prenex += ' Bool'
        prenex += ' (! '
        if sort.dom:
            prenex += '(' + name + ' '
            prenex += ' '.join('V{}'.format(idx) for idx,s in enumerate(sort.dom))
            prenex += ')'
        else:
            prenex += name
        prenex += ' :global true))'
        self.str[k] = prenex
                    
    def get_formula(self, clauses):
        cl = lut.and_clauses(clauses)
        f = cl.to_formula()
        return f
    
    def get_vmt_string(self, k):
        f, name, suffix, value = self.vmt[k]
        res = '(define-fun .' + name + ' () Bool (! \n'
        res += ' (let (($v '
        res += str(f)
        res += '\n ))\n (and $v))'
        res += '\n :' + suffix + ' ' + value + '))'
        return res
    
    def get_vmt_string_def(self, k):
        f, name, prenex, value = self.vmt[k]
        
        res = prenex
        res += ' ' + str(f)
        res += '\n)'
        return res
    
    def print_sort_size(self, name, sz):
        res = ''
        res += '(define-fun .{} ((S {})) {} (! S :sort '.format(name, name, name)
        res += '{}))'.format(sz)
        fprint(res)
    

def print_isolate():
    temporals = [p for p in im.module.labeled_props if p.temporal]
    mod = im.module
    if temporals:
        if len(temporals) > 1:
            raise IvyError(None,'multiple temporal properties in an isolate not supported yet')
        from ivy_l2s import l2s
        l2s(mod, temporals[0])
        mod.concept_spaces = []
        mod.update_conjs()
#     ifc.check_fragment()
    print_module_vmt(mod)
    with im.module.theory_context():
#         ip.print_module(mod)
        pass
        return

def print_module():
    isolate = ivy_compiler.isolate.get()
    if isolate != None:
        isolates = [isolate]
    else:
        isolates = sorted(list(im.module.isolates))
        if len(isolates) == 0:
            isolates = [None]

    if len(isolates) != 1:
        raise iu.IvyError(None,"Expected exactly one isolate, got %s" % len(isolates))

    for isolate in isolates:
        if isolate != None and isolate in im.module.isolates:
            idef = im.module.isolates[isolate]
            if len(idef.verified()) == 0 or isinstance(idef,ivy_ast.TrustedIsolateDef):
                continue # skip if nothing to verify
        if isolate:
            print "\nPrinting isolate {}:".format(isolate)
        with im.module.copy():
            ivy_isolate.create_isolate(isolate) # ,ext='ext'
            print_isolate()

def usage():
    print "usage: \n  {} file.ivy output.vmt".format(sys.argv[0])
    sys.exit(1)

def main():
    global outFile
    import signal
    signal.signal(signal.SIGINT,signal.SIG_DFL)
    import ivy_alpha
    ivy_alpha.test_bottom = False # this prevents a useless SAT check
    ivy_init.read_params()
    if len(sys.argv) != 3 or not sys.argv[1].endswith('ivy'):
        usage()
    with im.Module():
        with utl.ErrorPrinter():
            ivy_init.source_file(sys.argv[1],ivy_init.open_read(sys.argv[1]),create_isolate=False)
            outFile = sys.argv[2]
            print_module()
    print "OK"


if __name__ == "__main__":
    main()

