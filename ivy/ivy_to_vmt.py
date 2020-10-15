import sys

import ivy_logic
import ivy_utils as iu
import ivy_actions as ia
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
from collections import defaultdict

outF = sys.stdout
def fprint(s):
    global outF
    outF.write(s + "\n")

#for cls in [lg.Eq, lg.Not, lg.And, lg.Or, lg.Implies, lg.Iff, lg.Ite, lg.ForAll, lg.Exists,
#            lg.Apply, lg.Var, lg.Const, lg.Lambda, lg.NamedBinder, lg.EnumeratedSort, lg.Const]:
#    if hasattr(cls,'__vmt__'):
#        cls.__str__ = cls.__vmt__

class print_module_vmt():
    def __init__(self, mod, inst):
        self.instance = {}
        self.concretizations = []
        self.used = set()
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
        self.prestr = {}
        self.nexstr = {}
        self.prenexstr = {}
        self.vmt = {}
        self.axioms = []
        self.prefix = "__"
        self.read_instance(open(inst, 'r'))
        self.execute()

    def read_instance(self, fi):
        n = eval(fi.readline())
        for i in range(n):
            st = fi.readline().split('=')
            self.instance[st[0]] = eval(st[1])
        assert fi.readline() == '\n'
        n = eval(fi.readline())
        for i in range(n):
            st = fi.readline()[:-1]
            self.concretizations.append(st)
            s = st.split('=')
            if len(s) == 2:
                self.axioms.append('(= %s %s)' % (s[0], s[1]))
            else:
                self.axioms.append("(= %s bv_true)" % (s[0]))

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
            print >> sys.stderr, "sig.interp: %s" % str(self.mod.sig.interp)
#            assert(0)

        if len(self.mod.definitions) != 0:
#             print("definitions: %s" % str(self.mod.definitions))
            for defn in self.mod.definitions:
                self.definitions.add(defn)
            self.mod.definitions = []

        with self.mod.theory_context():
            print >>sys.stderr, 'sig'
            self.process_sig()
            print >>sys.stderr, 'defs'
            self.process_defs()
            print >>sys.stderr, 'conj'
            self.process_conj()
            print >>sys.stderr, 'axiom'
            self.process_axiom()
            print >>sys.stderr, 'init'
            self.process_init()
            print >>sys.stderr, 'actions'
            self.process_actions()
            print >>sys.stderr, 'done'
#            self.process_guarantee()
    
            self.print_vmt()
            self.print_config()
    
    def print_vmt(self):
        fprint(
'''(set-info :source |Haojun Ma (mahaojun@umich.edu)|)

; Typecast bit to bool
(define-sort bool_type () (_ BitVec 1)) 
(define-fun bv_false () bool_type (_ bv0 1)) 
(define-fun bv_true  () bool_type (_ bv1 1)) 
(define-fun is_bool ((x bool_type)) Bool (or (= x bv_true) (= x bv_false)))

; Define and enumerate transition system parameters'''
)
        for s, v in self.sorts.iteritems():
            fprint('(define-sort %s_type () (_ BitVec %d))' % (s, v))
            for i in range(self.instance[s]):
                fprint('(define-fun %s%d () %s_type (_ bv%d %d))' % (s, i, s, i, v))
            fprint('(define-fun is_%s ((%s %s_type)) Bool (or %s))'%(s, s, s, ' '.join(["(= %s %s%d)" % (s, s, i) for i in range(self.instance[s])])))
        fprint("\n; Declare transition system states")
        for pre in self.pre:
            fprint(self.prestr[pre.get_vmt()])
        fprint("\n; Declare next states")
        for pre in self.pre:
            nex = self.pre2nex[pre]
            fprint(self.nexstr[nex.get_vmt()])
        fprint("")
        for pre in self.pre:
            nex = self.pre2nex[pre]
            fprint(self.prenexstr[pre.get_vmt() + nex.get_vmt()])
# no global
#        if len(self.glo) != 0:
#            fprint("")
#            for g in self.glo:
#                fprint(self.str[str(g)])
#            fprint("")
#            for g in self.glo:
#                pre = self.nex2pre[g]
#                fprint(self.str[str(pre)+str(g)])
        if len(self.vars) != 0:
            fprint("\n; Declare local variables")
            for v in self.vars:
                fprint(self.nexstr[v.get_vmt()])
#        for h in self.defn_labels:
#            fprint("")
#            fprint(self.get_vmt_string_def(h))
#            fprint(self.get_vmt_string(h))
        fprint("\n; Safety property")
        fprint(self.get_vmt_string("$prop"))
        fprint("\n; Declare axioms")
        if len(self.mod.labeled_axioms) != 0:
            f, name, suffix, value = self.vmt["$axiom"]
            fprint('(define-fun my_axioms () Bool\n(and %s\n%s)\n)' % (f.instantiation(self.instance, {}), ' '.join(self.axioms)))
        else:
            fprint('(define-fun my_axioms () Bool\n(and true\n%s)\n)' % (' '.join(self.axioms)))
        fprint("\n; Declare initial states")
        fprint(self.get_vmt_string("$init"))
        fprint("\n; Declare actions")
        for actname in self.actions:
            fprint("")
            fprint(self.vmt[actname])
            fprint("")
        copies = []
        for var in self.nex:
            copies += self.copy_constant(var)
        fprint("(define-fun .trans () Bool (! (and (or %s \n(and %s))\n my_axioms) \n:trans true))"%(' '.join(self.actions), ' '.join(copies)))
#        for h in sorted(self.helpers.keys()):
#            fprint(self.get_vmt_string(h))
#            fprint("")
        
    def print_config(self):
        fo = open('config.txt', 'w')
        if ivy_compiler.isolate.get():
            st = sys.argv[1].split("_")
            print>>fo, '_'.join(st[:-1])
            print>>fo, 'isolate=%s' % ivy_compiler.isolate.get()
        else:
            st = sys.argv[1].replace(".ivy", '')
            print>>fo, st
        print>>fo
        
        print >>fo, len(self.pre)
        for pre in self.pre:
            var = self.pre2nex[pre]
            if isinstance(var.sort, UnionSort):
                sort = var.sort.sorts[0]
            else:
                sort = var.sort
            if sort.dom:
                st = "%d %s %s %s" % (len(sort.dom), sort.rng.get_vmt().upper(), var.name, ' '.join([s.get_vmt().upper() for s in sort.dom]))
            else:
                st = "0 %s %s" % (sort.name.upper(), var.name)
            print >>fo, st

        print >>fo
        print >>fo, len(self.sorts)
        for k in self.sorts:
            print >> fo, k.upper(), self.sorts[k]
        print >>fo
        print >>fo, len(self.concretizations)
        for k in self.concretizations:
            print >>fo, k
        
    def process_sig(self):
        for name,sort in ivy_logic.sig.sorts.iteritems():
            if name == 'bool':
                continue
            if isinstance(sort, lg.EnumeratedSort):
                print >> sys.stderr, 'enumerated sort', sort.get_vmt(), type(sort)
                n = len(sort.extension)
                self.instance[name] = n
                for i in range(n):
                    for j in range(i):
                        if sort.extension[i] in ivy_logic.sig.symbols and sort.extension[j] in ivy_logic.sig.symbols:
                            self.axioms.append('(not (= %s_%s %s_%s))'% (sort.name, sort.extension[i], sort.name, sort.extension[j]))
            elif not isinstance(sort,UninterpretedSort):
                print >> sys.stderr, 'not uninterpreted sort', sort.get_vmt(), type(sort), isinstance(sort, lg.EnumeratedSort)
                assert False, "todo"
            for i in range(2, 32):
                if 2**i >= self.instance[name] and i not in self.used:
                    break
            self.used.add(i)
            self.sorts[name] = i

#        print >>sys.stderr, ivy_logic.sig.symbols
        for name,sym in ivy_logic.sig.symbols.iteritems():
#            print name, sym.sort
            if isinstance(sym.sort,UnionSort):
                print >> sys.stderr, "UnionSort", sym, sym.sort

                for s in sym.sort.sorts:
                    sym = lg.Const(sym.name, s)
                    psym = sym.prefix('__')
                    nsym = sym
                    self.pre.add(psym)
                    self.nex.add(nsym)
                    self.pre2nex[psym] = nsym
                    self.nex2pre[nsym] = psym
                    self.allvars.add(psym)
                    self.allvars.add(nsym)
            
                    self.add_constant(sym, True)
            else:
                psym = sym.prefix('__')
                nsym = sym
                self.pre.add(psym)
                self.nex.add(nsym)
                self.pre2nex[psym] = nsym
                self.nex2pre[nsym] = psym
                self.allvars.add(psym)
                self.allvars.add(nsym)
            
                self.add_constant(sym, True)
    
    def process_defs(self):
        for lf in self.definitions:
            sym = lf.formula.defines()
            print >> sys.stderr, "def!", sym
            print >> sys.stderr, lf
            continue
            assert False, "TODO"
            label = "def_" + str(sym)
            lhs = lf.formula.lhs()
            rhs = lf.formula.rhs()
            self.add_new_constants(rhs)

            args = {}
            vargs = []
            print lhs, rhs
#            if isinstance(lhs, lg.Apply):
#                for arg in lhs.terms:
#                    name = "V" + str(len(vargs))
#                    varg = lg.Var(name, arg.sort)
#                    args[arg] = varg
#                    vargs.append(varg)
#                print args
#                lhs = lgu.substitute(lhs, args)
#                rhs = lgu.substitute(rhs, args)
            f = lg.Eq(lhs, rhs)
            print f
#            exit()
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
        fmlas = [lf.formula for lf in self.mod.labeled_conjs]
        cl = lut.Clauses(fmlas)
        f = self.get_formula(cl)
        pref = lgu.substitute(f, self.nex2pre)
        self.add_new_constants(pref, True)
        pref = lgu.substitute(pref, self.nex2pre)
        res = (pref, "prop", "invar-property", "0")
        self.vmt["$prop"] = res
        
    def process_axiom(self):
        fmlas = [lf.formula for lf in self.mod.labeled_axioms]
        cl = lut.Clauses(fmlas)
        f = self.get_formula(cl)
        print >> sys.stderr, f
        self.add_new_constants(f, True)
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
        while len(init_cl) > 1:
            if init_cl[0] == init_cl[1]:
                init_cl = init_cl[1:]
        clauses = lut.and_clauses(*init_cl)
#        print >> sys.stderr, clauses
        f = self.get_formula(clauses)
        pref = lgu.substitute(f, self.nex2pre)
        self.add_new_constants(pref, True)
        pref = lgu.substitute(f, self.nex2pre)
        res = (pref, "init", "init", "true")
        self.vmt["$init"] = res
        
    def process_actions(self):
#        print self.mod.public_actions
        st = ivy_compiler.isolate.get().split('.')[0]
        st = [st, 'timeout', 'handle', 'recv']
        for name in self.mod.public_actions:
            print >>sys.stderr, name
            if ivy_compiler.isolate.get() == None or any(s in name for s in st):
                action = ia.env_action(name)
#            print "action2: ", ia.action_def_to_str(name, action)
                ag = ivy_art.AnalysisGraph()
                pre = itp.State()
                pre.clauses = lut.true_clauses()
                with itp.EvalContext(check=False):
                    post = ag.execute(action, pre)
                history = ag.get_history(post)
                clauses = lut.and_clauses(history.post)
                f = self.get_formula(clauses)
#                print >>sys.stderr, name, f
                conjuncts = clauses.fmlas
                defn = lut.close_epr(lg.And(*conjuncts))
#             print(defn)
#             assert(0)
            
                update = action.update(pre.domain,pre.in_scope)
                sf = self.standardize_action(f, update[0], name)
#            print >> sys.stderr, sf

                copies = []
                for var in self.nex:
                    if var not in update[0]:
                        copies += self.copy_constant(var)
                self.add_new_constants(sf)
            
                actname = ("action_" + name).replace(":", "_")
                self.actions.add(actname)
#            print 'result: ', res
                self.vmt[actname] = ("(define-fun %s () Bool \n(and %s\n%s)\n)" % (actname, sf.instantiation(self.instance, {}), ' '.join(copies))).replace(":", "_")

    def process_guarantee(self):
        callgraph = defaultdict(list)
        for actname,action in self.mod.actions.iteritems():
            for called_name in action.iter_calls():
                callgraph[called_name].append(actname)
        for actname,action in self.mod.actions.iteritems():
            guarantees = [sub for sub in action.iter_subactions() if isinstance(sub, (ia.AssertAction, ia.Ranking))]
            if guarantees:
                callers = callgraph[actname]
                roots = set(iu.reachable([actname], lambda x: callgraph[x]))
                for sub in guarantees:
                    for root in roots:
                        if root in self.mod.public_actions:
                            action = ia.env_action(root)
                            ag = ivy_art.AnalysisGraph()
                            pre = itp.State()
                            pre.clauses = lut.true_clauses()
                            post = ag.execute(action,prestate=pre)
                            fail = itp.State(expr = itp.fail_expr(post.expr))
                            print post
                            print fail
        exit(0)

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
#        print >>sys.stderr, subs
        if len(subs) == 0:
            return f
        else:
#            for k, v in subs.iteritems():
#                 print("\treplacing %s -> %s in %s" % (k, v, name))
            return lgu.substitute(f, subs)
  
    def add_new_constants(self, f, addPre = False):
        cons = lgu.used_constants(f)
        for c in cons:
            if c not in self.allvars and c.name != '>' and c.name != '>=' and c.name != '<=':
                print >> sys.stderr, "local variable %s" % (c.name)
                if addPre:
                    psym = c.prefix("__")
                    nsym = c
                    self.pre.add(psym)
                    self.nex.add(nsym)
                    self.pre2nex[psym] = nsym
                    self.nex2pre[nsym] = psym
                    self.allvars.add(psym)
                    self.allvars.add(nsym)
                    print >> sys.stderr, '???', c, c.sort
                else:
                    self.vars.add(c)
                    self.allvars.add(c)
                    nsym = c

                self.add_constant(nsym, addPre)
                
    def add_constant(self, sym, addPre):   
        if isinstance(sym.sort, UnionSort):
            sort = sym.sort.sorts[0]
        else:
            sort = sym.sort
        name = sym.get_vmt()
        names = [name.replace(":", "_")]
        if sort.dom:
            for s in sort.dom:
                tmp = []
                for i in range(self.instance[s.get_vmt()]):
                    tmp += ['%s%d_%s'%(s.get_vmt(), i, n) for n in names]
                names = tmp
        st = '(declare-fun %s ()'
        if not sort.is_relational():
            st += ' {}_type)'.format(sort.rng.get_vmt())
            self.axioms += ["(is_%s %s)" % (sort.rng.get_vmt(), n) for n in names]
        else:
            st += ' bool_type)'

        self.nexstr[name] = '\n'.join([st%(n) for n in names])
#        print name
#        print self.str[name]
        
        if addPre:
            psym = self.nex2pre[sym]
            prename = psym.get_vmt()
            prenames = [prename.replace(":", '_')]
            if sort.dom:
                for s in sort.dom:
                    tmp = []
                    for i in range(self.instance[s.get_vmt()]):
                        tmp += ['%s%d_%s'%(s.get_vmt(), i, n) for n in prenames]
                    prenames = tmp
            self.prestr[prename] = '\n'.join([st%(n) for n in prenames])
            
            prenex = '(define-fun .%s ()'
            if not sort.is_relational():
                prenex += ' {}_type'.format(sort.rng.get_vmt())
            else:
                prenex += ' bool_type'
            prenex += ' (! %s :next %s))'
            self.prenexstr[prename+name] = '\n'.join([prenex%(n1, n1, n2) for n1, n2 in zip(prenames, names)])
#            print prename, self.str[prename]
#            print prename+name, self.str[prename+name]

    def copy_constant(self, sym):
        ret = []
        psym = self.nex2pre[sym]
        names = [sym.get_vmt().replace(":", "_")]
        prenames = [psym.get_vmt().replace(":", "_")]
        if isinstance(sym.sort, UnionSort):
            sort = sym.sort.sorts[0]
        else:
            sort = sym.sort
        if sort.dom:
            for s in sort.dom:
                tmp    = []
                pretmp = []
                for i in range(self.instance[s.get_vmt()]):
                    tmp    += ['%s%d_%s'%(s.get_vmt(), i, n) for n in names]
                    pretmp += ['%s%d_%s'%(s.get_vmt(), i, n) for n in prenames]
                names = tmp
                prenames = pretmp
        return ["(= %s %s)" % (name, prename) for name, prename in zip(names, prenames)]
            
    def get_formula(self, clauses):
        cl = lut.and_clauses(clauses)
        f = cl.to_formula()
        rep = {}
        for c in f:
            if isinstance(c, lg.Eq) or isinstance(c, lg.Iff):
#                print >>sys.stderr, 'here!!', type(c.t1), type(c.t2)
#                print >>sys.stderr, c
                for st in ['fml:', 'loc:', 'ts0_']:
                    if isinstance(c.t1, lg.Const) and st in c.t1.name and (c.t1 not in rep or rep[c.t1] == c.t1):
                        if c.t2 in rep:
                            rep[c.t1] = rep[c.t2]
                            break
                        else:
                            rep[c.t1] = c.t2
                            break
                    elif isinstance(c.t2, lg.Const) and st in c.t2.name and (c.t2 not in rep or rep[c.t2] == c.t2):
                        if c.t1 in rep:
                            rep[c.t2] = rep[c.t1]
                            break
                        else:
                            rep[c.t2] = c.t1
                            break
#        print >>sys.stderr, rep
#        print >>sys.stderr, f
        return lgu.substitute(f, rep)
        return f
    
    def get_vmt_string(self, k):
        f, name, suffix, value = self.vmt[k]
        res = '(define-fun .' + name + ' () Bool (! \n'
        res += f.instantiation(self.instance, {}).replace(":", "_")
        res += '\n :' + suffix + ' ' + value + '))'
        return res
    
#    def get_vmt_string_def(self, k):
#        f, name, prenex, value = self.vmt[k]
#        
#        res = prenex
#        res += ' ' + str(f)
#        res += '\n)'
#        return res
    
    def print_sort_size(self, name, sz):
        res = ''
        res += '(define-fun .{} ((S {})) {} (! S :sort '.format(name, name, name)
        res += '{}))'.format(sz)
        fprint(res)
    

def print_isolate(inst):
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
    print_module_vmt(mod, inst)

def print_module(inst):
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
                print >> sys.stderr, "\nPrinting isolate {}:".format(isolate)
        with im.module.copy():
            ivy_isolate.create_isolate(isolate) # ,ext='ext'
            print_isolate(inst)

def usage():
    print >> sys.stderr, "usage: \n  {} file.ivy instance_specification".format(sys.argv[0])
    sys.exit(1)


def main():
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
            print_module(sys.argv[2])
    print >> sys.stderr, "OK"


if __name__ == "__main__":
    main()

