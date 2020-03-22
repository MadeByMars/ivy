import sys

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
from collections import defaultdict

outF = None
def fprint(s):
    global outF
    outF.write(s + "\n")

instance = {}

for cls in [lg.Eq, lg.Not, lg.And, lg.Or, lg.Implies, lg.Iff, lg.Ite, lg.ForAll, lg.Exists,
            lg.Apply, lg.Var, lg.Const, lg.Lambda, lg.NamedBinder, lg.EnumeratedSort, lg.Const]:
    if hasattr(cls,'__vmt__'):
        cls.__str__ = cls.__vmt__

class print_module_vmt():
    def __init__(self, mod):
        global instance
        self.instance = instance
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
        self.str = {}
        self.vmt = {}
        self.axioms = []
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
#            self.process_guarantee()
    
            self.print_vmt()
    
    def print_vmt(self):
        global outF
        outF = sys.stdout
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
            fprint(self.str[str(pre)])
        fprint("\n; Declare next states")
        for pre in self.pre:
            nex = self.pre2nex[pre]
            fprint(self.str[str(nex)])
        fprint("")
        for pre in self.pre:
            nex = self.pre2nex[pre]
            fprint(self.str[str(pre) + str(nex)])
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
                fprint(self.str[str(v)])
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
        
        
    def process_sig(self):
        for name,sort in ivy_logic.sig.sorts.iteritems():
            if name == 'bool':
                continue
            if isinstance(sort, lg.EnumeratedSort):
                print >> sys.stderr, 'enumerated sort', str(sort), type(sort)
                n = len(sort.extension)
                print >> sys.stderr, type(sort.extension[0])
                for i in range(1, n):
                    for j in range(i):
                        print >> sys.stderr, str(sort.extension[i]), type(sort.extension[j])
                        self.axioms.append('(not (= %s_%s %s_%s))'% (sort.name, sort.extension[i], sort.name, sort.extension[j]))
            elif not isinstance(sort,UninterpretedSort):
                print >> sys.stderr, 'not uninterpreted sort', str(sort), type(sort), isinstance(sort, lg.EnumeratedSort)
                assert("todo")
            for i in range(2, 32):
                if 2**i >= instance[name] and i not in self.used:
                    break
            self.used.add(i)
            self.sorts[name] = i
        for name,sym in ivy_logic.sig.symbols.iteritems():
            if isinstance(sym.sort,UnionSort):
                print >> sys.stderr, 'Union sort!', name, sym.sort
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
            print >> sys.stderr, "def!", sym
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
                print >>sys.stderr, "help", lf
                assert False
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
        self.add_new_constants(pref, True)
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
#            for k, v in subs.iteritems():
#                 print("\treplacing %s -> %s in %s" % (k, v, name))
            return lgu.substitute(f, subs)
  
    def add_new_constants(self, f, addPre = False):
        cons = lgu.used_constants(f)
        for c in cons:
            if c not in self.allvars and c.name != '>' and c.name != '>=' and c.name != '<=':
                print >> sys.stderr, "local variable %s" % (c.name)
                if addPre:
                    assert False, "new variable %s in init" % (c.name)
                    psym = c
                    nsym = c.prefix("new_")
                    self.pre.add(psym)
                    self.nex.add(nsym)
                    self.pre2nex[psym] = nsym
                    self.nex2pre[nsym] = psym
                    self.allvars.add(psym)
                    self.allvars.add(nsym)
                else:
                    self.vars.add(c)
                    self.allvars.add(c)
                    nsym = c

                self.add_constant(nsym, addPre)
                
    def add_constant(self, sym, addPre):   
        sort = sym.sort
        name = str(sym)
        names = [name.replace(":", "_")]
        if sort.dom:
            for s in sort.dom:
                tmp = []
                for i in range(self.instance[str(s)]):
                    tmp += ['%s%d_%s'%(s, i, n) for n in names]
                names = tmp

        st = '(declare-fun %s ()'
        if not sort.is_relational():
            st += ' {}_type)'.format(sort.rng)
            self.axioms += ["(is_%s %s)" % (sort.rng, n) for n in names]
        else:
            st += ' bool_type)'

        self.str[name] = '\n'.join([st%(n) for n in names])
#        print name
#        print self.str[name]
        
        if addPre:
            psym = self.nex2pre[sym]
            prename = str(psym)
            prenames = [prename]
            if sort.dom:
                for s in sort.dom:
                    tmp = []
                    for i in range(self.instance[str(s)]):
                        tmp += ['%s%d_%s'%(s, i, n) for n in prenames]
                    prenames = tmp
            self.str[prename] = '\n'.join([st%(n) for n in prenames])
            
            prenex = '(define-fun .%s ()'
            if not sort.is_relational():
                prenex += ' {}_type'.format(sort.rng)
            else:
                prenex += ' bool_type'
            prenex += ' (! %s :next %s))'
            self.str[prename+name] = '\n'.join([prenex%(n1, n1, n2) for n1, n2 in zip(prenames, names)])
#            print prename, self.str[prename]
#            print prename+name, self.str[prename+name]

    def copy_constant(self, sym):
        ret = []
        psym = self.nex2pre[sym]
        names = [str(sym)]
        prenames = [str(psym)]
        if sym.sort.dom:
            for s in sym.sort.dom:
                tmp    = []
                pretmp = []
                for i in range(self.instance[str(s)]):
                    tmp    += ['%s%d_%s'%(s, i, n) for n in names]
                    pretmp += ['%s%d_%s'%(s, i, n) for n in prenames]
                names = tmp
                prenames = pretmp
        return ["(= %s %s)" % (name, prename) for name, prename in zip(names, prenames)]
            
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
        res += f.instantiation(self.instance, {}).replace(":", "_")
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
                print >> sys.stderr, "\nPrinting isolate {}:".format(isolate)
        with im.module.copy():
            ivy_isolate.create_isolate(isolate) # ,ext='ext'
            print_isolate()

def usage():
    print >> sys.stderr, "usage: \n  {} file.ivy output.vmt".format(sys.argv[0])
    sys.exit(1)

def main():
    import signal
    signal.signal(signal.SIGINT,signal.SIG_DFL)
    import ivy_alpha
    ivy_alpha.test_bottom = False # this prevents a useless SAT check
    ivy_init.read_params()
    if len(sys.argv) < 2 or not sys.argv[1].endswith('ivy'):
        usage()
    for i in range(2, len(sys.argv)):
        st = sys.argv[i].split('=')
        instance[st[0]] = eval(st[1])
    with im.Module():
        with utl.ErrorPrinter():
            ivy_init.source_file(sys.argv[1],ivy_init.open_read(sys.argv[1]),create_isolate=False)
            print_module()
    print >> sys.stderr, "OK"


if __name__ == "__main__":
    main()

