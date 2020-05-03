import sys
import os
from collections import defaultdict
from copy import copy

numbers = set()
replace = {'!': '~', '&&': '&', '==': '='}
for i in range(10):
    numbers.add(str(i))

def add_var(var, dic):
    l = len(var)
    while var[l - 1] in numbers:
        l = l - 1
    if l == len(var):
        return var
    var = var.upper()
    if var not in dic[var[:l]]:
        dic[var[:l]].append(var)
    return var

def parse_var(st, used):
#    print 'parsing', st
    if st[0] == '_':
        st = st[1:]
    st = st.split('_')
    while len(st) > 1 and st[-2][-1] not in numbers:
        st[-2] = "%s_%s" % (st[-2], st[-1])
        st.pop()
    ret = st[-1]
    if len(st) > 1:
        ret += '('
    else:
        ret = add_var(ret, used)
    i = len(st) - 2
    while i >= 0:
        if i > 0:
            ret += add_var(st[i], used) + ', '
        else:
            ret += add_var(st[i], used) + ')'
        i = i - 1
#    print ret
    return ret

def parse(st, used, config):
    ret = ''
    l = 0
    while l < len(st):
        if st[l] == '?':
            print ret
            print st
            exit()
        if st[l] in ['(', ')', '~', ' ', '&']:
            ret += st[l]
            l = l + 1
        elif st[l] == '\t':
            l = l + 1
        else:
            r = l + 1
            while st[r] not in ['(', ')', '~', ' ']:
                r = r + 1
            ret += parse_var(st[l:r], used)
            l = r
    return ret

def comp(dic1, dic2):
    for k in dic1:
        if k not in dic2:
            return False
        for v in dic1[k]:
            if v not in dic2[k]:
                return False
    return True

class Config():
    def __init__(self, fi):
        self.read_relations(fi)
        assert fi.readline() == '\n'
        self.read_sorts(fi)
        assert fi.readline() == '\n'
        self.read_prefix(fi)

    def read_relations(self, fi):
        n = eval(fi.readline())
        self.relations = set()
        self.values = {}
        self.paras = {}
        for i in range(n):
            st = fi.readline().split()
            self.relations.add(st[2])
            self.values[st[2]] = st[1]
            self.paras[st[2]] = st[3:]

    def read_sorts(self, fi):
        n = eval(fi.readline())
        self.sorts = {}
        for i in range(n):
            st = fi.readline().split()
            self.sorts["%s'd" % st[1]] = st[0]

    def read_prefix(self, fi):
        n = eval(fi.readline())
        self.prefix = {}
        for i in range(n):
            st = fi.readline()[:-1].split('=')
            used = defaultdict(list)
            if (len(st) > 1):
                ret = "%s=%s" % (parse_var(st[0], used), parse_var(st[1], used))
            else:
                ret = "%s" % (parse_var(st[0], self.used))
            self.prefix[ret] = used
#        print self.prefix

class Invariant():
    def __init__(self, fi, config):
        self.invs = []
        self.vars = []
        self.config = config
        for st in fi:
            if st != '\n' and st.find('sz:') == -1 and st.find('property') == -1 and 'fml_' not in st:
                st = st[:-1]
                self.parse(st, self.config)
        for i in range(len(self.invs)):
            prefix = []
            for p in config.prefix:
                if comp(config.prefix[p], self.vars[i]):
                    prefix.append(p)
            for t in self.vars[i]:
                for l in range(1, len(self.vars[i][t])):
                    for r in range(l):
                        prefix.append("%s ~= %s" % (self.vars[i][t][r], self.vars[i][t][l]))
            if prefix:
                self.invs[i] = "(%s) -> (%s)" % (' & '.join(prefix), self.invs[i])

    def __str__(self):
        ret = ''
        for i in range(len(self.invs)):
            ret += "invariant [%d] %s\n" % (i, self.invs[i])
        return ret

    def parse(self, st, config):
        var = defaultdict(list)
        st = st.replace('___', '_')
        if st.endswith('&&'):
            st = st[:-2]
        for k in config.sorts:
            st = st.replace(k, config.sorts[k])
        for k in replace:
            st = st.replace(k, replace[k])
        self.invs.append(parse(st, var, config))
        self.vars.append(var)

    def remove(self, i):
        self.invs[i] = 'false -> (%s)' % self.invs[i]

def check(inv, module):
    fi = open(module + '.ivy', 'r')
    fo = open(module + '_inv.ivy', 'w')
    for st in fi:
        fo.write(st)
    fo.write(str(inv))
    fo.close()
    fi.close()
    os.system("ivy_check " + module + "_inv.ivy > log.txt")

    fi = open('log.txt', 'r')
    for st in fi:
        if st.find('FAIL') != -1 and st.find('line') != -1:
            print st
            p = st.find('line')
            p += st[p:].find(':') + 2
            r = st[p:].find(' ')
            fail = eval(st[p:p + r])
            if fail >= 1000000:
                print 'safety failed'
                exit()
            inv.remove(fail)
        if st == 'OK\n':
            return True
    return False

if __name__ == '__main__':
    if len(sys.argv) != 4:
        print 'python main.py module inv config'
        exit()
    config = Config(open(sys.argv[3], 'r'))
    inv = Invariant(open(sys.argv[2], 'r'), config)
    cnt = 1
    while not check(inv, sys.argv[1]):
        print cnt, 'done'
        cnt += 1
        if cnt > 5:
            exit()
    print 'Success!'
