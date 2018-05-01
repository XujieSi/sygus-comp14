#!/usr/bin/env python3

import sys

startInt = '''
        (StartInt Int
            (%s
                (+ StartInt StartInt)
                (- StartInt StartInt)
                (* StartInt StartInt)
            )
        )
'''

startBool = '''
        (Start Bool
            (
                (not Start)
                (or Start Start)
                (and Start Start)
                (< StartInt StartInt)
                (<= StartInt StartInt)
                (= StartInt StartInt)
                (> StartInt StartInt)
                (>= StartInt StartInt)
            )
        )
'''

cons_template = '''
(constraint
    (=>
        %s
        %s
    )                                                                             
)                                                                               
'''

class SExp:
    def __init__(self, app, args, src=None):
        if app == '=':
            app = '=='
        self.app = app
        self.args = args
        self.src = src

    def __str__(self):
        return self.show(0)

    def show(self, k):
        if len(self.args) == 0:
            return  "  " * k + self.app
        else:
            indent = "  " * k
            res = indent + "(" + self.app + "\n"
            args = "\n".join( [a.show(k+1) for a in self.args]  )
            res += args
            res += "\n" + indent + ")\n"
            return res

    def collect_stats(self, stats):
        if self.app == '+' or self.app == '-' or self.app == '*' or len(self.args)  == 0:
            return

        if self.app not in stats:
            stats[self.app] = 0
        stats[self.app] += 1
        for a in self.args:
            a.collect_stats(stats)

    def to_str(self):
        if self.app == 'and':
            return "(" + " && ".join( [a.to_str() for a in self.args] ) + ")"
        elif self.app == 'or':
            return "(" + " || ".join( [a.to_str() for a in self.args] ) + ")"
        elif self.app == 'not':
            assert len(self.args) == 1
            return "( !(%s) )" % self.args[0].to_str()
        elif len(self.args) == 0:
            return "(%s)" % self.app
        else:
            #print("debug: ", self.app, self.args)
            assert len(self.args) == 2
            return "(%s %s %s)" % ( self.args[0].to_str(), self.app, self.args[1].to_str() )


    def extract_numbers(self, st):
        if len(self.args) > 0:
            for a in self.args:
                a.extract_numbers(st)
        else:
            if self.app.isdigit() or ( self.app[0] == '-' and self.app[1:].isdigit() ):
                st.add( self.app )



    def to_general_track(self, consts=None):
        if self.app == "declare-primed-var":
            v = self.args[0].app 
            r = "(declare-var " + v +" " + self.args[1].to_general_track() + ")\n"
            r+= "(declare-var " + v +"! " +  self.args[1].to_general_track() + ")\n"
            return r 
        elif self.app == "synth-inv":
            f = self.args[0].app 
            r = "(synth-fun " + f + " "
            r+= "(" + " ".join( [a.to_general_track() for a in self.args[1:] ] ) + ")"
            r+= " Bool\n"

            # add vars
            vars = []
            for a in self.args[1:]:
                vars.append(a.app)

            vars.extend(consts)
            r += "    (\n"
            r += startInt % " ".join(vars)
            r += startBool
            r += "    )\n"
            r += ")\n"
            return r 
        else:
            return self.src


def inv_constraints(vars):
    "inv-f pre-f trans-f post-f    "
    vs = " ".join(vars)
    vs_update = " ".join( [v + "!" for v in vars] )

    pre_f = "(pre-f " + vs + ")"
    inv_f = "(inv-f " + vs + ")"
    trans_f = "(trans-f " + vs + " " + vs_update + ")"
    inv_f_update = "(inv-f " + vs_update + ")"
    post_f = "(post-f " + vs + ")"

    pre_cond = cons_template % (pre_f, inv_f)
    post_cond = cons_template % (inv_f, post_f)

    inv_trans = "(and\n"
    inv_trans += "            " + inv_f + "\n"
    inv_trans += "            " + trans_f + "\n"
    inv_trans += "        )"
    ind_cond = cons_template % (inv_trans, inv_f_update)

    return "\n".join( [pre_cond,ind_cond, post_cond] )


def match_p(s, i):
    L = len(s)
    ct = 0 
    while i < L:
        c = s[i]
        if c == '(':
            ct += 1
        elif c == ')':
            ct -= 1
            if ct == 0:
                return i
        i += 1

    return -1

def parse_sexp(s):
    #print("s:", s)
    vs = s.split()
    if len(vs) == 0:
        return []

    if vs[0][0] == '(':
        s = " ".join(vs)
        vs2 = s[1:].split()
        app = vs2[0]

        #print("app:", app)
        if app.startswith("check-synth"):
            hd = SExp("check-synth",[],"(check-synth)")
            return [hd]

        l = 1 + len(app)
        r = match_p(s, 0)
        assert r>l

        src = s[:r+1]

        res = []
        if app == "define-fun" or app == "synth-inv":
            # get rid of the extra parenthesis
            left = l 
            while left < r:
                if s[left] == '(':
                    break
                left += 1
            right = match_p(s, left)
            tmp = s[:left] + " " + s[left+1:right] + " " + s[right+1:]
            s = tmp


        res.extend( parse_sexp(s[l:r]) )
        hd = SExp(app, res, src)

        res = parse_sexp( s[r+1:] )
        return [hd] + res

    else:
        hd = SExp(vs[0],[], vs[0])
        res = parse_sexp(" ".join(vs[1:]))
        return [hd] + res


def R(fpath):
    with open(fpath, "r") as fin:
        return fin.read()

if len(sys.argv) != 2:
    print("usage: ", sys.argv[0], "a.sl")
    exit()

f = R(sys.argv[1])
res = parse_sexp(f)

consts = set()
for e in res:
    e.extract_numbers(consts)

vars = []
for e in res[:-1]:
    if e.app == "inv-constraint":
        continue

    if e.app == "declare-primed-var":
        vars.append(  e.args[0].app )
    r = e.to_general_track(consts)
    print ( r )

inv_cs = inv_constraints(vars)
print( inv_cs )
print("(check-synth)")
