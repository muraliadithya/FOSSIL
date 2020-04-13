from z3 import *
import ast

def getVariables(vc):
    x = Int('x')
    return [x]

def getLHS(vc, z3_str):
    lhs = z3_str['sdlist'](getVariables(vc))
    print(lhs)
    return lhs

def getRHS(vc, z3_str):
    rhs = z3_str['dlist'](getVariables(vc))
    print(rhs)
    return rhs

def makeIP(vc, variables, lhs, rhs, recdefs_macros):
    rec_rho = True # getDef(lhs, recdefs_macros)
    pfp = True
    # pfp = ForAll(variables, Implies(substitute(rec_rho (lhs, rhs)), rhs))
    induction_principle = Implies(pfp, ForAll(variables, Implies(lhs, rhs)))
    return induction_principle

# unfold each recursive definition on x
def unfold_recdefs(sol, recdefs_macros, x):
    for rec in recdefs_macros:
        sol.add(rec(x))

# Get false model - model where VC is false
def proveVC(fct_axioms, z3_str, recdefs_macros, deref, const, vc, ip):
    sol = Solver()

    # add axioms next(nil) = nil, prev(nil) = nil
    for ax in fct_axioms:
        sol.add(ax)

    # unfold constants
    for c in const:
        unfold_recdefs(sol, recdefs_macros, c)

    # unfold dereferenced variables
    for d in deref:
        unfold_recdefs(sol, recdefs_macros, d)

    # negate VC
    sol.add(Not(vc))

    if ip:
        variables = getVariables(vc)
        lhs = vc.args(0)
        print(lhs)
        # lhs = getLHS(vc, z3_str)
        rhs = getRHS(vc, z3_str)
        induction_principle = makeIP(vc, variables, lhs, rhs, recdefs_macros)
        print(induction_principle)
        sol.add(induction_principle)

    # check satisfiability and print model in format CVC4 can handle 
    if (sol.check() == sat):
        m = sol.model()
        return m

    else:
        print("No model available. Lemma was proved.")
