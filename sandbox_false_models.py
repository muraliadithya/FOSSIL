from z3 import *
from lemsynth_utils import *


# # unfold each recursive definition on x
# def unfold_recdefs(sol, recdefs_macros, x):
#     for rec in recdefs_macros:
#         sol.add(rec(x))

# Get false model - model where VC is false
# deref is a list of terms that are derefenced. This must be computed prior depending on the depth of instantiation
## This can be done by knowing prior the terms that appear in the axioms and the recursive definitions,
## and then computing the appriopriate set of terms at the instantiation depth. In general, this will be a dictionary of tuples
## indexed by signature.
# Currently only unary (or 0-ary) recursive predicates and axioms on the location sort are supported. So it is all computed in one loop
def getFalseModel(axioms_z3, unfold_recdefs_z3, deref, const, vc):
    sol = Solver()

    instantiations = const + deref #only useful for current implementation. must be distinguished by signature in general

    for key in axioms_z3.keys():
        signature = getFctSignature(key)
        arity = signature[0]
        if arity == 0:
            for ax in axioms_z3[key]:
                # add axioms like next(nil) = nil, prev(nil) = nil
                sol.add(ax)
        else:
            # Currently not distinguishing by signature
            for ax in axioms_z3[key]:
                for inst in instantiations:
                    sol.add(ax(inst))

    # unfold recursive definitions on instantiations
    for recdef in unfold_recdefs_z3:
        for inst in instantiations:
            sol.add(recdef(inst))

    # negate VC
    sol.add(Not(vc))

    # check satisfiability and print model in format CVC4 can handle
    if (sol.check() == sat):
        m = sol.model()
        return m

    else:
        print("No model available. Lemma was proved.")
        return None


# Get false model in dictionary representation
# Only need to get values of dereferenced variables and constants. Nothing else will be used in SyGuS file generation
## VERY IMPORTANT: the dictioaries' entries are not integers, but Z3 types like IntNumRef and such. Must fix to avoid subtle issues
def getFalseModelDict(fcts_z3, axioms_z3, unfold_recdefs_z3, deref, const, vc):
    false_model_z3 = getFalseModel(axioms_z3, unfold_recdefs_z3, deref, const, vc)
    if false_model_z3 == None:
        #Lemma is correct and useful. Exit.
        exit(0)

    false_model_dict = {}
    for key in fcts_z3.keys():
        signature = getFctSignature(key)
        arity = signature[0]
        if arity == 0:
            # constant symbols
            for fct in fcts_z3[key]:
                fct_name = getZ3FctName(fct)
                false_model_dict[fct_name] = false_model_z3.eval(fct,model_completion=True)
                #print(type(false_model_z3.eval(fct,model_completion=True)))
        else:
            # Currently only supporting unary functions/recursive definitions
            for fct in fcts_z3[key]:
                fct_name = getZ3FctName(fct)
                false_model_dict[fct_name] = {}
                # Need to add support for n-ary symbols. But that requires knowing the instantiations sorted by signature
                instantiations = const + deref
                for inst in instantiations:
                    inst_value = false_model_z3.eval(inst, model_completion=True)
                    fct_of_inst_value = false_model_z3.eval(fct(inst), model_completion=True)
                    false_model_dict[fct_name][inst_value] = fct_of_inst_value
    return (false_model_z3, false_model_dict)