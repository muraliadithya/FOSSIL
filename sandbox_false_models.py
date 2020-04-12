from z3 import *
from lemsynth_utils import *

# Get false model - model where VC is false deref is a list of terms that are
# derefenced. This must be computed prior depending on the depth of instantiation.
# Only unary recursive predicates and axioms supported
def getFalseModel(axioms_z3, lemmas, unfold_recdefs_z3, deref, const, vc):
    sol = Solver()

    # only useful for current implementation. must be distinguished by signature in general
    instantiations = const + deref
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

    # instantiate lemmas
    fresh = Int('fresh')
    for lemma in lemmas:
        for inst in instantiations:
            inst = substitute(lemma, (fresh, inst))
            sol.add(inst)

    # unfold recursive definitions on instantiations
    for key in unfold_recdefs_z3:
        if key != '1_int_bool':
            raise ValueError('Only unary recursive predicates on the foreground sort permitted.')
        else:
            recdefs = unfold_recdefs_z3[key]
            for recdef in recdefs:
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


# Get false model in dictionary representation. Only need values of
# dereferenced variables and constants, nothing else will be used in SyGuS file
# generation.
# TODO - VERY IMPORTANT: the dictionaries' entries are not integers, but Z3 types
#  like IntNumRef and such. Must fix to avoid subtle issues
def getFalseModelDict(fcts_z3, axioms_z3, lemmas, unfold_recdefs_z3, deref, const, vc):
    false_model_z3 = getFalseModel(axioms_z3, lemmas, unfold_recdefs_z3, deref, const, vc)
    if false_model_z3 == None:
        # Lemmas generated up to this point are useful. Exit.
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
        else:
            # only supporting unary functions/recursive definitions
            for fct in fcts_z3[key]:
                fct_name = getZ3FctName(fct)
                false_model_dict[fct_name] = {}
                # TODO: add support for n-ary symbols
                instantiations = const + deref
                for inst in instantiations:
                    inst_value = false_model_z3.eval(inst, model_completion=True)
                    fct_of_inst_value = false_model_z3.eval(fct(inst), model_completion=True)
                    false_model_dict[fct_name][inst_value] = fct_of_inst_value
    return (false_model_z3, false_model_dict)
