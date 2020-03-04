from z3 import *

# functions
next = Function('next', IntSort(), IntSort())
prev = Function('prev', IntSort(), IntSort())

fcts = ['next', 'prev']
fct_axioms = [next(-1) == -1, prev(-1) == -1]

# axioms for next and prev of nil equals nil as python functions -
# for true model generation
def axiomNextNil(model):
   return model['next'][-1] == -1

def axiomPrevNil(model):
   return model['prev'][-1] == -1

vc_axioms  = [axiomNextNil, axiomPrevNil]

# recursive definitions
list = Function('list', IntSort(), BoolSort())
dlist = Function('dlist', IntSort(), BoolSort())

# some general FOL macros
def Iff(b1, b2):
   return And(Implies(b1, b2), Implies(b2, b1))

def IteBool(b, l, r):
    return And(Implies(b, l), Implies(Not(b), r))

# macros for unfolding recursive definitions
def ulist(x):
    return Iff( list(x), IteBool(x == -1, True, list(next(x))))

def udlist(x):
    return Iff( dlist(x), IteBool( x == -1,
                                   True,
                                   IteBool( next(x) == -1,
                                            True,
                                            And(prev(next(x)) == x, dlist(next(x))) ))
   )

recdefs_macros = [ulist, dlist]

# for producing true models: functional versions of recursive definitions
def list_fct(x, model):
   if x == -1:
      return True
   elif model['next'][x] == -1:
      return True
   else:
      next_val = model['next'][x]
      return model['list'][next_val]

def dlist_fct(x, model):
   if x == -1:
      return True
   elif model['next'][x] == -1:
      return True
   else:
      next_val = model['next'][x]
      doubly_linked_cond = model['prev'][next_val] == x
      return doubly_linked_cond and model['dlist'][next_val]

recdefs = [list_fct, dlist_fct]

# string representation of recursive definition
def recdefToStr(recdef):
   if recdef == list_fct:
      return 'list'
   elif recdef == dlist_fct:
      return 'dlist'
   return None

# Z3Py representation of strings (for converting internal model to Z3Py model)
def stringToZ3Fct(string):
   if string == 'list':
      return list
   elif string == 'dlist':
      return dlist
   elif string == 'next':
      return next
   elif string == 'prev':
      return prev
   return None

# VC
def pgm(x, ret):
    return IteBool(x == -1, ret == -1, ret == next(x))

def vc(x, ret):
    return Implies( dlist(x),
                    Implies(pgm(x, ret), list(ret)))

x, ret = Ints('x ret')
deref = [x]
const = [-1]

# TODO: enforce small false model?

# unfold each recursive definition on x
def unfold_recdefs(sol, x):
   for rec in recdefs_macros:
      sol.add(rec(x))

# Get false model - model where VC is false
def getFalseModel():
   sol = Solver()

   # add axioms next(nil) = nil, prev(nil) = nil
   for ax in fct_axioms:
      sol.add(ax)

   # unfold constants
   for c in const:
      unfold_recdefs(sol, c)

   # unfold dereferenced variables
   for d in deref:
      unfold_recdefs(sol, d)

   # negate VC
   sol.add(Not(vc(x, ret)))

   # check satisfiability and print model in format CVC4 can handle 
   sol.check()
   m = sol.model()
   return m.sexpr()

# get false model in dictionary representation
# TODO: generate automatically
def getFalseModelDict():
   false_model = getFalseModel()
   false_model_dict = {'prev': {-1: -1, 0: -1, 1: -1},
                       'next': {-1: -1, 0: 1, 1: -1},
                       'list': {-1: True, 0: False, 1: False},
                       'dlist': {-1: True, 0: True, 1: True}}
   return false_model_dict

# return product of two lists of dictionaries
def product(ll1, ll2):
   out = []
   for x in ll1:
      for y in ll2:
         new_dict = x.copy()
         for key in y.keys():
            if key in new_dict:
               new_dict_key = new_dict[key].copy()
               new_dict_key.update(y[key])
               new_dict[key] = new_dict_key
            else:
               new_dict[key] = y[key]
         out += [new_dict]
   return out

# return product of two lists of lists
def productlist(ll1, ll2):
   return [ x + y for x in ll1 for y in ll2 ]

# generate all possible valuations of all functions at src
def getTrueModelsElem(elems, fcts, src):
   models_elt = [{}]
   for fct in fcts:
      fct_eval = [ { fct : { src : tgt } } for tgt in elems ]
      models_elt = product(fct_eval, models_elt)
   return models_elt

# generate true models in the form of all posible evaluations of all functions
def getTrueModels(elems):
   models = [{}]
   for elem in elems:
      models_elt = getTrueModelsElem(elems, fcts, elem)
      models = product(models, models_elt)
   return models

# initialize dictionary where all recdefs are False for all elements
def initializeRecDefs(elems):
   init = {}
   for recdef in recdefs:
      curr = {}
      for elem in elems:
         curr[elem] = False
      init[recdefToStr(recdef)] = curr
   return init

# evaluate model via recdef functions until fixpoint is reached
def evaluateUntilFixpoint(model, prev_model, elems):
   if model == prev_model:
      return model
   new_prev = model.copy()
   for elem in elems:
      for recdef in recdefs:
         new_val = recdef(elem, model)
         model[recdefToStr(recdef)][elem] = new_val
   return evaluateUntilFixpoint(model, new_prev, elems)

# add constraints from each model into a given solver
def modelToSolver(model, sol):
   for key in model.keys():
      z3key = stringToZ3Fct(key)
      for arg in model[key].keys():
         sol.add(z3key(arg) == model[key][arg])

# return True if given model satisfies all axioms
def filterByAxioms(model):
   axiom_sol = Solver()
   modelToSolver(model, axiom_sol)
   axiom_sol.add(Not(And(fct_axioms)))
   if axiom_sol.check() == unsat:
      return True
   else:
      return False

# evaluate recursive definitions on true model
def getRecDefsEval(elems):
   models = getTrueModels(elems)
   evaluated_models = []
   for model in models:
      init_recs = initializeRecDefs(elems)
      model.update(init_recs)
      eval_model = evaluateUntilFixpoint(model, [], elems)
      if filterByAxioms(eval_model):
         evaluated_models += [ eval_model ]
   return evaluated_models

# add offset to true models to avoid non-unique keys
def addOffset(model, f):
   newModel = model.copy()
   for key in model.keys():
      newDict = {}
      for fctkey in model[key].keys():
         if fctkey == -1:
            if isinstance(model[key][fctkey], bool) or model[key][fctkey] == -1:
               newDict[fctkey] = model[key][fctkey]
            else:
               newDict[fctkey] = f(model[key][fctkey])
         else:
            if isinstance(model[key][fctkey], bool) or model[key][fctkey] == -1:
               newDict[f(fctkey)] = model[key][fctkey]
            else:
               newDict[f(fctkey)] = f(model[key][fctkey])
      newModel[key] = newDict
   return newModel

# get true models with offsets added
def getTrueModelsOffsets(elems):
   models = getRecDefsEval(elems)
   for i in range(len(models)):
      models[i] = addOffset(models[i], lambda x: x + 50*(i+1))
   return models

# generate single model from a given list of models
def sygusBigModelEncoding(models, sol):
   for model in models:
      modelToSolver(model, sol)
   sol.check()
   m = sol.model()
   return m.sexpr()

# generate constraints corresponding to false model for SyGuS
def generateFalseConstraints(model):
   out = '(constraint (or '
   for var in deref:
      out += '(not (lemma ' + str(var) + '))'
   out += '))'
   return out

# generate constraints corresponding to one true model for SyGuS
def generateTrueConstraints(model, elems, f):
   out = ''
   for elem in elems:
      if elem != -1:
         out += '(constraint (lemma ' + str(f(elem)) + '))\n'
   return out

# generate constraints corresponding to all true models for SyGuS
def generateAllTrueConstraints(models, elems):
   out = '(constraint (lemma (- 1)))\n'
   for i in range(len(models)):
      out += generateTrueConstraints(models[i], elems, lambda x: x + 50*(i+1))
   return out

# write output to a file that can be parsed by CVC4 SyGuS
def getSygusOutput():
   elems = [-1, *range(2)]
   true_models = getTrueModelsOffsets(elems)
   false_model = getFalseModelDict()
   all_models = true_models + [ false_model ]
   encoding_sol = Solver()
   sygus_model = sygusBigModelEncoding(all_models, encoding_sol)
   with open('test.sy', 'w') as out, open('preamble.sy', 'r') as preamble, open('grammar.sy', 'r') as grammar:
      for line in preamble:
         out.write(line)
      out.write('\n')
      out.write(sygus_model)
      out.write('\n\n')
      for line in grammar:
         out.write(line)
      out.write('\n')
      out.write(generateFalseConstraints(false_model))
      out.write('\n')
      out.write(generateAllTrueConstraints(true_models, elems))
      out.write('\n')
      out.write('(check-synth)')

getSygusOutput()
