from z3 import *

# functions
next = Function('next', IntSort(), IntSort())
prev = Function('prev', IntSort(), IntSort())

fcts = [next, prev]
fct_axioms = [next(-1) == -1, prev(-1) == -1]

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
   elif model[next][x] == -1:
      return True
   else:
      next_val = model[next][x]
      return model[list_fct][next_val]

def dlist_fct(x, model):
   if x == -1:
      return True
   elif model[next][x] == -1:
      return True
   else:
      next_val = model[next][x]
      doubly_linked_cond = model[prev][next_val] == x
      return doubly_linked_cond and model[dlist_fct][next_val]

recdefs = [list_fct, dlist_fct]

# string representation of recursive definition
def recdefToStr(recdef):
   if recdef == list_fct:
      return 'list'
   elif recdef == dlist_fct:
      return 'dlist'
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
      elems_with_nil = elems + [-1]
      fct_eval = [ { fct : { src : tgt } } for tgt in elems_with_nil ]
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
      init[recdef] = curr
   return init

# evaluate model via recdef functions until fixpoint is reached
def evaluateUntilFixpoint(model, prev_model, elems):
   if model == prev_model:
      return model
   new_prev = model.copy()
   for elem in elems:
      for recdef in recdefs:
         new_val = recdef(elem, model)
         model[recdef][elem] = new_val
   return evaluateUntilFixpoint(model, new_prev, elems)

# evaluate recursive definitions on true model
def getRecDefsEval(elems):
   models = getTrueModels(elems)
   evaluated_models = []
   count = 0
   for model in models:
      init_recs = initializeRecDefs(elems)
      model.update(init_recs)
      eval_model = evaluateUntilFixpoint(model, [], elems)
      evaluated_models += [ eval_model ]
   return evaluated_models

print(getFalseModel())
print()

# add offset to true models to avoid non-unique keys
def addOffset(model, f):
   newModel = model.copy()
   for key in fcts + recdefs:
      newDict = {}
      for fctkey in model[key].keys():
         if isinstance(model[key][fctkey], bool) or model[key][fctkey] == -1:
            newDict[f(fctkey)] = model[key][fctkey]
         else:
            newDict[f(fctkey)] = f(model[key][fctkey])
      newModel[key] = newDict
   return newModel

elems = [*range(2)]

models = getRecDefsEval(elems)
for i in range(len(models)):
   models[i] = addOffset(models[i], lambda x: x + 50*(i+1))
   print(models[i])
