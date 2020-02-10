from z3 import *

sol = Solver()

next = Function('next', IntSort(), IntSort())

list = Function('list', IntSort(), BoolSort())
listlen = Function('listlen', IntSort(), IntSort(), BoolSort())

def Iff(b1, b2):
   return And(Implies(b1, b2), Implies(b2, b1))

def IteBool(b, l, r):
    return And(Implies(b, l), Implies(Not(b), r))

def ulist(x):
    return Iff( list(x), IteBool(x == -1, True, list(next(x))))

def ulistlen(x, l):
    return Iff( listlen(x, l), IteBool( x == -1,
                                        l == 0,
                                        And(l > 0, listlen(next(x), l - 1))))

def pgm(x, l, ret):
    return IteBool(l <= 1, ret == -1, ret == next(x))

def vc(x, l, ret):
    return Implies( listlen(x, l),
                    Implies(pgm(x, l, ret), list(ret)))

# dereferenced terms in vc: { x }

# TODO: enforce small false model?

sol.add(next(-1) == -1)
sol.add(ulist(-1))
sol.add(ulistlen(-1, 0))

x, l, xl, ret = Ints('x l xl ret')

sol.add(listlen(x, l))
sol.add(pgm(x, l, ret))

# sol.add(ulist(ret))
sol.add(ulist(x))
sol.add(ulistlen(x, xl))

sol.add(Implies(l == xl, ulistlen(x, l) == ulistlen(x, xl)))

# sol.add(ulist(next(x)))
# sol.add(ulist(next(ret)))

sol.add(Not(vc(x, l, ret)))
sol.check()

m = sol.model()

unary = { next : ['x Loc', 'Loc'],
          list : ['x Loc', 'Bool']
        }
binary = { listlen : ['x Loc', 'y Loc', 'Bool'] }

fcts = { next : ['x Loc', 'Loc'],
         list : ['x Loc', 'Bool'],
         listlen : ['x Loc', 'y Loc', 'Bool']
       }

defaults = { next : -1, list : False, listlen : False }

# get header of function, i.e. (define-fun next ...
def getHeader(elt):
    header = '(define-fun ' + str(elt)
    header += ' ('
    length = len(fcts[elt])
    for i in range(0, length-1):
        header += '(' + fcts[elt][i] + ') '
    header += ') '
    header += fcts[elt][length-1]
    return header

# get body of unary function, ite expression
def getUnaryBody(elt):
    body = ''
    length = len(fcts[elt])
    for d in m.decls():
        if not(d in fcts.keys()):
            body += '  (ite '
            body += '(= ' + fcts[elt][0].split(' ')[0] + ' ' + str(m[d]) + ') '
            body += str(m.eval(elt(m[d]))).lower()
            body += '\n'
    return body

# get body of binary function, ite expression
def getBinaryBody(elt):
    body = ''
    length = len(fcts[elt])
    for d1 in m.decls():
        for d2 in m.decls():
            if not(d1 in fcts.keys()) and not(d2 in fcts.keys()):
                body += '  (ite (and '
                body += '(= ' + fcts[elt][0].split(' ')[0] + ' ' + str(m[d1]) + ') '
                body += '(= ' + fcts[elt][1].split(' ')[0] + ' ' + str(m[d2]) + ') '
                body += str(m.eval(elt(m[d1], m[d2]))).lower()
                body += '\n'
    return body

# print output in format CVC4 can handle
for elt in fcts.keys():
   print(getHeader(elt))
   if elt in unary.keys():
      print(getUnaryBody(elt), end = '')
   elif elt in binary.keys():
      print(getBinaryBody(elt), end = '')
   print('  ', end = '')
   for d in m.decls():
      if not(d in fcts.keys()):
         if elt in unary.keys():
            print(')', end = '')
         elif elt in binary.keys():
            for d in m.decls():
               if not(d in fcts.keys()):
                  print(')', end = '')
   print(' ' + str(defaults[elt]).lower())
   print(')')
   print()

