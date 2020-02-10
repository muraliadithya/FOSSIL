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

rank_list = Function('rank-list', IntSort(), IntSort())
rank_listlen = Function('rank-listlen', IntSort(), IntSort(), IntSort())

def ulist_rank(x):
    return IteBool( x == -1,
                    And(rank_list(x) == 0, list(x)),
                    IteBool( list(next(x)),
                             And(rank_list(x) == rank_list(next(x)) + 1, list(x)),
                             And(rank_list(x) == -1, Not(list(x)))))

def ulistlen_rank(x, l):
    return IteBool( x == -1,
                    And(rank_listlen(x,l) == 0, listlen(x,0)),
                    IteBool( listlen(next(x), l - 1),
                             And(rank_listlen(x, l) == rank_listlen(next(x), l-1) + 1, listlen(x,l)),
                             And(rank_listlen(x, l) == -1, Not(listlen(x,l)))))

sol.add(next(-1) == -1)
sol.add(ulist_rank(-1))
sol.add(ulistlen_rank(-1, 0))

# x = 1, l = 2, ret = 3
sol.add(ulistlen_rank(1, 2))
sol.add(pgm(1, 2, 3))
sol.add(ulist_rank(3))
sol.add(ulist_rank(next(3)))
sol.add(ulist_rank(1))
sol.add(ulist_rank(next(1)))
sol.add(ulistlen_rank(1, 2))

sol.add(Not(vc(1, 2, 3)))
sol.check()
print(sol.model())
