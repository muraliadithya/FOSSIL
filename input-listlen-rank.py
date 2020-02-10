from z3_utils_hakank import *

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
                    IteBool(l == 0, And(rank_listlen(x,l) == 0, listlen(x,0)), Not(listlen(x, l))),
                    IteBool( listlen(next(x), l - 1),
                             And(rank_listlen(x, l) == rank_listlen(next(x), l-1) + 1, listlen(x,l)),
                             And(rank_listlen(x, l) == -1, Not(listlen(x,l)))))

sol.add(next(-1) == -1)
sol.add(Or(next(1) == 1, next(1) == 2, next(1) == -1))
sol.add(Or(next(2) == 1, next(2) == 2, next(2) == -1))

sol.check()
mod = sol.model()

# while loop to evaluate list

sol.add(ulist_rank(1))
sol.add(ulist_rank(2))
sol.add(ulist_rank(-1))

sol.add(ulistlen_rank(1,0))
sol.add(ulistlen_rank(1,1))
sol.add(ulistlen_rank(1,2))

sol.add(ulistlen_rank(2,0))
sol.add(ulistlen_rank(2,1))
sol.add(ulistlen_rank(2,2))

sol.add(ulistlen_rank(-1,0))
sol.add(ulistlen_rank(-1,1))
sol.add(ulistlen_rank(-1,2))

num_solutions = 0
while sol.check() == sat:
    num_solutions += 1
    mod = sol.model()
    print(mod)
    print()
    sol.add(Or(next(1) != mod.eval(next(1)), next(2) != mod.eval(next(2))))

print(num_solutions)
