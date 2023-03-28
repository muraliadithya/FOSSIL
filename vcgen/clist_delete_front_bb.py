from BBGenerator import BBGenerator
import argparse
import importlib
from interpreting import vc
# /*D_defs 
#   define relation lseg^(head, tail): 
#   ( 
#   ((head l= tail) & emp) | 
#   ((head |-> loc next: nxt) * lseg^(nxt, tail))  
#   ) ;
# */
# // ---------------------------------------------------------

# _(dryad)
# CNode * circular_list_delete_front(CNode * x)
#   /*D_requires ((x |-> loc next: nxt) * lseg^(nxt, x)) */
#   /*D_ensures ((emp & ((x l= nxt) => (ret l= nil))) |
#        ((~(x l= nxt)) => ((x |-> loc next: ret) * lseg^(ret, x)))) */
# {
# 	CNode * next = x->next;

# 	if (next == x) {
# 		free(next);
# 		return NULL;
# 	} else {
# 		CNode * next_next = next->next;
# 		free(next);
# 		x->next = next_next;
# 		return next_next;
# 	}
# }




program = """
(Var x Loc)
(Var y Loc)

(Var head Loc)
(Var tail Loc)
(Var ret Loc)
(Var nxt Loc)
(Var new_nxt Loc)
(Var hd_nxt Loc)
(Function next Loc Loc)
(RecFunction Lseg Loc Loc Bool)
(RecDef (Lseg x y) (ite (= x y) True (and (Lseg (next x) y) (not (IsMember x (Sp (Lseg (antiSp (next x)) y)))))   )    )

(Program circular_list_delete_front (x nxt ret))
(Pre (and (= nxt (next x)) 
(Lseg nxt x)
(not (IsMember x (SPLseg nxt x)))
))
(Post (ite
  (= nxt x)
  (= ret nil)
  (and
    (= (next x) ret)
    (Lseg ret x)
    (not (IsMember x (Sp (Lseg ret x)))))
))
(If (= nxt x)
Then
(free nxt)
(assign ret nil)
(return)
Else
(assign new_nxt (next nxt))
(free nxt)
(assign (next x) new_nxt)
(assign ret new_nxt)
(return)
)
"""



bbgen_object = BBGenerator()
parsed_bbs = bbgen_object.parse_input(program)

i = 2

print(f'{str(len(parsed_bbs))} Basic Blocks\n', '\n'.join(parsed_bbs[i]))


vc(parsed_bbs[i])