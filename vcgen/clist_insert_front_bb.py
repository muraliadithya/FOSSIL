from BBGenerator import BBGenerator
import argparse
import importlib
from interpreting import vc
# // ---- Commmon definitions for circular list examples  ----
# #include <vcc.h>
# #include <stdlib.h>

# typedef
# /*D_tag node */
# struct node {
#   int key;
#   struct node * next;
# } CNode;

# /*D_defs 
#   define relation lseg^(head, tail): 
#   ( 
#   ((head l= tail) & emp) | 
#   ((head |-> loc next: nxt) * lseg^(nxt, tail))  
#   ) ;
# */
# // ---------------------------------------------------------

# _(dryad)
# CNode * circular_list_insert_front(CNode * x)
#   /*D_requires ((x |-> loc next: nxt) * lseg^(nxt, x)) */
#   /*D_ensures  ((x |-> loc next: ret) * lseg^(ret, x)) */
# {
# 	CNode * tmp = x->next;
# 	CNode * hd = (CNode *) malloc(sizeof(CNode)) ;
# 	_(assume hd != NULL)
# 	hd->next = tmp;
# 	x->next = hd; 
# 	return hd;
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
(Var tmp Loc)
(Function next Loc Loc)
(RecFunction Lseg Loc Loc Bool)
(RecDef (Lseg x y) (ite (= x y) True (and (Lseg (next x) y) (not (IsMember x (Sp (Lseg (antiSp (next x)) y)))))   )    )

(Program circular_list_insert_front (x nxt ret))
(Pre (and (= nxt (next x)) 
(Lseg nxt x)
(not (IsMember x (SPLseg nxt x)))
))
(Post (and (= ret (next x))
(Lseg ret x)
(not (IsMember x (SPLseg ret x)))
))

(alloc new_nxt)
(assume (not (= x nil)))
(assign tmp (next x))
(assign (next new_nxt) tmp)
(assign (next x) new_nxt)
(assign ret new_nxt)
(return)
"""



bbgen_object = BBGenerator()
parsed_bbs = bbgen_object.parse_input(program)

i = 0

print(f'{str(len(parsed_bbs))} Basic Blocks\n', '\n'.join(parsed_bbs[i]))


vc(parsed_bbs[i])