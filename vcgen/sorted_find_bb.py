from BBGenerator import BBGenerator
import argparse
import importlib
from interpreting import vc

# typedef
# /*D_tag node */
# struct node {
#   int key;
#   struct node * next;
# } SNnode;

# /*D_defs
# define pred sorted^(x): 
#   ( 
#   ((x l= nil) & emp) | 
#           ((x |-> loc next: nxt; int key: ky) * 
#       (sorted^(nxt) & (ky lt-set keys^(nxt)))
#       )  
#   ) ;
  
# define set-fun keys^(x):
#   (case (x l= nil): emptyset;
#    case ((x |-> loc next: nxt; int key: ky) * true): 
#     ((singleton ky) union keys^(nxt));
#    default: emptyset
#   ) ;
# */
# // -------------------------------------------------------

# _(dryad)
# int sorted_find(SNnode * l, int k)
#   /*D_requires sorted^(x) */
#   /*D_ensures ((sorted^(x) & (keys^(x) s= old(keys^(x)))) & ((ret i= 1) <=> (k i-in old(keys^(x))))) */
# {
# 	if (l == NULL) {
# 		return -1;
# 	} else if (l->key == k) {
# 		return 1;
# 	} else {
# 		int res = sorted_find(l->next, k);
# 		return res;
# 	}
# }

real_prog = """
(Const nil Loc)
(Var x Loc)
(Var k Int)
(Var ret Int)
(Var tmp Loc)

(Function next Loc Loc)
(Function key Loc Int)
(RecFunction Sorted Loc Bool)
(RecFunction Keys Loc SetInt)

(Var plus_infty Int)
(RecFunction Min Loc Int)
(RecDef (Min x) (ite (= x nil) plus_infty (ite (< (key x) (Min (next x))) (key x) (Min (next x)) ) ))


(RecDef (Sorted x) (ite (= x nil) True (and (Sorted (next x)) (not (IsMember x (Sp (Sorted (antiSp (next x)))))) (<= (key x) (Min (next x))) )))
(RecDef (Keys x) (ite (= x nil) EmptySetInt (SetAdd (Keys (next x)) (key x) ) ))

(Var oldkeysx SetInt)
(Var aux Loc)
(Var oldkeysaux SetInt)
(Var oldnxt Loc)

(lemma (x) (< (key x) plus_infty))
(lemma (x) (=> (Sorted x) (= (SPKeys x) (SPSorted x)) ))

(Program sorted_find (x k oldkeysx ret))
(Pre (Sorted x))
(Post (and
(Sorted x)
(= (Keys x) oldkeysx)
(=> (= ret (IntConst 1)) (IsMember k oldkeysx))
))

(assign oldkeysx (Keys x))
(If (= x nil)
Then
(assign ret (IntConst 0))
(return)
Else
    (If (= (key x) k)
    Then
    (assign ret (IntConst 1))
    (return)
    Else
    (assign aux (next x))
    (assign oldkeysaux (Keys aux))
    (call sorted_find (aux k oldkeysaux ret))
    (return)
    )
)
"""



bbgen_object = BBGenerator()
parsed_bbs = bbgen_object.parse_input(real_prog)
i = 0


print(f'{str(len(parsed_bbs))} Basic Blocks\n', '\n'.join(parsed_bbs[i]))


vc(parsed_bbs[i])